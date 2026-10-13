// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

/**
 * @file
 *
 * This file implements checked-exception capability argument checking (experimental, behind
 * '--experimental --enable-checked-exceptions').
 *
 * Per callable body the pass walks the typed AST with a stack of capability scopes (supplies)
 * and checks every demand against it:
 * - Supplies: the callable's own 'throws' clause; a 'try' block introduces one capability per
 *   exception type listed in its catch patterns ('e: E1 | E2' introduces two) covering the try
 *   block and the resource initializers of a try-with-resources expression, while 'catch' and
 *   'finally' blocks stay outside; a function literal's body is covered by the capability list
 * of the literal's own functional type (inferred from the expected type).
 *   'spawn' bodies start with an EMPTY stack (author ruling): enclosing capabilities are
 *   unreachable inside them. A 'handle' clause supplies a handler capability for each command
 *   type it lists, over the region its 'try' covers.
 * - Demands: 'throw e' and 'resume r throwing e' demand the static type of 'e'; 'perform c'
 *   demands the command's type; a call demands every entry of the resolved callee's (or called
 *   function value's) instantiated functional type, and a try-with-resources demands what each
 *   resource's implicit 'close()' requires. A value formed from an inferred declaration carries
 *   the list on its (completed) type, so the call through it pays. A default parameter value is
 *   checked against the callable's own scope; an instance field initializer must be satisfiable in
 *   EVERY constructor's scope; static field initializers, 'static init' blocks and top-level
 *   initializers have no capability scope.
 * - Resolution: a demand is satisfied iff some active supply S exists with demanded <: S,
 * searched from the innermost scope outwards, first match.
 *
 * The local Sema driver completes inferred contracts before use. This walker consumes completed
 * types and shares lexical resolution between residual collection and final read-only validation.
 */

#include "cangjie/Sema/CapabilityCheck.h"

#include <algorithm>
#include <functional>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "Diags.h"
#include "TypeCheckUtil.h"
#include "cangjie/AST/ASTCasting.h"
#include "cangjie/AST/Utils.h"
#include "cangjie/AST/Walker.h"
#include "cangjie/Basic/DiagnosticEngine.h"
#include "cangjie/Modules/ImportManager.h"
#include "cangjie/Sema/TypeManager.h"
#include "cangjie/Utils/CheckUtils.h"
#include "cangjie/Utils/ConstantsUtils.h"

using namespace Cangjie;
using namespace Cangjie::AST;

namespace {
/// One capability scope: the exception types whose capabilities the scope supplies, in textual
/// order (within one scope the first suitable entry wins).
using SupplyScope = std::vector<Ptr<Ty>>;
/// The nullary member named @p name among @p members, if any.
Ptr<FuncDecl> FindNullaryAmong(const std::vector<Ptr<Decl>>& members, const std::string& name)
{
    for (auto member : members) {
        auto fd = DynamicCast<FuncDecl*>(member);
        if (!fd || fd->identifier != name || !fd->funcBody || fd->funcBody->paramLists.empty()) {
            continue;
        }
        if (fd->funcBody->paramLists[0]->params.empty()) {
            return fd;
        }
    }
    return nullptr;
}

/// The nullary member named @p name of @p receiverTy or of any of its supertypes -- the shape
/// every protocol method the compiler calls implicitly has ('close', 'iterator', 'next'). An
/// extension's members count as the type's own: 'Array<T>' gets its 'iterator()' from one.
Ptr<FuncDecl> FindNullaryMemberOf(TypeManager& typeManager, Ptr<Ty> receiverTy, const std::string& name)
{
    if (!Ty::IsTyCorrect(receiverTy)) {
        return nullptr;
    }
    std::vector<Ptr<Ty>> chain{receiverTy};
    for (auto superTy : typeManager.GetAllSuperTys(*receiverTy)) {
        chain.emplace_back(superTy);
    }
    for (auto ty : chain) {
        if (auto decl = Ty::GetDeclOfTy<InheritableDecl>(ty)) {
            if (auto found = FindNullaryAmong(decl->GetMemberDeclPtrs(), name)) {
                return found;
            }
        }
        for (auto extend : typeManager.GetAllExtendsByTy(*ty)) {
            if (auto found = extend ? FindNullaryAmong(extend->GetMemberDeclPtrs(), name) : nullptr) {
                return found;
            }
        }
    }
    return nullptr;
}

class CapabilityChecker {
public:
    CapabilityChecker(TypeManager& typeManager, const ImportManager& importManager,
        Sema::CapabilityMissHandler& missHandler, const Sema::EffectiveCapabilityType& effective,
        const Sema::EnsureCapabilityContract& ensure = {}, Ptr<DiagnosticEngine> diag = nullptr)
        : typeManager(typeManager),
          importManager(importManager),
          missHandler(missHandler),
          effective(effective),
          ensure(ensure),
          diag(diag)
    {
    }

    /**
     * Check one callable in collect mode: the declaration's own inferred list is
     * not consulted as a supply, so every requirement its body does not discharge locally
     * reaches the miss handler. Explicit clause entries still supply.
     */
    void CollectResidualDemands(Decl& decl, Ptr<const Decl> ownerDecl)
    {
        collectingFor = ownerDecl;
        CheckDecl(decl);
        CollectFieldInitializerDemands(decl);
        collectingFor = nullptr;
    }

    /**
     * An instance field initializer "contributes to every inference-eligible constructor that
     * evaluates it" (What is inferred, point 3): it has no capability scope of its own, so its
     * requirements are the constructor's, and a clause-free constructor must infer them rather
     * than report them at the initializer. Walked inside the constructor's own scope, so a
     * constructor that declares a clause discharges what its fields need.
     */
    void CollectFieldInitializerDemands(Decl& decl)
    {
        auto ctor = DynamicCast<FuncDecl*>(&decl);
        if (!ctor || !ctor->TestAttr(Attribute::CONSTRUCTOR) || ctor->TestAttr(Attribute::STATIC) || !ctor->funcBody ||
            !ctor->outerDecl) {
            return;
        }
        auto owner = ctor->outerDecl;
        if (owner->astKind != ASTKind::CLASS_DECL && owner->astKind != ASTKind::STRUCT_DECL) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        supplies.emplace_back(TypeCheckUtil::GetFuncBodyCapTys(*ctor->funcBody));
        supplyOwners.emplace_back(ctor);
        auto captures = OwnerCaptures(*ctor);
        PushCaptures(captures, ctor);
        for (auto& member : owner->GetMemberDecls()) {
            auto field = DynamicCast<VarDecl*>(member.get());
            if (field && !field->TestAttr(Attribute::STATIC) && field->initializer) {
                WalkScoped(field->initializer.get());
            }
        }
        PopCaptures(captures);
        supplies.pop_back();
        supplyOwners.pop_back();
    }

    void CheckDecl(Decl& decl)
    {
        switch (decl.astKind) {
            case ASTKind::FUNC_DECL:
                CheckCallable(StaticCast<FuncDecl&>(decl));
                break;
            case ASTKind::PROP_DECL: {
                auto& pd = StaticCast<PropDecl&>(decl);
                for (auto& getter : pd.getters) {
                    if (getter) {
                        CheckCallable(*getter);
                    }
                }
                for (auto& setter : pd.setters) {
                    if (setter) {
                        CheckCallable(*setter);
                    }
                }
                break;
            }
            default:
                break;
        }
    }

    void CheckPackage(Package& pkg)
    {
        for (auto& file : pkg.files) {
            CJC_NULLPTR_CHECK(file);
            for (auto& decl : file->decls) {
                CJC_NULLPTR_CHECK(decl);
                CheckTopLevelDecl(*decl);
            }
        }
    }

private:
    void CheckTopLevelDecl(Decl& decl)
    {
        switch (decl.astKind) {
            case ASTKind::FUNC_DECL:
                CheckCallable(StaticCast<FuncDecl&>(decl));
                break;
            case ASTKind::MAIN_DECL: {
                // 'main' is desugared into a function declaration before type check; its body
                // (and 'throws' clause, covering the default exception handler) moved with it.
                auto& md = StaticCast<MainDecl&>(decl);
                if (md.desugarDecl) {
                    CheckCallable(*md.desugarDecl);
                }
                break;
            }
            case ASTKind::MACRO_DECL: {
                auto& md = StaticCast<MacroDecl&>(decl);
                if (md.desugarDecl) {
                    CheckCallable(*md.desugarDecl);
                }
                break;
            }
            case ASTKind::CLASS_DECL:
            case ASTKind::STRUCT_DECL:
            case ASTKind::INTERFACE_DECL:
            case ASTKind::ENUM_DECL:
            case ASTKind::EXTEND_DECL:
                CheckMembers(decl);
                break;
            case ASTKind::VAR_DECL:
            case ASTKind::VAR_WITH_PATTERN_DECL:
                // Top-level variable initializers cannot throw checked exceptions: no capability
                // scope encloses them.
                CheckInitializer(StaticCast<VarDeclAbstract&>(decl), nullptr);
                break;
            default:
                break;
        }
    }

    void CheckMembers(Decl& decl)
    {
        // An instance field initializer has no scope of its own: its demands must be satisfiable
        // in the capability scope of EVERY constructor. With no explicit
        // constructor the implicit one supplies nothing.
        std::vector<Sema::CapabilityScope> constructorScopes;
        for (auto& member : decl.GetMemberDecls()) {
            auto fd = DynamicCast<FuncDecl*>(member.get());
            if (fd && fd->TestAttr(Attribute::CONSTRUCTOR) && !fd->TestAttr(Attribute::STATIC) && fd->funcBody) {
                // A constructor's effective list, not merely its written one: inference gave a
                // clause-free constructor the very requirements its field initializers raise
                // (they are collected into it), so reading the clause alone would report at the
                // initializer what the constructor already carries.
                auto ft = DynamicCast<FuncTy*>(fd->GetTy());
                auto caps = ft ? ft->capTys : SupplyScope{};

                constructorScopes.push_back({std::move(caps), fd});
            }
        }
        if (constructorScopes.empty()) {
            constructorScopes.push_back({{}, &decl});
        }
        bool hasInstanceFields = decl.astKind == ASTKind::CLASS_DECL || decl.astKind == ASTKind::STRUCT_DECL;
        for (auto& member : decl.GetMemberDecls()) {
            CJC_NULLPTR_CHECK(member);
            switch (member->astKind) {
                case ASTKind::FUNC_DECL:
                    CheckCallable(StaticCast<FuncDecl&>(*member));
                    break;
                case ASTKind::PROP_DECL: {
                    auto& pd = StaticCast<PropDecl&>(*member);
                    for (auto& getter : pd.getters) {
                        if (getter) {
                            CheckCallable(*getter);
                        }
                    }
                    for (auto& setter : pd.setters) {
                        if (setter) {
                            CheckCallable(*setter);
                        }
                    }
                    break;
                }
                case ASTKind::VAR_DECL: {
                    // Static field initializers have no capability scope, like top-level ones.
                    auto& vd = StaticCast<VarDecl&>(*member);
                    bool isInstanceField = hasInstanceFields && !vd.TestAttr(Attribute::STATIC);
                    if (isInstanceField) {
                        for (const auto& scope : constructorScopes) {
                            CheckInitializer(vd, &scope);
                        }
                    } else {
                        CheckInitializer(vd, nullptr);
                    }
                    break;
                }
                default:
                    // PRIMARY_CTOR_DECL is desugared into an 'init' member during type check.
                    break;
            }
        }
    }

    /// The escape hatch: 'std.core.unsafeCanThrow<E, R>' is a compiler intrinsic with a
    /// library-visible signature. Inside it -- and nowhere else -- a capability for its own 'E' is
    /// fabricated, which is what lets it invoke a callback that requires one. No source operation
    /// fabricates capabilities; this is the one declaration that gets one for free.
    static bool IsEscapeHatch(const FuncDecl& fd)
    {
        return (fd.identifier == UNSAFE_CAN_THROW && fd.fullPackageName == CORE_PACKAGE_NAME) ||
            (fd.identifier == "unsafeCanPerform" && fd.fullPackageName == EFFECT_PACKAGE_NAME);
    }

    SupplyScope FabricatedCapabilities(const FuncDecl& fd) const
    {
        SupplyScope caps;
        if (!IsEscapeHatch(fd) || !fd.funcBody || !fd.funcBody->generic) {
            return caps;
        }
        // Only the FIRST parameter is the fabricated capability's type: the signature is
        // 'unsafeCanThrow<E, R>', and 'R' is the callback's result. Fabricating for every
        // parameter happened to be harmless with this shape and stops being so the moment the
        // effect twin lands (review finding I43).
        auto& params = fd.funcBody->generic->typeParameters;
        if (!params.empty() && params.front() && Ty::IsTyCorrect(params.front()->GetTy())) {
            (void)caps.emplace_back(params.front()->GetTy());
        }
        return caps;
    }

    void PushLexicalContext(FuncDecl& fd)
    {
        if (!IsNestedFunc(fd) || !fd.curFile) {
            return;
        }
        // Declaration-site ancestry is authoritative; FuncBody::outerFunc is not
        // populated by Sema and caller scopes must never enter this context.
        Ptr<Node> root = fd.curFile;
        for (auto outer = fd.outerDecl; outer && outer->IsFunc(); outer = outer->outerDecl) {
            root = outer;
        }
        std::vector<Ptr<Node>> path;
        std::vector<Ptr<Node>> ancestors;
        Walker(
            root,
            [&](Ptr<Node> node) {
                if (node == &fd) {
                    ancestors = path;
                    return VisitAction::STOP_NOW;
                }
                path.emplace_back(node);
                return VisitAction::WALK_CHILDREN;
            },
            [&](Ptr<Node>) {
                path.pop_back();
                return VisitAction::KEEP_DECISION;
            })
            .Walk();
        for (size_t i = 0; i < ancestors.size(); ++i) {
            auto node = ancestors[i];
            SupplyScope caps;
            if (auto body = DynamicCast<FuncBody*>(node)) {
                // Pending outer inference is deliberately unavailable to nested ellipsis.
                caps = TypeCheckUtil::GetFuncBodyCapTys(*body);
                if (body->funcDecl && !body->funcDecl->TestAttr(Attribute::STATIC) && !body->funcDecl->IsFinalizer()) {
                    PushCaptures(OwnerCaptures(*body->funcDecl), body->funcDecl);
                }
            } else if (auto literal = DynamicCast<LambdaExpr*>(node)) {
                caps = GetLiteralCapTys(*literal);
            } else if (auto te = DynamicCast<TryExpr*>(node); te && i + 1 < ancestors.size()) {
                auto child = ancestors[i + 1];
                bool protectedBody = child == te->tryBlock.get() || child == te->tryLambda.get();
                for (auto& resource : te->resourceSpec) {
                    protectedBody = protectedBody || child == resource.get();
                }
                if (protectedBody) {
                    caps = CollectCatchCapTys(*te);
                    auto handlers = CollectHandlerCapTys(*te);
                    caps.insert(caps.end(), handlers.begin(), handlers.end());
                }
            } else if (node->astKind == ASTKind::SPAWN_EXPR) {
                supplies.clear();
                supplyOwners.clear();
            }
            if (!caps.empty()) {
                supplies.emplace_back(std::move(caps));
                supplyOwners.emplace_back(node);
            }
        }
    }

    void CheckCallable(FuncDecl& fd)
    {
        if (!fd.funcBody) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        PushLexicalContext(fd);
        auto fabricated = FabricatedCapabilities(fd);
        bool hasFabricated = !fabricated.empty();
        if (hasFabricated) {
            supplies.emplace_back(std::move(fabricated));
            supplyOwners.emplace_back(&fd);
        }
        // The enclosing class's captured capabilities are in scope throughout a member that has
        // a receiver to carry them. A static member, a static initializer and a
        // finalizer have none, and a checked throw is forbidden there. Derived
        // from the declaration's owner rather than from checker state, so inference — which
        // checks declarations one by one — sees the same supplies as the reporting pass.
        bool hasReceiver = !fd.TestAttr(Attribute::STATIC) && !fd.IsFinalizer();
        auto captures = hasReceiver ? OwnerCaptures(fd) : SupplyScope{};
        PushCaptures(captures, &fd);
        // The FUNC_BODY visit then pushes the declaration's own clause scope. The walker visits
        // parameter default values before the body, matching "as if it appeared at the
        // beginning of the body".
        WalkScoped(fd.funcBody.get());
        PopCaptures(captures);
        if (hasFabricated) {
            supplies.pop_back();
            supplyOwners.pop_back();
        }
        supplies.clear();
        supplyOwners.clear();
    }

    void CheckInitializer(VarDeclAbstract& vd, const Sema::CapabilityScope* constructor)
    {
        if (!vd.initializer) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        if (constructor) {
            supplies.push_back(constructor->types);
            supplyOwners.push_back(constructor->owner);
        }
        auto captures = constructor ? OwnerCaptures(vd) : SupplyScope{};
        PushCaptures(captures, &vd);
        WalkScoped(vd.initializer.get());
        PopCaptures(captures);
        if (constructor) {
            supplies.pop_back();
            supplyOwners.pop_back();
        }
        CJC_ASSERT(supplies.empty());
    }

    /// The 'captures' list of the declaration's own class or struct — never an inherited one
    ///.
    SupplyScope OwnerCaptures(const Decl& decl) const
    {
        auto owner = decl.outerDecl;
        if (auto extension = DynamicCast<ExtendDecl*>(owner); extension && extension->extendedType) {
            auto receiver = extension->extendedType->GetTy();
            auto nominal = Ty::GetDeclOfTy<InheritableDecl>(receiver);
            if (!nominal) {
                return {};
            }
            auto caps = TypeCheckUtil::GetDeclCapturesCapTys(*nominal);
            auto mapping = TypeCheckUtil::GenerateTypeMappingByTy(nominal->GetTy(), receiver);
            for (auto& cap : caps) {
                cap = typeManager.GetInstantiatedTy(cap, mapping);
            }
            return typeManager.NormalizeCapTys(caps);
        }
        return owner ? TypeCheckUtil::GetDeclCapturesCapTys(*owner) : SupplyScope{};
    }

    void PushCaptures(const SupplyScope& captures, Ptr<const Node> captureOwner = nullptr)
    {
        if (!captures.empty()) {
            supplies.emplace_back(captures);
            supplyOwners.emplace_back(captureOwner);
        }
    }

    void PopCaptures(const SupplyScope& captures)
    {
        if (!captures.empty()) {
            supplies.pop_back();
            supplyOwners.pop_back();
        }
    }

    void WalkScoped(Ptr<Node> root)
    {
        if (!root) {
            return;
        }
        Walker(
            root, [this](Ptr<Node> node) { return VisitPre(node); }, [this](Ptr<Node> node) { return VisitPost(node); })
            .Walk();
    }

    void DemandProperty(Expr& reference, bool getter, const Node& site)
    {
        if (reference.desugarExpr || reference.TestAttr(Attribute::UNREACHABLE)) {
            return;
        }
        auto property = DynamicCast<PropDecl*>(reference.GetTarget());
        if (!property) {
            return;
        }
        auto accessor = DynamicCast<FuncDecl*>(TypeCheckUtil::GetUsedMemberDecl(*property, getter));
        if (!accessor) {
            return;
        }
        Ptr<Ty> receiver = nullptr;
        if (auto member = DynamicCast<MemberAccess*>(&reference); member && member->baseExpr) {
            receiver = member->baseExpr->GetTy();
        }
        if (ensure && !ensure(*accessor, site)) {
            return;
        }
        for (auto cap : ProtocolMemberCaps(*accessor, receiver)) {
            Demand(cap, site, getter ? "this property read" : "this property write");
        }
    }

    VisitAction VisitPre(Ptr<Node> node)
    {
        CJC_NULLPTR_CHECK(node);
        switch (node->astKind) {
            case ASTKind::FUNC_BODY: {
                // Named callables: the body of a callable with a 'throws' list is a capability
                // scope.
                auto& fb = StaticCast<FuncBody&>(*node);
                auto ft = DynamicCast<FuncTy*>(fb.GetTy());
                auto caps =
                    fb.funcDecl.get() == collectingFor.get() || !ft ? TypeCheckUtil::GetFuncBodyCapTys(fb) : ft->capTys;
                supplies.emplace_back(std::move(caps));
                supplyOwners.emplace_back(fb.funcDecl ? Ptr<const Node>(fb.funcDecl) : Ptr<const Node>(node));
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::FUNC_DECL: {
                auto& fd = StaticCast<FuncDecl&>(*node);
                if (!IsNestedFunc(fd) || !fd.funcBody) {
                    return VisitAction::WALK_CHILDREN;
                }
                // Nested declarations retain lexical supplies; their own completed parameters
                // discharge requirements before residuals reach the enclosing inference owner.
                CheckLocalFunc(fd);
                return VisitAction::SKIP_CHILDREN;
            }
            case ASTKind::LAMBDA_EXPR:
                // A literal's capability list comes from the expected type only and is stored
                // on the literal's functional type.
                supplies.emplace_back(GetLiteralCapTys(StaticCast<LambdaExpr&>(*node)));
                supplyOwners.emplace_back(node);
                return VisitAction::WALK_CHILDREN;
            case ASTKind::FUNC_PARAM: {
                // A default parameter value is checked against the callable's own capability
                // scope (already on the stack). Skip the synthesized default-value function
                // (desugarDecl): it clones the same expression into a clause-less body.
                auto& fp = StaticCast<FuncParam&>(*node);
                WalkScoped(fp.assignment.get());
                return VisitAction::SKIP_CHILDREN;
            }
            case ASTKind::TRY_EXPR:
                HandleTry(StaticCast<TryExpr&>(*node));
                return VisitAction::SKIP_CHILDREN;
            case ASTKind::SPAWN_EXPR:
                HandleSpawn(StaticCast<SpawnExpr&>(*node));
                return VisitAction::SKIP_CHILDREN;
            case ASTKind::RESUME_EXPR: {
                // Effects: 'resume r throwing e' injects 'e' at the suspended 'perform' site, so
                // it is a requirement site classified by the static type of 'e', exactly as
                // 'throw e' is -- but resolved where the injected exception SURFACES: inside the
                // try's body, so the try's own catch clauses discharge it, and the scopes
                // enclosing the 'try-handle' follow.
                auto& re = StaticCast<ResumeExpr&>(*node);
                if (re.throwingExpr && Ty::IsTyCorrect(re.throwingExpr->GetTy())) {
                    DemandInjected(re.throwingExpr->GetTy(), re, "this 'resume ... throwing' expression");
                }
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::THROW_EXPR: {
                auto& te = StaticCast<ThrowExpr&>(*node);
                if (te.expr && Ty::IsTyCorrect(te.expr->GetTy())) {
                    Demand(te.expr->GetTy(), te, "this 'throw' expression");
                }
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::PERFORM_EXPR: {
                // Effects: 'perform c' requires a handler capability for the
                // command's own type, exactly as 'throw e' requires one for the exception's.
                auto& pe = StaticCast<PerformExpr&>(*node);
                if (pe.expr && Ty::IsTyCorrect(pe.expr->GetTy())) {
                    Demand(pe.expr->GetTy(), pe, "this 'perform' expression");
                }
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::FOR_IN_EXPR: {
                DemandForInProtocol(StaticCast<ForInExpr&>(*node));
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::CALL_EXPR: {
                auto& ce = StaticCast<CallExpr&>(*node);
                HandleCall(ce);
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::ASSIGN_EXPR: {
                auto& assignment = StaticCast<AssignExpr&>(*node);
                if (!assignment.desugarExpr && assignment.leftValue) {
                    DemandProperty(*assignment.leftValue, false, assignment);
                    if (assignment.isCompound || assignment.TestAttr(Attribute::SIDE_EFFECT)) {
                        DemandProperty(*assignment.leftValue, true, assignment);
                    }
                }
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::INC_OR_DEC_EXPR: {
                auto& increment = StaticCast<IncOrDecExpr&>(*node);
                if (!increment.desugarExpr && increment.expr) {
                    DemandProperty(*increment.expr, false, increment);
                    DemandProperty(*increment.expr, true, increment);
                }
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::MEMBER_ACCESS: {
                // A function-typed field or property of an assumed package, or one of its methods
                // taken as a value. An INFERRED declaration needs nothing here: its list is on the
                // reference's own type by then, so the eventual call pays it, which is what the
                // text asks for.
                auto& ma = StaticCast<MemberAccess&>(*node);
                if (!ma.TestAttr(Attribute::LEFT_VALUE)) {
                    DemandProperty(ma, true, ma);
                }
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::REF_EXPR: {
                // The same for an unqualified reference.
                auto& re = StaticCast<RefExpr&>(*node);
                if (!re.TestAttr(Attribute::LEFT_VALUE)) {
                    DemandProperty(re, true, re);
                }
                return VisitAction::WALK_CHILDREN;
            }
            default:
                return VisitAction::WALK_CHILDREN;
        }
    }

    VisitAction VisitPost(Ptr<Node> node)
    {
        // Balanced with VisitPre: these two kinds always push exactly one scope there.
        if (node->astKind == ASTKind::FUNC_BODY || node->astKind == ASTKind::LAMBDA_EXPR) {
            supplies.pop_back();
            supplyOwners.pop_back();
        }
        return VisitAction::KEEP_DECISION;
    }

    SupplyScope GetLiteralCapTys(const LambdaExpr& le) const
    {
        auto funcTy = DynamicCast<FuncTy*>(le.GetTy());
        return funcTy ? funcTy->capTys : SupplyScope{};
    }

    /**
     * Checked exceptions ("Capability scopes" rule 1): try-with-resources closes its resources
     * implicitly, and that closing is inside the try's own scope -- the desugaring puts it in a
     * 'finally' INNER to the user's catch clauses, so the same clauses catch it (probed
     * 2026-08-30). The capability pass runs before desugar, so the implicit calls do not exist as
     * AST nodes yet and nothing would be demanded for them at all. The requirement is synthesized
     * here instead, against the try's scope, exactly as an explicit 'r.close()' in the body would
     * be. Inert while 'Resource.close()' is clause-free, which is why it must land BEFORE the
     * standard library gives it one.
     */
    Ptr<FuncDecl> FindNullaryMember(Ptr<Ty> receiverTy, const std::string& name) const
    {
        return FindNullaryMemberOf(typeManager, receiverTy, name);
    }

    /// The effective capability list of a nullary protocol member on @p receiverTy: what it
    /// declares, instantiated through the receiver, plus what inference gave it in this package.
    std::vector<Ptr<Ty>> ProtocolMemberCaps(const FuncDecl& member, Ptr<Ty> receiverTy)
    {
        if (ensure && !ensure(const_cast<FuncDecl&>(member), member)) {
            return {};
        }
        auto ty = effective ? effective(member, member.GetTy(), false) : member.GetTy();
        auto ft = DynamicCast<FuncTy*>(ty);
        if (!ft) {
            return {};
        }
        MultiTypeSubst mapping;
        if (Ty::IsTyCorrect(receiverTy)) {
            typeManager.GenerateGenericMapping(mapping, *receiverTy);
        }
        TypeSubst subst;
        for (auto& [var, candidates] : mapping) {
            if (candidates.size() == 1) {
                subst.emplace(var, *candidates.begin());
            }
        }
        auto caps = ft->capTys;
        for (auto& cap : caps) {
            cap = typeManager.GetInstantiatedTy(cap, subst);
        }
        return typeManager.NormalizeCapTys(caps);
    }

    /**
     * "Implicit invocations include ... the iterator protocol of 'for-in'" (What is inferred,
     * point 2). The pass runs before desugar, so the calls to 'iterator()' and 'next()' do not
     * exist as nodes yet and would demand nothing at all; they are synthesized here, in the loop's
     * own scope, exactly as the implicit 'close()' of try-with-resources is. Range and string
     * loops iterate built-ins and have nothing to demand.
     */
    void DemandForInProtocol(const ForInExpr& fe)
    {
        if (!fe.inExpression) {
            return;
        }
        // 'forInKind' is not decided yet at this stage -- CHIR classifies the loop -- so the
        // subject's own members decide instead: a range or a string reaches the built-in
        // iteration whose protocol members declare nothing, and demands nothing here either.
        auto subjectTy = fe.inExpression->GetTy();
        if (!Ty::IsTyCorrect(subjectTy)) {
            return;
        }
        // 'for (x in xs)' calls 'xs.iterator()' once, then 'next()' on the result until it ends.
        // Iterating an iterator directly skips the first step.
        auto iteratorTy = subjectTy;
        if (auto iterFd = FindNullaryMember(subjectTy, "iterator")) {
            for (auto cap : ProtocolMemberCaps(*iterFd, subjectTy)) {
                Demand(cap, fe, "the 'iterator()' of this 'for-in'");
            }
            if (auto funcTy = DynamicCast<FuncTy*>(iterFd->GetTy()); funcTy && Ty::IsTyCorrect(funcTy->retTy)) {
                auto mapping = TypeCheckUtil::GenerateTypeMappingByTy(
                    iterFd->outerDecl ? iterFd->outerDecl->GetTy() : nullptr, subjectTy);
                auto instantiated =
                    mapping.empty() ? funcTy->retTy : typeManager.GetInstantiatedTy(funcTy->retTy, mapping);
                iteratorTy = Ty::IsTyCorrect(instantiated) ? instantiated : funcTy->retTy;
                // The core Iterator.iterator implementation returns its receiver.
                // Preserve that receiver's selected next() contract when iterating it directly.
                if (iterFd->fullPackageName == CORE_PACKAGE_NAME && iterFd->outerDecl &&
                    iterFd->outerDecl->identifier == "Iterator") {
                    iteratorTy = subjectTy;
                }
            }
        }
        if (auto nextFd = FindNullaryMember(iteratorTy, "next")) {
            for (auto cap : ProtocolMemberCaps(*nextFd, iteratorTy)) {
                Demand(cap, fe, "the 'next()' of this 'for-in'");
            }
        }
    }

    void DemandResourceClose(const VarDecl& resource)
    {
        auto resourceTy = resource.GetTy();
        auto closeFd = FindNullaryMember(resourceTy, "close");
        if (!closeFd) {
            return;
        }
        // The declared list, instantiated through the resource's own type (a generic resource
        // closes at its instantiation), plus the list inference gave 'close' in this package.
        auto caps = ProtocolMemberCaps(*closeFd, resourceTy);

        for (auto cap : typeManager.NormalizeCapTys(caps)) {
            if (Ty::IsTyCorrect(cap)) {
                Demand(cap, resource, "the implicit 'close()' of this resource");
            }
        }
    }

    void HandleTry(TryExpr& te)
    {
        // A 'handle' clause supplies a handler capability for each command type it lists
        //, over the same region a 'catch' covers. 'te.tryLambda' and
        // 'te.finallyLambda' are the desugared forms of the blocks walked below, so they are
        // deliberately not walked again.
        auto caps = CollectCatchCapTys(te);
        for (auto handlerCap : CollectHandlerCapTys(te)) {
            caps.emplace_back(handlerCap);
        }
        supplies.emplace_back(std::move(caps));
        supplyOwners.emplace_back(&te);
        for (auto& resource : te.resourceSpec) {
            // Resource initializers of try-with-resources are inside the try's scope: their
            // exceptions are caught by the same clauses. So is the implicit closing.
            WalkScoped(resource.get());
            if (resource) {
                DemandResourceClose(*resource);
            }
        }
        // With 'handle' clauses present the parser rebuilds the try block as a lambda, and THAT
        // copy is the one sema types; the original block keeps untyped nodes, so walking it would
        // silently raise no demands at all. Walk whichever copy carries the types.
        if (te.tryLambda) {
            WalkScoped(te.tryLambda.get());
        } else {
            WalkScoped(te.tryBlock.get());
        }
        supplies.pop_back();
        supplyOwners.pop_back();
        // A 'catch' block is not inside its try's capability scope: rethrowing a caught checked
        // exception requires a capability from the enclosing scopes. Same for 'finally' and for
        // a 'handle' body, which runs where the handler was installed.
        for (auto& catchBlock : te.catchBlocks) {
            WalkScoped(catchBlock.get());
        }
        // A handler body runs where the handler was installed -- outside the try's scope for an
        // ordinary 'throw' -- but a 'resume ... throwing' inside it injects at the suspended
        // 'perform', which is inside the try's body. The try's catch capabilities are therefore
        // offered to resume sites alone.
        resumeSupplies.push_back({CollectCatchCapTys(te), &te});
        for (auto& handler : te.handlers) {
            if (handler.desugaredLambda) {
                WalkScoped(handler.desugaredLambda.get());
            } else {
                WalkScoped(handler.block.get());
            }
        }
        resumeSupplies.pop_back();
        WalkScoped(te.finallyBlock.get());
    }

    SupplyScope CollectCatchCapTys(const TryExpr& te) const
    {
        // One capability per exception type listed in the catch patterns, in textual order;
        // a pattern 'e: E1 | E2' introduces two. Mirrors ChkTryExprCatchPatterns' collection.
        SupplyScope caps;
        for (auto& pattern : te.catchPatterns) {
            if (!pattern) {
                continue;
            }
            if (pattern->astKind == ASTKind::WILDCARD_PATTERN) {
                auto exception = importManager.GetCoreDecl<ClassDecl>(CLASS_EXCEPTION);
                if (exception && Ty::IsTyCorrect(exception->GetTy())) {
                    caps.emplace_back(exception->GetTy());
                }
            } else if (auto etp = DynamicCast<ExceptTypePattern*>(pattern.get())) {
                for (auto& type : etp->types) {
                    if (type && Ty::IsTyCorrect(type->GetTy())) {
                        caps.emplace_back(type->GetTy());
                    }
                }
            }
        }
        return caps;
    }

    /// The command types listed by the 'handle' clauses of @p te. A pattern
    /// 'c: C1 | C2' introduces two, mirroring how a catch pattern introduces one per exception.
    SupplyScope CollectHandlerCapTys(const TryExpr& te) const
    {
        SupplyScope caps;
        for (auto& handler : te.handlers) {
            auto ctp = DynamicCast<CommandTypePattern*>(handler.commandPattern.get());
            if (ctp == nullptr) {
                continue;
            }
            for (auto& type : ctp->types) {
                if (type && Ty::IsTyCorrect(type->GetTy())) {
                    caps.emplace_back(type->GetTy());
                }
            }
        }
        return caps;
    }

    void CheckLocalFunc(FuncDecl& fd)
    {
        WalkScoped(fd.funcBody.get());
    }

    void HandleSpawn(SpawnExpr& se)
    {
        // The thread context argument is evaluated at the spawn site, in the current scopes.
        WalkScoped(se.arg.get());
        // A 'spawn' body starts with an EMPTY capability scope stack (author ruling): the
        // enclosing capabilities (including any every-constructor root) are unreachable.
        std::vector<SupplyScope> savedSupplies;
        savedSupplies.swap(supplies);
        auto savedOwners = std::move(supplyOwners);
        supplyOwners.clear();
        WalkScoped(se.task.get());
        supplies = std::move(savedSupplies);
        supplyOwners = std::move(savedOwners);
    }

    /// The escape hatch is a no-op when its type argument is unchecked: an unchecked exception
    /// never required a capability, so nothing is being assumed away. Worth saying, since the call
    /// reads as if it were.
    void WarnUselessEscapeHatch(const CallExpr& ce) const
    {
        if (!ce.resolvedFunction || !IsEscapeHatch(*ce.resolvedFunction)) {
            return;
        }
        auto ref = DynamicCast<RefExpr*>(ce.baseFunc.get());
        if (!ref || ref->typeArguments.empty()) {
            return;
        }
        auto assumedTy = ref->typeArguments.front()->GetTy();
        if (diag && Ty::IsTyCorrect(assumedTy) &&
            TypeCheckUtil::IsUncheckedExceptionTy(typeManager, importManager, assumedTy)) {
            diag->DiagnoseRefactor(DiagKindRefactor::sema_chexc_useless_escape_hatch, ce, Ty::ToString(assumedTy));
        }
    }

    void HandleCall(CallExpr& ce)
    {
        // Both resolved-function calls and function-value calls: the callee expression's type
        // is the callee's functional type with generic instantiation applied.
        if (!ce.baseFunc) {
            return;
        }
        WarnUselessEscapeHatch(ce);
        auto funcTy = DynamicCast<FuncTy*>(ce.baseFunc->GetTy());
        if (!funcTy) {
            return;
        }
        std::vector<Ptr<Ty>> demands = funcTy->capTys;
        // The semantic form is what a scope offers AND what a callee requires: an entry covered by
        // a more general entry of the same list is not part of the list, so it is not demanded --
        // 'throws Base, Derived' is the list {Base}, and a missing handler reports Base alone.
        for (auto cap : typeManager.NormalizeCapTys(demands)) {
            if (Ty::IsTyCorrect(cap)) {
                Demand(cap, ce, DescribeCallee(ce));
            }
        }
        DemandConstructedCaptures(ce);
    }

    /// Substitution from the callee's own type parameters to this call site's type arguments:
    /// the receiver's instantiation (for a member of a generic type) combined with the call's
    /// explicit or inferred type arguments (for a generic function).
    TypeSubst CalleeTypeMapping(const CallExpr& ce) const
    {
        TypeSubst mapping;
        if (!ce.resolvedFunction) {
            return mapping;
        }
        if (auto ma = DynamicCast<MemberAccess*>(ce.baseFunc.get());
            ma && ma->baseExpr && ce.resolvedFunction->outerDecl && Ty::IsTyCorrect(ma->baseExpr->GetTy())) {
            mapping =
                TypeCheckUtil::GenerateTypeMappingByTy(ce.resolvedFunction->outerDecl->GetTy(), ma->baseExpr->GetTy());
        }
        if (auto nre = DynamicCast<NameReferenceExpr*>(ce.baseFunc.get()); nre && !nre->instTys.empty()) {
            auto funcMapping = TypeCheckUtil::GenerateTypeMapping(*ce.resolvedFunction, nre->instTys);
            mapping.insert(funcMapping.begin(), funcMapping.end());
        }
        return mapping;
    }

    void DemandConstructedCaptures(CallExpr& ce)
    {
        // Constructing an instance of a capturing class or struct requires its captured
        // capabilities at the construction site. This covers 'C(...)',
        // delegating 'this(...)' calls, and 'super(...)' calls, which resolve to the
        // superclass constructor and therefore demand the superclass's captures (rule 5).
        auto ctor = ce.resolvedFunction;
        if (!ctor || !ctor->TestAttr(Attribute::CONSTRUCTOR) || !ctor->outerDecl) {
            return;
        }
        auto captures = TypeCheckUtil::GetDeclCapturesCapTys(*ctor->outerDecl);
        if (captures.empty()) {
            return;
        }
        // A generic capturing class captures at the instantiated types: 'C<Int64>()' of
        // 'class C<T> captures GenericException<T>' requires 'GenericException<Int64>'.
        auto declaredTy = ctor->outerDecl->GetTy();
        auto instantiated = Ty::IsTyCorrect(ce.GetTy()) ? ce.GetTy() : declaredTy;
        auto typeMapping = TypeCheckUtil::GenerateTypeMappingByTy(declaredTy, instantiated);
        for (auto cap : captures) {
            auto demanded = typeMapping.empty() ? cap : typeManager.GetInstantiatedTy(cap, typeMapping);
            if (Ty::IsTyCorrect(demanded)) {
                Demand(demanded, ce, DescribeCallee(ce));
            }
        }
    }

    std::string DescribeCallee(const CallExpr& ce) const
    {
        if (ce.resolvedFunction) {
            return "the call to '" + ce.resolvedFunction->identifier.Val() + "'";
        }
        if (auto re = DynamicCast<RefExpr*>(ce.baseFunc.get())) {
            return "the call to '" + re->ref.identifier.Val() + "'";
        }
        if (auto ma = DynamicCast<MemberAccess*>(ce.baseFunc.get())) {
            return "the call to '" + ma->field.Val() + "'";
        }
        return "this call";
    }

    /**
     * Effects (rule 5 of "Effect requirements"): 'resume r throwing e' injects 'e' at the
     * suspended 'perform' site, so it is resolved by the scopes that cover every possible perform
     * site -- the 'try''s own catch clauses, and the scopes enclosing the 'try-handle'. The catch
     * clauses come from the resume-only stack, which nothing else consults; everything beyond
     * that is the ordinary resolution.
     */
    void DemandInjected(Ptr<Ty> exceptionTy, const Node& site, const std::string& requiredBy)
    {
        if (!resumeSupplies.empty()) {
            supplies.push_back(resumeSupplies.back().types);
            supplyOwners.push_back(resumeSupplies.back().owner);
        }
        Demand(exceptionTy, site, requiredBy);
        if (!resumeSupplies.empty()) {
            supplies.pop_back();
            supplyOwners.pop_back();
        }
    }

    void Demand(Ptr<Ty> exceptionTy, const Node& site, const std::string& requiredBy)
    {
        auto kind = Sema::ClassifyCapability(typeManager, importManager, exceptionTy);
        if (kind == Sema::CapabilityKind::UNTRACKED) {
            return;
        }
        Sema::CapabilityContext context;
        context.inferenceOwner = DynamicCast<const FuncDecl*>(collectingFor);
        for (size_t i = 0; i < supplies.size(); ++i) {
            context.scopes.push_back({supplies[i], supplyOwners[i]});
        }
        Sema::CapabilityDemand demand{exceptionTy, &site, requiredBy, kind == Sema::CapabilityKind::EFFECT};
        auto resolution = Sema::ResolveCapability(typeManager, context, demand);
        if (resolution.kind != Sema::CapabilityResolutionKind::SUPPLIED) {
            missHandler.HandleMiss(resolution.demand);
        }
    }

    TypeManager& typeManager;
    const ImportManager& importManager;
    Sema::CapabilityMissHandler& missHandler;
    /// Sema-owned consumer view, also used for implicit operations.
    Sema::EffectiveCapabilityType effective;
    std::vector<SupplyScope> supplies;
    std::vector<Ptr<const Node>> supplyOwners;
    /// Effects: the capabilities a 'resume ... throwing' may resolve against on top of the
    /// ordinary stack -- the catch clauses of the very 'try' whose handler is running. Kept apart
    /// from 'supplies' because an ordinary 'throw' in a handler body must NOT see them: the
    /// handler runs where the handler was installed, while a resumed exception surfaces at the
    /// suspended 'perform', inside the try's body.
    std::vector<Sema::CapabilityScope> resumeSupplies;
    Sema::EnsureCapabilityContract ensure;
    // Set while collecting one declaration's residual demands: its own inferred list is not a supply.
    Ptr<const Decl> collectingFor{nullptr};
    /// Only the reporting pass carries one: the collecting pass of inference walks every body a
    /// second time, and a warning emitted there would be a duplicate.
    Ptr<DiagnosticEngine> diag{nullptr};
};
/// Collects residual demands instead of diagnosing them (miss-handler seam).
class CollectingMissHandler : public Sema::CapabilityMissHandler {
public:
    void HandleMiss(const Sema::CapabilityDemand& demand) override
    {
        if (!Ty::IsTyCorrect(demand.exceptionTy)) {
            return;
        }
        // Effect requirements are never inferred (policy table): they are semantic
        // contract and, under evidence passing, ABI. Dropping them here leaves them undischarged,
        // so the reporting pass diagnoses them instead of silently widening the declaration.
        if (demand.isEffect) {
            return;
        }
        collected.emplace_back(demand.exceptionTy);
    }
    std::vector<Ptr<Ty>> Take()
    {
        auto ret = std::move(collected);
        collected.clear();
        return ret;
    }

private:
    std::vector<Ptr<Ty>> collected;
};

} // namespace

namespace Cangjie::Sema {
bool IsInferenceEligible(const FuncDecl& fd)
{
    if (!fd.funcBody || !fd.funcBody->body) {
        return false;
    }
    if (fd.ownerFunc || fd.TestAnyAttr(Attribute::IMPORTED, Attribute::MAIN_ENTRY) || IsExportedDecl(fd)) {
        return false;
    }
    // No capability scope encloses a finalizer -- it may run after the supplying handlers are
    // gone -- so it is not a declaration a list can be inferred for either: a checked throw
    // inside one has nothing to discharge it and is reported at the throw. A static initializer
    // is the same: it runs during the program's global initialization, where no handler of the
    // program's own is installed, exactly as a static field initializer does -- and it has no call
    // site at which an inferred list could be paid.
    if (fd.IsFinalizer() || IsStaticInitializer(fd)) {
        return false;
    }
    // Interface members are contracts: their lists are written explicitly.
    if (fd.outerDecl && fd.outerDecl->astKind == ASTKind::INTERFACE_DECL) {
        return false;
    }
    // A clause ending in '...' re-opens inference, so such a declaration is eligible too -- the
    // distinction the incremental frontend's private copy of this predicate used to miss, which
    // let a body edit leave callers on a stale contract again (review finding I45).
    auto& clause = fd.funcBody->throwsClause;
    return IsNestedFunc(fd) ? clause && clause->hasEllipsis : !clause || clause->hasEllipsis;
}

bool IsExportedDecl(const Decl& decl)
{
    // Effective visibility: the narrowest of the declaration's own modifier and those of its
    // enclosing declarations, so a 'public' method of an 'internal' class does not leave the module
    // and is inferred, while a 'private init' of a 'public' class is inferred too.
    if (auto fd = DynamicCast<const FuncDecl*>(&decl); fd && IsNestedFunc(*fd)) {
        return false;
    }
    for (auto current = Ptr<const Decl>(&decl); current; current = current->outerDecl) {
        if (current->outerDecl && current->outerDecl->astKind == ASTKind::INTERFACE_DECL) {
            continue; // an interface member is a public contract, written modifier or not
        }
        if (!current->outerDecl && current->TestAttr(Attribute::PROTECTED)) {
            return false;
        }
        if (!current->TestAttr(Attribute::PUBLIC) && !current->TestAttr(Attribute::PROTECTED)) {
            return false;
        }
    }
    return true;
}

void ReportCapabilityMissHandler::HandleMiss(const CapabilityDemand& demand)
{
    CJC_NULLPTR_CHECK(demand.demandSite);
    if ((demand.isEffect ? effects : exceptions) == CheckingLevel::OFF) {
        return; // This checking axis imposes no obligations.
    }
    // Held until the package has been walked: several misses at one site have to be reported
    // together (see 'Finish').
    pending.emplace_back(demand);
}

void ReportCapabilityMissHandler::Finish()
{
    auto batch = std::move(pending);
    pending.clear();
    // Group by site and kind so independent checking levels and warning groups remain visible.
    std::vector<std::pair<std::pair<Ptr<const Node>, bool>, std::vector<const CapabilityDemand*>>> groups;
    for (auto& demand : batch) {
        auto key = std::make_pair(Ptr<const Node>(demand.demandSite), demand.isEffect);
        auto it = std::find_if(groups.begin(), groups.end(), [&key](auto& g) { return g.first == key; });
        if (it == groups.end()) {
            groups.emplace_back(key, std::vector<const CapabilityDemand*>{&demand});
        } else {
            it->second.emplace_back(&demand);
        }
    }
    for (auto& [key, demands] : groups) {
        auto& first = *demands.front();
        bool asWarning = (first.isEffect ? effects : exceptions) == CheckingLevel::WARN;
        // Each capability kind uses its own terminology, checking level, and warning group.
        if (demands.size() == 1) {
            auto tyName = Ty::ToString(first.exceptionTy);
            auto kind = first.isEffect ? (asWarning ? DiagKindRefactor::sema_chexc_missing_handler_capability_warn
                                                    : DiagKindRefactor::sema_chexc_missing_handler_capability)
                                       : (asWarning ? DiagKindRefactor::sema_chexc_missing_capability_warn
                                                    : DiagKindRefactor::sema_chexc_missing_capability);
            auto builder = diag.DiagnoseRefactor(kind, *first.demandSite, tyName, tyName);
            builder.AddMainHintArguments(first.requiredBy);
            continue;
        }
        std::string names;
        std::string types;
        const std::string capability = first.isEffect ? "CanPerform<" : "CanThrow<";
        for (auto demand : demands) {
            auto tyName = Ty::ToString(demand->exceptionTy);
            names += (names.empty() ? "" : ", ") + ("'" + tyName + "'");
            types += (types.empty() ? "" : ", ") + ("'" + capability + tyName + ">'");
        }
        auto kind = asWarning ? (first.isEffect ? DiagKindRefactor::sema_effect_missing_capabilities_warn
                                                : DiagKindRefactor::sema_chexc_missing_capabilities_warn)
                              : (first.isEffect ? DiagKindRefactor::sema_effect_missing_capabilities
                                                : DiagKindRefactor::sema_chexc_missing_capabilities);
        auto builder = diag.DiagnoseRefactor(kind, *first.demandSite, names, types);
        builder.AddMainHintArguments("required by " + first.requiredBy);
    }
}

void CheckCompletedOverrides(TypeManager& typeManager, const ImportManager& importManager, Package& pkg,
    DiagnosticEngine& diag, CheckingLevel exceptions, CheckingLevel effects, const EffectiveCapabilityType& effective)
{
    std::vector<Ptr<FuncDecl>> declarations;
    Walker(&pkg, [&declarations](Ptr<Node> node) {
        if (auto fd = DynamicCast<FuncDecl*>(node)) {
            declarations.emplace_back(fd);
        }
        return VisitAction::WALK_CHILDREN;
    }).Walk();
    for (auto decl : declarations) {
        auto childTy = DynamicCast<FuncTy*>(decl->GetTy());
        if (!childTy) {
            continue;
        }
        auto& caps = childTy->capTys;
        for (auto parent : typeManager.GetOverridden(*decl)) {
            auto parentTy = DynamicCast<FuncTy*>(parent->GetTy());
            if (!parentTy) {
                continue;
            }
            auto effectiveParent =
                DynamicCast<FuncTy*>(effective ? effective(*parent, parent->GetTy(), false) : parent->GetTy());
            auto parentCaps = effectiveParent ? effectiveParent->capTys : std::vector<Ptr<Ty>>{};
            if (decl->outerDecl && Ty::IsTyCorrect(decl->outerDecl->GetTy())) {
                MultiTypeSubst mts;
                typeManager.GenerateGenericMapping(mts, *decl->outerDecl->GetTy());
                TypeSubst subst;
                for (auto& [var, candidates] : mts) {
                    if (candidates.size() == 1) {
                        subst.emplace(var, *candidates.begin());
                    }
                }
                for (auto& cap : parentCaps) {
                    cap = typeManager.GetInstantiatedTy(cap, subst);
                }
            }
            if (parent->TestAttr(Attribute::GENERIC) && decl->TestAttr(Attribute::GENERIC)) {
                auto mapping = typeManager.GenerateGenericMappingFromGeneric(*parent, *decl);
                for (auto& cap : parentCaps) {
                    cap = typeManager.GetInstantiatedTy(cap, mapping);
                }
                parentCaps = typeManager.NormalizeCapTys(parentCaps);
            }
            for (auto capTy : caps) {
                if (!Ty::IsTyCorrect(capTy) || typeManager.IsCapTysSubsumed({capTy}, parentCaps)) {
                    continue;
                }
                // A property accessor is not what the author wrote and a compiler-generated one has
                // no position at all; the property is. A declaration overridden across a package
                // boundary is rebuilt from the '.cjo' and has no position either -- the message
                // names it, only the second location is lost.
                auto blame = GetDiagnosableDecl(*decl);
                if (!blame) {
                    continue;
                }
                // The checking level applies here as everywhere: at 'warn' the violation is
                // reported and the package still builds.
                bool effect = TypeCheckUtil::IsCommandTy(typeManager, importManager, capTy);
                auto level = effect ? effects : exceptions;
                if (level == CheckingLevel::OFF) {
                    continue;
                }
                auto kind = level == CheckingLevel::WARN
                    ? (effect ? DiagKindRefactor::sema_effect_override_missing_capability_warn
                              : DiagKindRefactor::sema_chexc_override_missing_capability_warn)
                    : (effect ? DiagKindRefactor::sema_effect_override_missing_capability
                              : DiagKindRefactor::sema_chexc_override_missing_capability);
                auto builder = diag.DiagnoseRefactor(
                    kind, MakeRangeForDeclIdentifier(*blame), Ty::ToString(capTy), GetDiagnosableDeclName(*decl));
                builder.AddMainHintArguments(Ty::ToString(capTy));
                if (auto parentBlame = GetDiagnosableDecl(*parent)) {
                    builder.AddNote(MakeRangeForDeclIdentifier(*parentBlame),
                        parentTy->capTys.empty()
                            ? "the overridden or implemented declaration has no 'throws' clause, and this "
                              "one's list was inferred from its body"
                            : "the overridden or implemented declaration is declared here");
                }
            }
        }
    }
}

std::vector<Ptr<Ty>> GetCapturesCapTys(const AST::Decl& decl)
{
    return TypeCheckUtil::GetDeclCapturesCapTys(decl);
}

std::vector<Ptr<Ty>> FilterCapabilityKinds(
    TypeManager& typeManager, const std::vector<Ptr<Ty>>& caps, CheckingLevel exceptions, CheckingLevel effects)
{
    std::vector<Ptr<Ty>> kept;
    for (auto cap : caps) {
        if (!Ty::IsTyCorrect(cap)) {
            continue;
        }
        bool effect = false;
        auto isCommand = [](Ptr<Ty> ty) {
            auto decl = Ty::GetDeclPtrOfTy(ty);
            return decl && decl->fullPackageName == EFFECT_PACKAGE_NAME && decl->identifier == CLASS_COMMAND;
        };
        // Generic upper bounds may name a subclass of Command rather than Command itself.
        // Follow those bounds' nominal ancestors too, without revisiting recursive bounds.
        std::vector<Ptr<Ty>> pending{cap};
        std::unordered_set<Ptr<Ty>> visited;
        while (!pending.empty() && !effect) {
            auto current = pending.back();
            pending.pop_back();
            if (!visited.emplace(current).second) {
                continue;
            }
            effect = isCommand(current);
            if (!effect) {
                auto supers = typeManager.GetAllSuperTys(*current);
                pending.insert(pending.end(), supers.begin(), supers.end());
            }
        }
        if ((effect ? effects : exceptions) != CheckingLevel::OFF) {
            kept.emplace_back(cap);
        }
    }
    return typeManager.NormalizeCapTys(kept);
}

CapabilityKind ClassifyCapability(TypeManager& typeManager, const ImportManager& importManager, Ptr<Ty> ty)
{
    if (!Ty::IsTyCorrect(ty) || TypeCheckUtil::IsUncheckedExceptionTy(typeManager, importManager, ty)) {
        return CapabilityKind::UNTRACKED;
    }
    if (TypeCheckUtil::IsCommandTy(typeManager, importManager, ty)) {
        return CapabilityKind::EFFECT;
    }
    auto exception = importManager.GetCoreDecl<ClassDecl>(CLASS_EXCEPTION);
    if (exception && Ty::IsTyCorrect(exception->GetTy()) && typeManager.IsSubtype(ty, exception->GetTy())) {
        return CapabilityKind::EXCEPTION;
    }
    return CapabilityKind::UNTRACKED;
}

CapabilityResolution ResolveCapability(
    TypeManager& typeManager, const CapabilityContext& context, const CapabilityDemand& demand)
{
    for (auto scope = context.scopes.rbegin(); scope != context.scopes.rend(); ++scope) {
        for (auto supplied : scope->types) {
            if (Ty::IsTyCorrect(supplied) && typeManager.IsSubtype(demand.exceptionTy, supplied)) {
                return {CapabilityResolutionKind::SUPPLIED, demand, scope->owner, supplied};
            }
        }
    }
    if (!demand.isEffect && context.inferenceOwner) {
        return {CapabilityResolutionKind::RESIDUAL, demand, context.inferenceOwner};
    }
    return {CapabilityResolutionKind::MISSING, demand, nullptr};
}

std::vector<Ptr<Ty>> CollectCapabilityRequirements(TypeManager& typeManager, const ImportManager& importManager,
    FuncDecl& decl, const EnsureCapabilityContract& ensure, const EffectiveCapabilityType& effective)
{
    CollectingMissHandler collector;
    CapabilityChecker checker(typeManager, importManager, collector, effective, ensure);
    checker.CollectResidualDemands(decl, IsInferenceEligible(decl) ? &decl : nullptr);
    return collector.Take();
}

void CheckCapabilities(TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg,
    CapabilityMissHandler& missHandler, DiagnosticEngine& diag, const EffectiveCapabilityType& effective)
{
    CapabilityChecker(typeManager, importManager, missHandler, effective, {}, &diag).CheckPackage(pkg);
    // A handler that batches its misses reports them now that the package is walked.
    missHandler.Finish();
}
} // namespace Cangjie::Sema
