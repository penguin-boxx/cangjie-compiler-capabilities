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
 *   unreachable inside them. Effect-handler clauses ('handle') are ignored entirely.
 * - Demands: 'throw e' demands the static type of 'e'; a call demands every entry of the
 *   resolved callee's (or called function value's) instantiated functional type. A default
 *   parameter value is checked against the callable's own scope; an instance field initializer
 *   must be satisfiable in EVERY constructor's scope; static and top-level initializers have
 *   no capability scope.
 * - Resolution: a demand is satisfied iff some active supply S exists with demanded <: S,
 * searched from the innermost scope outwards, first match.
 *
 * The pass never mutates types; unsatisfied demands go to a CapabilityMissHandler — the seam
 * where capability-parameter inference will later collect residual demands.
 */

#include "cangjie/Sema/CapabilityCheck.h"

#include <algorithm>
#include <functional>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "TypeCheckUtil.h"
#include "cangjie/AST/ASTCasting.h"
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
/// Consulted when the lexical scope stack has no suitable supply; used for the every-constructor
/// rule of instance field initializers. Null means no further supplies.
using RootSupply = std::function<bool(Ptr<Ty>)>;
/// Assumption imports, per file: the exception types imposed on every call into
/// each named package. Keyed per file because that is where an import — and with it the consumer's
/// trust claim about the dependency — lives.
using AssumedThrows = std::unordered_map<std::string, std::vector<Ptr<Ty>>>;
using AssumedThrowsByFile = std::unordered_map<Ptr<const File>, AssumedThrows>;

/**
 * Collects the assumption imports of a package.
 *
 * The bare form '@AssumeThrows' assumes 'Exception'. A tuple entry — written directly or reached
 * through a type alias — is a capability list and is spliced in. The claim is
 * recorded under every package name the import could denote, so it matches the callee's package
 * whether the import names the package ('import legacy.db.*') or a declaration in it
 * ('import legacy.db.query').
 */
AssumedThrowsByFile CollectAssumedThrows(const Package& pkg, const ImportManager& importManager)
{
    AssumedThrowsByFile byFile;
    for (auto& file : pkg.files) {
        if (!file) {
            continue;
        }
        for (auto& import : file->imports) {
            if (!import || import->IsImportMulti()) {
                continue; // Desugared into single imports, which carry copies of the annotations.
            }
            for (auto& anno : import->annotations) {
                if (!anno || !anno->assumeThrows) {
                    continue;
                }
                std::vector<Ptr<Ty>> caps;
                if (anno->assumeThrows->capTypes.empty()) {
                    auto exception = importManager.GetCoreDecl<ClassDecl>(CLASS_EXCEPTION);
                    if (exception && Ty::IsTyCorrect(exception->GetTy())) {
                        caps.emplace_back(exception->GetTy());
                    }
                } else {
                    caps = TypeCheckUtil::ExpandCapabilityList(anno->assumeThrows->capTypes);
                }
                if (caps.empty()) {
                    continue;
                }
                for (auto& name : import->content.GetPossiblePackageNames()) {
                    auto& entry = byFile[file.get()][name];
                    for (auto cap : caps) {
                        if (Ty::IsTyCorrect(cap) && !Utils::In(cap, entry)) {
                            entry.emplace_back(cap);
                        }
                    }
                }
            }
        }
    }
    return byFile;
}

/// Effects: an entry is an effect requirement iff it is a 'Command' subtype, and
/// an exception requirement iff it is an 'Exception' subtype. The two roots are disjoint, which is
/// what lets one capability list carry both kinds (decision D17).
bool IsCommandTy(TypeManager& typeManager, const ImportManager& importManager, Ptr<Ty> ty)
{
    if (!Ty::IsTyCorrect(ty)) {
        return false;
    }
    auto command = importManager.GetImportedDecl(EFFECT_PACKAGE_NAME, CLASS_COMMAND);
    if (!command) {
        return false; // No effect handlers in this build: nothing is a command.
    }
    // Compare DECLARATIONS, not types: 'Command' is generic, so a subtype test against the
    // uninstantiated 'Command<T>' fails for a concrete 'C <: Command<Int64>'.
    if (Ty::GetDeclPtrOfTy(ty) == command) {
        return true;
    }
    for (auto superTy : typeManager.GetAllSuperTys(*ty)) {
        if (Ty::GetDeclPtrOfTy(superTy) == command) {
            return true;
        }
    }
    return false;
}

class CapabilityChecker {
public:
    CapabilityChecker(TypeManager& typeManager, const ImportManager& importManager,
        Sema::CapabilityMissHandler& missHandler, const AssumedThrowsByFile& assumed,
        const Sema::InferredCapabilities& inferred = {})
        : typeManager(typeManager),
          importManager(importManager),
          missHandler(missHandler),
          assumed(assumed),
          inferred(inferred)
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
        collectingFor = nullptr;
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
        std::vector<SupplyScope> ctorCapLists;
        for (auto& member : decl.GetMemberDecls()) {
            auto fd = DynamicCast<FuncDecl*>(member.get());
            if (fd && fd->TestAttr(Attribute::CONSTRUCTOR) && !fd->TestAttr(Attribute::STATIC) && fd->funcBody) {
                ctorCapLists.emplace_back(TypeCheckUtil::GetFuncBodyCapTys(*fd->funcBody));
            }
        }
        if (ctorCapLists.empty()) {
            ctorCapLists.emplace_back();
        }
        RootSupply everyCtorSupplies = [this, ctorCapLists = std::move(ctorCapLists)](Ptr<Ty> demanded) {
            return std::all_of(ctorCapLists.begin(), ctorCapLists.end(),
                [this, demanded](const SupplyScope& caps) { return HasSuitableSupply(caps, demanded); });
        };
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
                    CheckInitializer(vd, isInstanceField ? everyCtorSupplies : nullptr);
                    break;
                }
                default:
                    // PRIMARY_CTOR_DECL is desugared into an 'init' member during type check.
                    break;
            }
        }
    }

    void CheckCallable(FuncDecl& fd)
    {
        if (!fd.funcBody) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        currentFile = fd.curFile;
        rootSupply = nullptr;
        // The enclosing class's captured capabilities are in scope throughout a member that has
        // a receiver to carry them. A static member, a static initializer and a
        // finalizer have none, and a checked throw is forbidden there. Derived
        // from the declaration's owner rather than from checker state, so inference — which
        // checks declarations one by one — sees the same supplies as the reporting pass.
        bool hasReceiver = !fd.TestAttr(Attribute::STATIC) && !fd.IsFinalizer();
        auto captures = hasReceiver ? OwnerCaptures(fd) : SupplyScope{};
        PushCaptures(captures);
        // The FUNC_BODY visit then pushes the declaration's own clause scope. The walker visits
        // parameter default values before the body, matching "as if it appeared at the
        // beginning of the body".
        WalkScoped(fd.funcBody.get());
        PopCaptures(captures);
        CJC_ASSERT(supplies.empty());
    }

    void CheckInitializer(VarDeclAbstract& vd, RootSupply root)
    {
        if (!vd.initializer) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        currentFile = vd.curFile;
        rootSupply = std::move(root);
        // Only an INSTANCE field initializer runs with a receiver; a static one has no
        // capability scope at all. 'root' is non-null exactly for
        // instance fields.
        auto captures = rootSupply ? OwnerCaptures(vd) : SupplyScope{};
        PushCaptures(captures);
        WalkScoped(vd.initializer.get());
        PopCaptures(captures);
        rootSupply = nullptr;
        CJC_ASSERT(supplies.empty());
    }

    /// The 'captures' list of the declaration's own class or struct — never an inherited one
    ///.
    SupplyScope OwnerCaptures(const Decl& decl) const
    {
        return decl.outerDecl ? TypeCheckUtil::GetDeclCapturesCapTys(*decl.outerDecl) : SupplyScope{};
    }

    void PushCaptures(const SupplyScope& captures)
    {
        if (!captures.empty()) {
            supplies.emplace_back(captures);
        }
    }

    void PopCaptures(const SupplyScope& captures)
    {
        if (!captures.empty()) {
            supplies.pop_back();
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

    VisitAction VisitPre(Ptr<Node> node)
    {
        CJC_NULLPTR_CHECK(node);
        switch (node->astKind) {
            case ASTKind::FUNC_BODY: {
                // Named callables: the body of a callable with a 'throws' list is a capability
                // scope. Nested (local) functions keep the enclosing scopes: pre-Modal,
                // capability checking is purely lexical (author ruling).
                auto& fb = StaticCast<FuncBody&>(*node);
                auto caps = TypeCheckUtil::GetFuncBodyCapTys(fb);
                // An inferred list acts as the declaration's clause — except while collecting
                // that very declaration's residual demands, when consulting it would make every
                // requirement look discharged.
                if (fb.funcDecl && fb.funcDecl.get() != collectingFor.get()) {
                    auto it = inferred.find(fb.funcDecl);
                    if (it != inferred.end()) {
                        caps.insert(caps.end(), it->second.begin(), it->second.end());
                    }
                }
                supplies.emplace_back(std::move(caps));
                return VisitAction::WALK_CHILDREN;
            }
            case ASTKind::LAMBDA_EXPR:
                // A literal's capability list comes from the expected type only and is stored
                // on the literal's functional type.
                supplies.emplace_back(GetLiteralCapTys(StaticCast<LambdaExpr&>(*node)));
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
            case ASTKind::CALL_EXPR:
                HandleCall(StaticCast<CallExpr&>(*node));
                return VisitAction::WALK_CHILDREN;
            default:
                return VisitAction::WALK_CHILDREN;
        }
    }

    VisitAction VisitPost(Ptr<Node> node)
    {
        // Balanced with VisitPre: these two kinds always push exactly one scope there.
        if (node->astKind == ASTKind::FUNC_BODY || node->astKind == ASTKind::LAMBDA_EXPR) {
            supplies.pop_back();
        }
        return VisitAction::KEEP_DECISION;
    }

    SupplyScope GetLiteralCapTys(const LambdaExpr& le) const
    {
        auto funcTy = DynamicCast<FuncTy*>(le.GetTy());
        return funcTy ? funcTy->capTys : SupplyScope{};
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
        for (auto& resource : te.resourceSpec) {
            // Resource initializers of try-with-resources are inside the try's scope: their
            // exceptions are caught by the same clauses.
            WalkScoped(resource.get());
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
        // A 'catch' block is not inside its try's capability scope: rethrowing a caught checked
        // exception requires a capability from the enclosing scopes. Same for 'finally' and for
        // a 'handle' body, which runs where the handler was installed.
        for (auto& catchBlock : te.catchBlocks) {
            WalkScoped(catchBlock.get());
        }
        for (auto& handler : te.handlers) {
            if (handler.desugaredLambda) {
                WalkScoped(handler.desugaredLambda.get());
            } else {
                WalkScoped(handler.block.get());
            }
        }
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

    void HandleSpawn(SpawnExpr& se)
    {
        // The thread context argument is evaluated at the spawn site, in the current scopes.
        WalkScoped(se.arg.get());
        // A 'spawn' body starts with an EMPTY capability scope stack (author ruling): the
        // enclosing capabilities (including any every-constructor root) are unreachable.
        std::vector<SupplyScope> savedSupplies;
        savedSupplies.swap(supplies);
        auto savedRoot = std::move(rootSupply);
        rootSupply = nullptr;
        WalkScoped(se.task.get());
        supplies = std::move(savedSupplies);
        rootSupply = std::move(savedRoot);
    }

    void HandleCall(CallExpr& ce)
    {
        // Both resolved-function calls and function-value calls: the callee expression's type
        // is the callee's functional type with generic instantiation applied.
        if (!ce.baseFunc) {
            return;
        }
        auto funcTy = DynamicCast<FuncTy*>(ce.baseFunc->GetTy());
        if (!funcTy) {
            return;
        }
        std::vector<Ptr<Ty>> demands = funcTy->capTys;
        // Defence in depth: a callee expression rebuilt by machinery that predates this feature
        // can carry a capability-free functional type. Recover from the callee's DECLARED clause
        // — never from its FuncTy capTys, which also hold the inferred entries the union below
        // contributes — re-instantiated through the receiver so a generic accessor demands
        // 'MyExc<Int64>' rather than a bare 'MyExc<T>'.
        if (demands.empty() && ce.resolvedFunction) {
            Ptr<Ty> receiverTy = nullptr;
            if (auto ma = DynamicCast<MemberAccess*>(ce.baseFunc.get()); ma && ma->baseExpr) {
                receiverTy = ma->baseExpr->GetTy();
            }
            demands = TypeCheckUtil::GetInstantiatedAccessorCapTys(typeManager, *ce.resolvedFunction, receiverTy);
        }
        // A callee whose list was inferred carries it beside the AST: this call
        // site's type was formed during type check, before inference ran, so completing the
        // declaration's type cannot reach it. Unioned, not appended: the entries can be
        // pointer-identical to those already present.
        if (ce.resolvedFunction) {
            auto it = inferred.find(ce.resolvedFunction);
            if (it != inferred.end()) {
                // The entries name the CALLEE's type parameters; the declared list on the callee
                // expression was already substituted by type check, so these must be too, or a
                // generic callee's requirement is demanded (and discharged) at the wrong type.
                auto typeMapping = CalleeTypeMapping(ce);
                for (auto cap : it->second) {
                    auto demanded = typeMapping.empty() ? cap : typeManager.GetInstantiatedTy(cap, typeMapping);
                    if (Ty::IsTyCorrect(demanded) && !Utils::In(demanded, demands)) {
                        demands.emplace_back(demanded);
                    }
                }
            }
        }
        AddAssumedDemands(ce, demands);
        for (auto cap : demands) {
            if (Ty::IsTyCorrect(cap)) {
                Demand(cap, ce, DescribeCallee(ce));
            }
        }
        DemandConstructedCaptures(ce);
    }

    /**
     * Assumption imports: a call into an assumed package carries the assumed
     * list on top of whatever the callee declares. Assumptions only ADD obligations relative to
     * the read-as-empty default, so the two are unioned; the entries can already be present when
     * the dependency is itself checked.
     */
    void AddAssumedDemands(const CallExpr& ce, std::vector<Ptr<Ty>>& demands) const
    {
        if (assumed.empty() || !ce.resolvedFunction) {
            return;
        }
        // The claim belongs to the file that wrote the import. A node the desugar rebuilt may have
        // lost its file, in which case the enclosing declaration's file is the same one.
        Ptr<const File> file = currentFile;
        if (ce.curFile) {
            file = ce.curFile;
        }
        auto byFile = assumed.find(file);
        if (byFile == assumed.end()) {
            return;
        }
        auto entry = byFile->second.find(ce.resolvedFunction->fullPackageName);
        if (entry == byFile->second.end()) {
            return;
        }
        for (auto cap : entry->second) {
            if (Ty::IsTyCorrect(cap) && !Utils::In(cap, demands)) {
                demands.emplace_back(cap);
            }
        }
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

    bool HasSuitableSupply(const SupplyScope& caps, Ptr<Ty> demanded)
    {
        return std::any_of(caps.begin(), caps.end(), [this, demanded](Ptr<Ty> supply) {
            return Ty::IsTyCorrect(supply) && typeManager.IsSubtype(demanded, supply);
        });
    }

    void Demand(Ptr<Ty> exceptionTy, const Node& site, const std::string& requiredBy)
    {
        // Throwing an unchecked exception never requires a capability. Call-site
        // demands are filtered here too: a capability parameter whose type instantiates to an
        // unchecked exception type is trivially satisfied.
        if (TypeCheckUtil::IsUncheckedExceptionTy(typeManager, importManager, exceptionTy)) {
            return;
        }
        // The Error hierarchy is fail-fast, never statically tracked (the fail-fast/recoverable split,
        // after Midori's Error Model): 'Error <: ToString' is a separate root, so a class type
        // under NEITHER tracked root -- Exception (throws) nor Command (performs) -- never
        // demands. Found by the stdlib migration: std.core's own OutOfMemoryError throws warned
        // without this. The Command test is essential, not defensive: commands are classes
        // outside the Exception root too, and exempting them here silenced every effect demand
        // (caught by the performs negative tests). Type parameters keep demanding: a generic
        // entry only instantiates where its clause was legal.
        if (exceptionTy->IsClass()) {
            auto exception = importManager.GetCoreDecl<ClassDecl>(CLASS_EXCEPTION);
            bool underException = exception && Ty::IsTyCorrect(exception->GetTy()) &&
                typeManager.IsSubtype(exceptionTy, exception->GetTy());
            if (!underException && !IsCommandTy(typeManager, importManager, exceptionTy)) {
                return;
            }
        }
        // Scopes are searched from the innermost enclosing one outwards; within one scope the
        // first suitable entry in textual order supplies the capability.
        for (auto scope = supplies.rbegin(); scope != supplies.rend(); ++scope) {
            if (HasSuitableSupply(*scope, exceptionTy)) {
                return;
            }
        }
        if (rootSupply && rootSupply(exceptionTy)) {
            return;
        }
        missHandler.HandleMiss({exceptionTy, &site, requiredBy, IsCommandTy(typeManager, importManager, exceptionTy)});
    }

    TypeManager& typeManager;
    const ImportManager& importManager;
    Sema::CapabilityMissHandler& missHandler;
    /// Assumption imports of the package being checked, indexed by the file they appear in.
    const AssumedThrowsByFile& assumed;
    std::vector<SupplyScope> supplies;
    RootSupply rootSupply;
    // Lists inferred for declarations without an authoritative clause.
    const Sema::InferredCapabilities& inferred;
    // Set while collecting one declaration's residual demands: its own inferred list is not a supply.
    Ptr<const Decl> collectingFor{nullptr};
    // File of the declaration being checked; the fallback for a call site that lost its own.
    Ptr<const File> currentFile{nullptr};
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

/**
 * Capability parameter inference.
 *
 * Eligible declarations are those without an authoritative clause that are not part of the
 * package's exported surface. Their lists are the least solution of
 *     C(f) = local(f) ∪ ⋃ over call sites in f: (C(callee) ∖ discharged at the site)
 * computed per strongly connected component of the intra-package call graph, bottom-up.
 *
 * The subtraction needs no separate representation: running the checking walker over a body in
 * collect mode reports exactly those requirements that the supply stack at their site does not
 * discharge, and a callee's current list is demanded at its call sites. Iterating that walk to
 * a fixed point therefore solves the equations directly, and monotonicity (lists only grow)
 * guarantees termination.
 */
class CapabilityInferencer {
public:
    CapabilityInferencer(TypeManager& typeManager, const ImportManager& importManager, DiagnosticEngine& diag)
        : typeManager(typeManager), importManager(importManager), diag(diag)
    {
    }

    Sema::InferredCapabilities Infer(Package& pkg)
    {
        // Assumed requirements participate in inference like declared ones.
        assumed = CollectAssumedThrows(pkg, importManager);
        CollectEligible(pkg);
        BuildCallGraph();
        for (auto& component : StronglyConnectedComponents()) {
            CheckPolymorphicRecursion(component);
            SolveComponent(component);
        }
        return std::move(inferred);
    }

private:
    /// Inference applies to declarations that are not part of the exported surface and carry no
    /// authoritative clause. A clause ending in `...` keeps inference on.
    static bool IsEligible(const FuncDecl& fd)
    {
        if (!fd.funcBody || !fd.funcBody->body) {
            return false;
        }
        if (fd.TestAttr(Attribute::PUBLIC) || fd.TestAttr(Attribute::PROTECTED)) {
            return false;
        }
        // No capability scope encloses a finalizer -- it may run after the supplying handlers are
        // gone -- so it is not a declaration a list can be inferred for either: a checked throw
        // inside one has nothing to discharge it and is reported at the throw.
        if (fd.IsFinalizer()) {
            return false;
        }
        // Interface members are contracts: their lists are written explicitly.
        if (fd.outerDecl && fd.outerDecl->astKind == ASTKind::INTERFACE_DECL) {
            return false;
        }
        // A non-private static class member can be redefined by a subclass and is dispatched
        // virtually, so the override rule applies to it — but override checking runs during type
        // check, before inference, and would not see an inferred list. Requiring an explicit
        // clause here keeps the two consistent; a post-inference re-check would let these be
        // inferred too.
        if (fd.TestAttr(Attribute::STATIC) && !fd.TestAttr(Attribute::PRIVATE) && fd.outerDecl &&
            fd.outerDecl->astKind == ASTKind::CLASS_DECL) {
            return false;
        }
        auto& clause = fd.funcBody->throwsClause;
        return !clause || clause->hasEllipsis;
    }

    void CollectEligibleMember(Decl& member)
    {
        if (auto fd = DynamicCast<FuncDecl*>(&member); fd && IsEligible(*fd)) {
            order.emplace_back(fd);
        } else if (auto pd = DynamicCast<PropDecl*>(&member)) {
            for (auto& accessor : pd->getters) {
                if (accessor && IsEligible(*accessor)) {
                    order.emplace_back(accessor.get());
                }
            }
            for (auto& accessor : pd->setters) {
                if (accessor && IsEligible(*accessor)) {
                    order.emplace_back(accessor.get());
                }
            }
        }
    }

    void CollectEligible(Package& pkg)
    {
        for (auto& file : pkg.files) {
            CJC_NULLPTR_CHECK(file);
            for (auto& decl : file->decls) {
                CJC_NULLPTR_CHECK(decl);
                if (decl->astKind == ASTKind::MAIN_DECL) {
                    continue; // 'main' clauses go to the default handler; never inferred.
                }
                CollectEligibleMember(*decl);
                for (auto& member : decl->GetMemberDecls()) {
                    if (member) {
                        CollectEligibleMember(*member);
                    }
                }
            }
        }
        for (size_t i = 0; i < order.size(); ++i) {
            index[order[i]] = i;
        }
    }

    /// Edges run from a caller to the eligible callees it invokes; only such edges can carry a
    /// list that is still being computed.
    void BuildCallGraph()
    {
        callees.resize(order.size());
        genericCalls.resize(order.size());
        for (size_t i = 0; i < order.size(); ++i) {
            auto caller = order[i];
            Walker(caller->funcBody.get(), [this, i](Ptr<Node> node) {
                if (auto ce = DynamicCast<CallExpr*>(node.get()); ce && ce->resolvedFunction) {
                    auto found = index.find(ce->resolvedFunction);
                    if (found != index.end()) {
                        if (found->second != i) {
                            callees[i].emplace(found->second);
                        }
                        // Self-calls are not graph edges (an SCC of one is still a cycle), but
                        // they are exactly where polymorphic recursion shows up, so record the
                        // call for the post-SCC check below.
                        genericCalls[i].emplace_back(Ptr<const CallExpr>(ce), found->second);
                    }
                }
                return VisitAction::WALK_CHILDREN;
            }).Walk();
        }
    }

    /**
     * A cycle that re-enters a member at a growing generic instantiation has no
     * finite candidate universe, so inference is rejected and explicit clauses are required.
     *
     * Only calls that stay inside the cycle can grow a type argument on every turn, so the check
     * runs per strongly connected component — including a component's self-calls, which are the
     * canonical case ('f<T>' calling 'f<Box<T>>') and are not graph edges. A call that merely
     * passes a wrapped type argument to a callee outside the cycle terminates and is fine.
     */
    void CheckPolymorphicRecursion(const std::vector<size_t>& component)
    {
        std::unordered_set<size_t> inCycle(component.begin(), component.end());
        bool isCycle = component.size() > 1;
        for (auto i : component) {
            auto caller = order[i];
            auto callerGeneric = caller->GetGeneric();
            if (!callerGeneric) {
                continue;
            }
            for (auto& [ce, callee] : genericCalls[i]) {
                bool selfCall = callee == i;
                if (!selfCall && (!isCycle || inCycle.count(callee) == 0)) {
                    continue; // Leaves the cycle: the instantiation cannot keep growing.
                }
                if (ReportGrowingInstantiation(*ce, i, *callerGeneric)) {
                    break;
                }
            }
        }
    }

    /// Reports the first type argument that properly contains one of the caller's own type
    /// parameters, i.e. one that is strictly larger on each turn of the cycle.
    bool ReportGrowingInstantiation(const CallExpr& ce, size_t caller, const Generic& callerGeneric)
    {
        if (reportedPolymorphic.count(caller) > 0) {
            return false;
        }
        auto nre = DynamicCast<NameReferenceExpr*>(ce.baseFunc.get());
        if (!nre) {
            return false;
        }
        for (auto typeArg : nre->instTys) {
            if (!Ty::IsTyCorrect(typeArg) || typeArg->IsGeneric()) {
                continue;
            }
            for (auto& typeParam : callerGeneric.typeParameters) {
                if (!typeParam || !Ty::IsTyCorrect(typeParam->GetTy())) {
                    continue;
                }
                if (typeArg != typeParam->GetTy() && ContainsTy(typeArg, typeParam->GetTy())) {
                    diag.DiagnoseRefactor(DiagKindRefactor::sema_chexc_polymorphic_recursion, ce,
                        order[caller]->identifier.Val(), Ty::ToString(typeArg));
                    reportedPolymorphic.emplace(caller);
                    return true;
                }
            }
        }
        return false;
    }

    static bool ContainsTy(Ptr<Ty> haystack, Ptr<Ty> needle)
    {
        if (!haystack) {
            return false;
        }
        if (haystack == needle) {
            return true;
        }
        return std::any_of(haystack->typeArgs.begin(), haystack->typeArgs.end(),
            [needle](Ptr<Ty> arg) { return ContainsTy(arg, needle); });
    }

    /// Tarjan's algorithm; components come out in reverse topological order, i.e. callees first,
    /// which is exactly the bottom-up order the phase ordering requires.
    std::vector<std::vector<size_t>> StronglyConnectedComponents()
    {
        tarjanIndex.assign(order.size(), kUnvisited);
        tarjanLow.assign(order.size(), 0);
        onStack.assign(order.size(), false);
        std::vector<std::vector<size_t>> components;
        for (size_t i = 0; i < order.size(); ++i) {
            if (tarjanIndex[i] == kUnvisited) {
                StrongConnect(i, components);
            }
        }
        return components;
    }

    void StrongConnect(size_t v, std::vector<std::vector<size_t>>& components)
    {
        tarjanIndex[v] = tarjanCounter;
        tarjanLow[v] = tarjanCounter;
        ++tarjanCounter;
        stack.emplace_back(v);
        onStack[v] = true;
        for (auto w : callees[v]) {
            if (tarjanIndex[w] == kUnvisited) {
                StrongConnect(w, components);
                tarjanLow[v] = std::min(tarjanLow[v], tarjanLow[w]);
            } else if (onStack[w]) {
                tarjanLow[v] = std::min(tarjanLow[v], tarjanIndex[w]);
            }
        }
        if (tarjanLow[v] != tarjanIndex[v]) {
            return;
        }
        std::vector<size_t> component;
        while (true) {
            auto w = stack.back();
            stack.pop_back();
            onStack[w] = false;
            component.emplace_back(w);
            if (w == v) {
                break;
            }
        }
        // Declaration order inside a component keeps diagnostics reproducible.
        std::sort(component.begin(), component.end());
        components.emplace_back(std::move(component));
    }

    /// Kleene iteration to the least fixed point. Members outside a cycle stabilize in one pass.
    void SolveComponent(const std::vector<size_t>& component)
    {
        CollectingMissHandler handler;
        CapabilityChecker checker(typeManager, importManager, handler, assumed, inferred);
        bool changed = true;
        while (changed) {
            changed = false;
            for (auto i : component) {
                auto decl = order[i];
                checker.CollectResidualDemands(*decl, decl);
                auto residual = handler.Take();
                if (MergeInto(inferred[decl], residual)) {
                    changed = true;
                }
            }
        }
    }

    /// Adds entries not already covered by the list; returns whether it grew.
    bool MergeInto(std::vector<Ptr<Ty>>& list, const std::vector<Ptr<Ty>>& additions)
    {
        bool grew = false;
        for (auto addition : additions) {
            bool covered = std::any_of(list.begin(), list.end(),
                [this, addition](Ptr<Ty> present) { return typeManager.IsSubtype(addition, present); });
            if (!covered) {
                list.emplace_back(addition);
                grew = true;
            }
        }
        return grew;
    }

    static constexpr size_t kUnvisited = static_cast<size_t>(-1);

    TypeManager& typeManager;
    const ImportManager& importManager;
    DiagnosticEngine& diag;
    std::vector<Ptr<FuncDecl>> order;
    std::unordered_map<Ptr<const Decl>, size_t> index;
    std::vector<std::set<size_t>> callees;
    /// Calls from an eligible declaration to an eligible one, kept for the polymorphic-recursion
    /// check, which is meaningful only once the cycles are known.
    std::vector<std::vector<std::pair<Ptr<const CallExpr>, size_t>>> genericCalls;
    std::unordered_set<size_t> reportedPolymorphic;
    Sema::InferredCapabilities inferred;
    /// Assumption imports of the package, shared with every checker below.
    AssumedThrowsByFile assumed;
    std::vector<size_t> tarjanIndex;
    std::vector<size_t> tarjanLow;
    std::vector<bool> onStack;
    std::vector<size_t> stack;
    size_t tarjanCounter{0};
};
} // namespace

namespace Cangjie::Sema {
void ReportCapabilityMissHandler::HandleMiss(const CapabilityDemand& demand)
{
    CJC_NULLPTR_CHECK(demand.demandSite);
    auto tyName = Ty::ToString(demand.exceptionTy);
    // Effects: an effect capability is named 'Handler<C>', not 'CanThrow<E>'.
    auto kind = demand.isEffect ? (asWarning ? DiagKindRefactor::sema_chexc_missing_handler_capability_warn
                                             : DiagKindRefactor::sema_chexc_missing_handler_capability)
                                : (asWarning ? DiagKindRefactor::sema_chexc_missing_capability_warn
                                             : DiagKindRefactor::sema_chexc_missing_capability);
    auto builder = diag.DiagnoseRefactor(kind, *demand.demandSite, tyName, tyName);
    builder.AddMainHintArguments(demand.requiredBy);
}

void CompleteInferredCapabilityTypes(TypeManager& typeManager, const InferredCapabilities& inferred)
{
    for (auto& [decl, caps] : inferred) {
        if (caps.empty() || !decl || !decl->funcBody) {
            continue;
        }
        auto funcTy = DynamicCast<FuncTy*>(decl->GetTy());
        if (!funcTy) {
            continue;
        }
        // Union: a clause ending in '...' contributes declared entries that are already present
        //.
        std::vector<Ptr<Ty>> completed = funcTy->capTys;
        for (auto cap : caps) {
            if (Ty::IsTyCorrect(cap) && !Utils::In(cap, completed)) {
                completed.emplace_back(cap);
            }
        }
        if (completed.size() == funcTy->capTys.size()) {
            continue;
        }
        auto completedTy = typeManager.GetFunctionTy(funcTy->paramTys, funcTy->retTy,
            {funcTy->IsCFunc(), funcTy->isClosureTy, funcTy->hasVariableLenArg, funcTy->noCast}, completed);
        decl->SetTy(completedTy);
        decl->funcBody->SetTy(completedTy);
    }
}

std::vector<Ptr<Ty>> GetCapturesCapTys(const AST::Decl& decl)
{
    return TypeCheckUtil::GetDeclCapturesCapTys(decl);
}

InferredCapabilities InferCapabilities(
    TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg, DiagnosticEngine& diag)
{
    return CapabilityInferencer(typeManager, importManager, diag).Infer(pkg);
}

void CheckCapabilities(TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg,
    CapabilityMissHandler& missHandler, const InferredCapabilities& inferred)
{
    auto assumed = CollectAssumedThrows(pkg, importManager);
    CapabilityChecker(typeManager, importManager, missHandler, assumed, inferred).CheckPackage(pkg);
}
} // namespace Cangjie::Sema
