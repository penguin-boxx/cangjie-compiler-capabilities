// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

/**
 * @file
 *
 * This file implements checked-exception capability argument checking (experimental, behind
 * '--experimental --enable-checked-exceptions'; proposal sections 3.3 and 3.5).
 *
 * Per callable body the pass walks the typed AST with a stack of capability scopes (supplies)
 * and checks every demand against it:
 * - Supplies: the callable's own 'throws' clause; a 'try' block introduces one capability per
 *   exception type listed in its catch patterns ('e: E1 | E2' introduces two) covering the try
 *   block and the resource initializers of a try-with-resources expression, while 'catch' and
 *   'finally' blocks stay outside; a function literal's body is covered by the capability list
 *   of the literal's own functional type (inferred from the expected type, proposal 3.5).
 *   'spawn' bodies start with an EMPTY stack (author ruling): enclosing capabilities are
 *   unreachable inside them. Effect-handler clauses ('handle') are ignored entirely.
 * - Demands: 'throw e' demands the static type of 'e'; a call demands every entry of the
 *   resolved callee's (or called function value's) instantiated functional type. A default
 *   parameter value is checked against the callable's own scope; an instance field initializer
 *   must be satisfiable in EVERY constructor's scope; static and top-level initializers have
 *   no capability scope.
 * - Resolution: a demand is satisfied iff some active supply S exists with demanded <: S,
 *   searched from the innermost scope outwards, first match (proposal 3.3).
 *
 * The pass never mutates types; unsatisfied demands go to a CapabilityMissHandler — the seam
 * where capability-parameter inference (proposal 6.3) will later collect residual demands.
 */

#include "cangjie/Sema/CapabilityCheck.h"

#include <algorithm>
#include <functional>
#include <string>
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
/// order (within one scope the first suitable entry wins, proposal 3.3).
using SupplyScope = std::vector<Ptr<Ty>>;
/// Consulted when the lexical scope stack has no suitable supply; used for the every-constructor
/// rule of instance field initializers. Null means no further supplies.
using RootSupply = std::function<bool(Ptr<Ty>)>;

class CapabilityChecker {
public:
    CapabilityChecker(
        TypeManager& typeManager, const ImportManager& importManager, Sema::CapabilityMissHandler& missHandler)
        : typeManager(typeManager), importManager(importManager), missHandler(missHandler)
    {
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
                // scope encloses them (proposal 3.3).
                CheckInitializer(StaticCast<VarDeclAbstract&>(decl), nullptr);
                break;
            default:
                break;
        }
    }

    void CheckMembers(Decl& decl)
    {
        // A capturing class or struct stores the listed capabilities at construction, so its own
        // clause supplies them to every member body (proposal 3.9 rules 3 and 4; until Modal
        // CangJie lands, every constructor captures and every body is covered). Rule 5: a
        // subclass does not see its superclass's captures — only the class's own clause counts.
        classCaptures = TypeCheckUtil::GetDeclCapturesCapTys(decl);
        // An instance field initializer has no scope of its own: its demands must be satisfiable
        // in the capability scope of EVERY constructor (proposal 3.3). With no explicit
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
        classCaptures.clear();
    }

    void CheckCallable(FuncDecl& fd)
    {
        if (!fd.funcBody) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        rootSupply = nullptr;
        // The enclosing class's captured capabilities, if any, are in scope throughout the
        // member (proposal 3.9); the FUNC_BODY visit then pushes the declaration's own clause
        // scope. The walker visits parameter default values before the body, matching "as if it
        // appeared at the beginning of the body" (proposal 3.3).
        PushClassCaptures();
        WalkScoped(fd.funcBody.get());
        PopClassCaptures();
        CJC_ASSERT(supplies.empty());
    }

    void CheckInitializer(VarDeclAbstract& vd, RootSupply root)
    {
        if (!vd.initializer) {
            return;
        }
        CJC_ASSERT(supplies.empty());
        rootSupply = std::move(root);
        PushClassCaptures();
        WalkScoped(vd.initializer.get());
        PopClassCaptures();
        rootSupply = nullptr;
        CJC_ASSERT(supplies.empty());
    }

    void PushClassCaptures()
    {
        if (!classCaptures.empty()) {
            supplies.emplace_back(classCaptures);
        }
    }

    void PopClassCaptures()
    {
        if (!classCaptures.empty()) {
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
            case ASTKind::FUNC_BODY:
                // Named callables: the body of a callable with a 'throws' list is a capability
                // scope. Nested (local) functions keep the enclosing scopes: pre-Modal,
                // capability checking is purely lexical (author ruling).
                supplies.emplace_back(TypeCheckUtil::GetFuncBodyCapTys(StaticCast<FuncBody&>(*node)));
                return VisitAction::WALK_CHILDREN;
            case ASTKind::LAMBDA_EXPR:
                // A literal's capability list comes from the expected type only and is stored
                // on the literal's functional type (proposal 3.5).
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
        // Effect-handler clauses ('handle') introduce no capabilities and are not checked
        // (author ruling); 'te.handlers', 'te.tryLambda' and 'te.finallyLambda' are ignored.
        supplies.emplace_back(CollectCatchCapTys(te));
        for (auto& resource : te.resourceSpec) {
            // Resource initializers of try-with-resources are inside the try's scope: their
            // exceptions are caught by the same clauses (proposal 3.3).
            WalkScoped(resource.get());
        }
        WalkScoped(te.tryBlock.get());
        supplies.pop_back();
        // A 'catch' block is not inside its try's capability scope: rethrowing a caught checked
        // exception requires a capability from the enclosing scopes. Same for 'finally'.
        for (auto& catchBlock : te.catchBlocks) {
            WalkScoped(catchBlock.get());
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
        for (auto cap : funcTy->capTys) {
            if (Ty::IsTyCorrect(cap)) {
                Demand(cap, ce, DescribeCallee(ce));
            }
        }
        DemandConstructedCaptures(ce);
    }

    void DemandConstructedCaptures(CallExpr& ce)
    {
        // Constructing an instance of a capturing class or struct requires its captured
        // capabilities at the construction site (proposal 3.9 rule 4). This covers 'C(...)',
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
        // Throwing an unchecked exception never requires a capability (proposal 6.4). Call-site
        // demands are filtered here too: a capability parameter whose type instantiates to an
        // unchecked exception type is trivially satisfied (proposal 3.2 rule 5).
        if (TypeCheckUtil::IsUncheckedExceptionTy(typeManager, importManager, exceptionTy)) {
            return;
        }
        // Scopes are searched from the innermost enclosing one outwards; within one scope the
        // first suitable entry in textual order supplies the capability (proposal 3.3).
        for (auto scope = supplies.rbegin(); scope != supplies.rend(); ++scope) {
            if (HasSuitableSupply(*scope, exceptionTy)) {
                return;
            }
        }
        if (rootSupply && rootSupply(exceptionTy)) {
            return;
        }
        missHandler.HandleMiss({exceptionTy, &site, requiredBy});
    }

    TypeManager& typeManager;
    const ImportManager& importManager;
    Sema::CapabilityMissHandler& missHandler;
    std::vector<SupplyScope> supplies;
    RootSupply rootSupply;
    // Capabilities captured by the class or struct whose members are being checked (proposal 3.9).
    SupplyScope classCaptures;
};
} // namespace

namespace Cangjie::Sema {
void ReportCapabilityMissHandler::HandleMiss(const CapabilityDemand& demand)
{
    CJC_NULLPTR_CHECK(demand.demandSite);
    auto tyName = Ty::ToString(demand.exceptionTy);
    auto kind = asWarning ? DiagKindRefactor::sema_chexc_missing_capability_warn
                          : DiagKindRefactor::sema_chexc_missing_capability;
    auto builder = diag.DiagnoseRefactor(kind, *demand.demandSite, tyName, tyName);
    builder.AddMainHintArguments(demand.requiredBy);
}

void CheckCapabilities(
    TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg, CapabilityMissHandler& missHandler)
{
    CapabilityChecker(typeManager, importManager, missHandler).CheckPackage(pkg);
}
} // namespace Cangjie::Sema
