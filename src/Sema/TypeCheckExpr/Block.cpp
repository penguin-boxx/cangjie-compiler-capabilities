// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "TypeCheckerImpl.h"

#include "DiagSuppressor.h"
#include "Diags.h"

using namespace Cangjie;
using namespace Sema;

bool TypeChecker::TypeCheckerImpl::SynthesizeAndReplaceIdealTy(const CheckerContext& ctx, Node& node)
{
    // Call `Synthesize` on declares containing invalid types may return valid types.
    // Therefore, we need to know if there are any errors during the inference process.
    auto ds = DiagSuppressor(diag);
    bool valid = Ty::IsTyCorrect(Synthesize(ctx, &node)) && ReplaceIdealTy(node) && !ds.HasError();
    ds.ReportDiag();
    return valid;
}

Ptr<Ty> TypeChecker::TypeCheckerImpl::SynBlock(const CheckerContext& ctx, Block& b)
{
    if (b.body.empty()) {
        b.SetTy(TypeManager::GetPrimitiveTy(TypeKind::TYPE_UNIT));
    } else {
        bool existInvalid = false;
        for (size_t i = 0; i < b.body.size(); i++) {
            auto& node = b.body[i];
            auto exprPos =
                i == b.body.size() - 1 && ctx.SynthPos() != SynPos::UNUSED ? SynPos::IMPLICIT_RETURN : SynPos::UNUSED;
            existInvalid = !SynthesizeAndReplaceIdealTy(ctx.With(exprPos), *node) || existInvalid;
        }
        Ptr<Node> lastNode = b.body[b.body.size() - 1].get();
        CJC_ASSERT(lastNode != nullptr);
        if (existInvalid) {
            b.SetTy(TypeManager::GetInvalidTy());
        } else if (lastNode->IsDecl()) {
            b.SetTy(TypeManager::GetPrimitiveTy(TypeKind::TYPE_UNIT));
        } else {
            b.SetTy(lastNode->GetTy());
        }
    }
    return b.GetTy();
}

bool TypeChecker::TypeCheckerImpl::ChkBlock(ASTContext& ctx, Ty& target, Block& b)
{
    Ptr<Ty> unitTy = TypeManager::GetPrimitiveTy(TypeKind::TYPE_UNIT);
    if (b.body.empty()) {
        b.SetTy(unitTy);
        // NOTE: This function may return false, the caller should handle diagnostics.
        // Only unsafe block is allowed to exist on its own, and needs to diagnose here.
        auto ret = CheckCapabilitySubtype(b.GetTy(), &target, b);
        if (!ret && b.TestAttr(Attribute::UNSAFE)) {
            auto builder = diag.DiagnoseRefactor(DiagKindRefactor::sema_mismatched_types, b);
            builder.AddMainHintArguments(target.String(), b.GetTy()->String());
        }
        return ret;
    }
    // Synthesize the first N - 1 nodes.
    bool isWellTyped = true;
    for (size_t i = 0; i < b.body.size() - 1; i++) {
        CJC_ASSERT(b.body[i]);
        isWellTyped = SynthesizeAndReplaceIdealTy({ctx, SynPos::UNUSED}, *b.body[i]) && isWellTyped;
    }
    Ptr<Node> lastNode = b.body[b.body.size() - 1].get();
    CJC_ASSERT(lastNode != nullptr);
    // If lastNode is compiler added return, just check inner expr.
    if (!b.TestAttr(AST::Attribute::COMPILER_ADD) && lastNode->TestAttr(AST::Attribute::COMPILER_ADD) &&
        lastNode->astKind == ASTKind::RETURN_EXPR) {
        lastNode = StaticCast<ReturnExpr>(lastNode)->expr.get();
    }
    if (lastNode->IsDecl()) {
        bool typeMatched = typeManager.IsSubtype(unitTy, &target);
        isWellTyped =
            SynthesizeAndReplaceIdealTy({ctx, SynPos::IMPLICIT_RETURN}, *lastNode) && typeMatched && isWellTyped;
        if (isWellTyped) {
            b.SetTy(unitTy);
            return true;
        } else {
            b.SetTy(TypeManager::GetInvalidTy());
            if (!typeMatched) {
                DiagMismatchedTypesWithFoundTy(
                    diag, *lastNode, target, *unitTy, "definitions and declarations are always of type 'Unit'");
            }
            return false;
        }
    } else {
        isWellTyped = Check(ctx, &target, lastNode) && isWellTyped;
        if (isWellTyped) {
            b.SetTy(lastNode->GetTy());
            return true;
        }
        b.SetTy(TypeManager::GetInvalidTy());
        return false;
    }
}
