// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "TypeCheckerImpl.h"

#include "Diags.h"
#include "TypeCheckUtil.h"

#include "cangjie/AST/Walker.h"
#include "cangjie/Utils/ConstantsUtils.h"

using namespace Cangjie;
using namespace Sema;

Ptr<Ty> TypeChecker::TypeCheckerImpl::CastTargetTy(Type& target)
{
    // Checked exceptions: a runtime type test sees the erased shape, so nothing verifies a
    // capability list -- reading a function type in a cast target as clause-free would launder a
    // '() throws E -> R' value into a '() -> R' one. The base design therefore rejects any target
    // containing a function type, in any position; relaxations that make such casts usable are an
    // extension. A parameter-typed target ('x as Box<T>') is accepted: rejecting it would break
    // ordinary generic code, and an instantiation with a function type is an unchecked boundary.
    // Off with the feature, the written type is the type.
    auto targetTy = target.GetTy();
    if (!ci->invocation.globalOptions.enableChexc || !Ty::IsTyCorrect(targetTy)) {
        return targetTy;
    }
    if (TypeCheckUtil::ContainsFuncTy(targetTy)) {
        diag.DiagnoseRefactor(DiagKindRefactor::sema_chexc_cast_target_func, target, Ty::ToString(targetTy));
    }
    return targetTy;
}

Ptr<Ty> TypeChecker::TypeCheckerImpl::SynIsExpr(ASTContext& ctx, IsExpr& ie)
{
    if (Ty::IsTyCorrect(Synthesize({ctx, SynPos::EXPR_ARG}, ie.leftExpr.get())) &&
        Ty::IsTyCorrect(Synthesize({ctx, SynPos::NONE}, ie.isType.get())) && ReplaceIdealTy(*ie.leftExpr)) {
        ie.SetTy(TypeManager::GetPrimitiveTy(TypeKind::TYPE_BOOLEAN));
    } else {
        ie.SetTy(TypeManager::GetInvalidTy());
    }
    return ie.GetTy();
}

bool TypeChecker::TypeCheckerImpl::ChkIsExpr(ASTContext& ctx, Ty& target, IsExpr& ie)
{
    // Always type checking the expression even if the target type mismatches.
    auto ty = SynIsExpr(ctx, ie);
    if (!Ty::IsTyCorrect(ty)) {
        return false;
    }
    bool isWellTyped = ty->IsBoolean();

    auto boolTy = TypeManager::GetPrimitiveTy(TypeKind::TYPE_BOOLEAN);
    if (!typeManager.IsLitBoxableType(boolTy, &target)) {
        DiagMismatchedTypesWithFoundTy(diag, ie, target, *boolTy);
        isWellTyped = false;
    }

    ie.SetTy(isWellTyped ? ie.GetTy() : TypeManager::GetInvalidTy());
    return isWellTyped;
}

Ptr<Ty> TypeChecker::TypeCheckerImpl::SynAsExpr(ASTContext& ctx, AsExpr& ae)
{
    if (Ty::IsTyCorrect(Synthesize({ctx, SynPos::EXPR_ARG}, ae.leftExpr.get())) &&
        Ty::IsTyCorrect(Synthesize({ctx, SynPos::NONE}, ae.asType.get())) && ReplaceIdealTy(*ae.leftExpr)) {
        auto optionDecl = RawStaticCast<EnumDecl*>(importManager.GetCoreDecl("Option"));
        if (optionDecl) {
            // The runtime test still uses the written type -- capability lists are erased, so both
            // read the same shape -- while the value handed back is read pessimistically.
            ae.SetTy(typeManager.GetEnumTy(*optionDecl, {CastTargetTy(*ae.asType)}));
        } else {
            diag.Diagnose(ae, DiagKind::sema_no_core_object);
            ae.SetTy(TypeManager::GetInvalidTy());
        }
    } else {
        ae.SetTy(TypeManager::GetInvalidTy());
    }
    return ae.GetTy();
}

bool TypeChecker::TypeCheckerImpl::ChkAsExpr(ASTContext& ctx, Ty& target, AsExpr& ae)
{
    if (!Ty::IsTyCorrect(SynAsExpr(ctx, ae))) {
        return false;
    }
    if (!CheckOptionBox(target, *ae.GetTy())) {
        DiagMismatchedTypes(diag, ae, target);
        ae.SetTy(TypeManager::GetInvalidTy());
        return false;
    }
    return true;
}
