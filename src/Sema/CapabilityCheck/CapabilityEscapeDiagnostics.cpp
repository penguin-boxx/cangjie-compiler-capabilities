// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "cangjie/AST/ASTCasting.h"
#include "cangjie/AST/Walker.h"
#include "cangjie/Basic/DiagnosticEngine.h"
#include "cangjie/Sema/CapabilityEscape.h"

namespace Cangjie::Sema {
void ReportCapabilityEscapes(const EscapeBodyResult& result, DiagnosticEngine& diag)
{
    if (result.analysis.status != EscapeAnalysisStatus::COMPLETE) {
        return;
    }
    for (const auto& violation : result.analysis.violations) {
        if (!violation.site) {
            continue;
        }
        auto kind = violation.level == CheckingLevel::WARN
            ? (violation.kind == CapabilityKind::EFFECT ? DiagKindRefactor::sema_effect_escape_warn
                                                        : DiagKindRefactor::sema_capability_escape_warn)
            : DiagKindRefactor::sema_capability_escape;
        std::string action;
        switch (violation.reason) {
            case EscapeViolationKind::STORE:
                action = "the destination can outlive the handler";
                break;
            case EscapeViolationKind::RESULT:
                action = "the result can retain a capability after its handler finishes";
                break;
            case EscapeViolationKind::MUTABLE_CALL:
                action = "the call can store a capability through an argument or receiver that outlives the handler";
                break;
            default:
                break;
        }
        auto builder = diag.DiagnoseRefactor(kind, *violation.site, action);
        builder.AddMainHintArguments(violation.conservative
                ? "the compiler cannot establish where this storage originated or what the call retains"
                : "keep this value and the storage receiving it within the supplying protected body");
        std::set<const AST::Node*> noted;
        for (auto id : violation.origins) {
            const auto& origin = result.graph.origins[id];
            if (origin.boundary && noted.insert(origin.boundary).second) {
                auto name = origin.type ? AST::Ty::ToString(origin.type) : "this capability";
                builder.AddNote(MakeRange(origin.boundary->begin, origin.boundary->end),
                    "the handler supplying " + name + " is introduced here");
            }
            auto capture = violation.captureSites.find(id);
            if (capture != violation.captureSites.end() && capture->second != violation.site &&
                noted.insert(capture->second).second) {
                builder.AddNote(
                    MakeRange(capture->second->begin, capture->second->end), "a value may retain this capability here");
            }
        }
    }
}

bool CheckPackageCapabilityEscapes(AST::Package& package, const ModalEscapeFacts* modal, CheckingLevel exceptions,
    CheckingLevel effects, DiagnosticEngine& diag)
{
    if (!modal || !modal->IsEnabled() || (exceptions == CheckingLevel::OFF && effects == CheckingLevel::OFF)) {
        return true;
    }
    auto errors = diag.GetErrorCount();
    std::set<const AST::FuncBody*> checked;
    AST::Walker(&package, [&](Ptr<AST::Node> node) {
        auto body = DynamicCast<AST::FuncBody*>(node);
        if (body && body->body) {
            auto& source = modal->SourceBody(*body);
            if (checked.insert(&source).second) {
                auto result = CheckCapabilityEscapes(source, modal->Captures(source), modal, exceptions, effects);
                if (result.analysis.status == EscapeAnalysisStatus::INVALID) {
                    diag.DiagnoseRefactor(DiagKindRefactor::sema_capability_escape_incomplete, source);
                } else {
                    ReportCapabilityEscapes(result, diag);
                }
            }
        }
        return AST::VisitAction::WALK_CHILDREN;
    }).Walk();
    return diag.GetErrorCount() == errors;
}
} // namespace Cangjie::Sema
