// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

/**
 * @file
 *
 * This file declares the checked-exception capability checking pass (experimental, behind
 * '--experimental --enable-checked-exceptions'; proposal sections 3.3 and 3.5).
 */

#ifndef CANGJIE_SEMA_CAPABILITYCHECK_H
#define CANGJIE_SEMA_CAPABILITYCHECK_H

#include <string>
#include <unordered_map>
#include <vector>

#include "cangjie/AST/Node.h"

namespace Cangjie {
class DiagnosticEngine;
class TypeManager;
class ImportManager;

namespace Sema {
/**
 * A capability demand that no active capability scope satisfies: the demanded exception type
 * (the corresponding capability has type 'CanThrow<exceptionTy>'), the demanding expression,
 * and a description of the demanding construct for diagnostics.
 */
struct CapabilityDemand {
    Ptr<AST::Ty> exceptionTy;
    Ptr<const AST::Node> demandSite;
    std::string requiredBy;
};

/**
 * Miss-handler seam (proposal 6.3): the demand/supply walker is parameterized over what happens
 * to unsatisfied demands. The reporting handler below diagnoses each miss; capability-parameter
 * inference will later plug in a collecting handler that gathers residual demands instead.
 */
class CapabilityMissHandler {
public:
    virtual ~CapabilityMissHandler() = default;
    virtual void HandleMiss(const CapabilityDemand& demand) = 0;
};

/**
 * Reporting miss-handler: diagnoses each miss with the proposal's wording. Severity follows
 * '--enable-checked-exceptions[=error|warn]'; the warning variant belongs to the 'chexc'
 * warn group.
 */
class ReportCapabilityMissHandler : public CapabilityMissHandler {
public:
    ReportCapabilityMissHandler(DiagnosticEngine& diag, bool asWarning) : diag(diag), asWarning(asWarning)
    {
    }
    void HandleMiss(const CapabilityDemand& demand) override;

private:
    DiagnosticEngine& diag;
    bool asWarning;
};

/**
 * Capability lists inferred for declarations without an authoritative clause (proposal 6.3).
 * Kept beside the AST rather than written into declaration types: the checking pass stays a
 * pure check, and call sites resolve a callee's list through this map.
 */
using InferredCapabilities = std::unordered_map<Ptr<const AST::Decl>, std::vector<Ptr<AST::Ty>>>;

/**
 * Infer capability parameter lists for the inference-eligible declarations of @p pkg
 * (proposal 6.3): the least solution of the monotone equations over each strongly connected
 * component of the intra-package call graph, computed bottom-up. Declarations carrying an
 * authoritative clause are constants; a clause ending in `...` contributes its entries and
 * still takes part. Polymorphic recursion is rejected with a diagnostic.
 */
InferredCapabilities InferCapabilities(
    TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg, DiagnosticEngine& diag);

/**
 * Run capability argument checking over every callable body and initializer of @p pkg on the
 * typed AST (after sema type check, before desugar destroys 'TryExpr' structure). The pass
 * never mutates types; every unsatisfied demand is passed to @p missHandler. @p inferred
 * supplies the lists computed by InferCapabilities: they act as the declared clause of their
 * declaration and are demanded at its call sites.
 */
void CheckCapabilities(TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg,
    CapabilityMissHandler& missHandler, const InferredCapabilities& inferred = {});
} // namespace Sema
} // namespace Cangjie

#endif // CANGJIE_SEMA_CAPABILITYCHECK_H
