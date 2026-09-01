// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

/**
 * @file
 *
 * This file declares the checked-exception capability checking pass (experimental, behind
 * '--experimental --enable-checked-exceptions').
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
    /// Effects: true when the demanded type is a Command subtype. Decides the
    /// diagnostic's capability name -- 'Handler<C>' rather than 'CanThrow<E>' -- and exclusion
    /// from inference, which never infers effect requirements.
    bool isEffect{false};
};

/**
 * Miss-handler seam: the demand/supply walker is parameterized over what happens
 * to unsatisfied demands. The reporting handler below diagnoses each miss; capability-parameter
 * inference will later plug in a collecting handler that gathers residual demands instead.
 */
class CapabilityMissHandler {
public:
    virtual ~CapabilityMissHandler() = default;
    virtual void HandleMiss(const CapabilityDemand& demand) = 0;
    /// Called once the package has been walked, for handlers that batch what they collected.
    virtual void Finish()
    {
    }
};

/**
 * Reporting miss-handler: diagnoses each miss. Severity follows
 * '--enable-checked-exceptions[=error|warn]'; the warning variant belongs to the 'chexc'
 * warn group.
 */
class ReportCapabilityMissHandler : public CapabilityMissHandler {
public:
    /**
     * @p asWarning downgrades exception misses to warnings (the 'warn' checking level).
     * @p reportExceptions is false when exception checking is off: the clauses still parse and
     * still mean what they say, but impose no obligations, while effect requirements are reported
     * whenever the effect-handler feature is on -- and always as errors, since an unhandled
     * 'perform' fails at run time and has no migration level.
     */
    ReportCapabilityMissHandler(DiagnosticEngine& diag, bool asWarning, bool reportExceptions = true)
        : diag(diag), asWarning(asWarning), reportExceptions(reportExceptions)
    {
    }
    ~ReportCapabilityMissHandler() override
    {
        Finish();
    }
    void HandleMiss(const CapabilityDemand& demand) override;
    /**
     * Emits one diagnostic per requirement site, naming every capability missing there. The
     * compiler's diagnostic set deduplicates by position and severity alone, so several
     * diagnostics at one site collapse into the first -- a call missing three capabilities would
     * report one, and the next only after that one is fixed. Batching keeps them all visible,
     * which is what burning warnings down during migration needs.
     */
    void Finish() override;

private:
    DiagnosticEngine& diag;
    bool asWarning;
    bool reportExceptions;
    /// Misses in the order they were found, grouped by site when they are reported.
    std::vector<CapabilityDemand> pending;
};

/**
 * True when @p decl leaves its module, so its capability list is authoritative and never inferred.
 * The test is *effective* visibility -- the narrowest of the declaration's own modifier and those of
 * its enclosing declarations -- plus interface membership, an interface member being a public
 * contract whether or not the modifier is written.
 */
/**
 * Checked exceptions: whether @p fd takes its capability list from its own body -- it has a body,
 * does not leave the module by effective visibility, is not a finalizer or an interface member,
 * and either carries no 'throws' clause or one ending in '...'. The single definition: the
 * incremental frontend asks the same question and must get the same answer, or a body edit can
 * leave callers checked against a stale contract.
 */
bool IsInferenceEligible(const AST::FuncDecl& fd);
bool IsExportedDecl(const AST::Decl& decl);

/**
 * Capability lists inferred for declarations without an authoritative clause.
 * Kept beside the AST rather than written into declaration types: the checking pass stays a
 * pure check, and call sites resolve a callee's list through this map.
 */
using InferredCapabilities = std::unordered_map<Ptr<AST::FuncDecl>, std::vector<Ptr<AST::Ty>>>;

/**
 * Infer capability parameter lists for the inference-eligible declarations of @p pkg
 *: the least solution of the monotone equations over each strongly connected
 * component of the intra-package call graph, computed bottom-up. Declarations carrying an
 * authoritative clause are constants; a clause ending in `...` contributes its entries and
 * still takes part. Polymorphic recursion is rejected with a diagnostic.
 */
InferredCapabilities InferCapabilities(
    TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg, DiagnosticEngine& diag);

/**
 * Complete the types of the declarations covered by @p inferred (capability
 * parameters, then clause components of types, then capability arguments). Each declaration's
 * functional type is re-interned with its inferred entries, so the declaration's own type is the
 * single source of its capability list. Expression types are deliberately NOT completed: they
 * were formed during type check, before inference ran, and re-typing them would double-charge
 * every call site — call sites read the map instead.
 */
void CompleteInferredCapabilityTypes(TypeManager& typeManager, const InferredCapabilities& inferred);

/**
 * Checked exceptions: finish the capability component of the EXPRESSION types that name an
 * inferred declaration — a reference used as a value, and the binding it initializes. Those types
 * were formed during type check, while the list was still empty, so without this a call through
 * such a value demands nothing at all. Run after 'CompleteInferredCapabilityTypes'.
 */
void CompleteInferredCapabilityExprTypes(
    TypeManager& typeManager, const InferredCapabilities& inferred, AST::Package& pkg);

/**
 * Checked exceptions: re-check the capability-sensitive judgements type check made while the
 * inferred lists were empty — assignment, initialization against a declared type, argument
 * passing and 'return'. Only the capability component can have changed, so a failure here is
 * always about capabilities. Overload resolution is never replayed: it does not consult lists.
 * @p asWarning follows the checking level, as for every other capability obligation.
 */
void ReplayCapabilitySubtyping(TypeManager& typeManager, AST::Package& pkg, DiagnosticEngine& diag, bool asWarning);

/**
 * Checked exceptions: report every inferred list that requires more than the declaration it
 * overrides or implements. Written lists are compared during type check; an inferred one cannot be,
 * because inference runs after it -- so the override pairs recorded then are consumed here.
 */
void CheckInferredOverrides(
    TypeManager& typeManager, const InferredCapabilities& inferred, DiagnosticEngine& diag, bool asWarning);

/**
 * Run capability argument checking over every callable body and initializer of @p pkg on the
 * typed AST (after sema type check, before desugar destroys 'TryExpr' structure). The pass
 * never mutates types; every unsatisfied demand is passed to @p missHandler. @p inferred
 * supplies the lists computed by InferCapabilities: they act as the declared clause of their
 * declaration and are demanded at its call sites.
 */
void CheckCapabilities(TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg,
    CapabilityMissHandler& missHandler, const InferredCapabilities& inferred, DiagnosticEngine& diag);

/**
 * The capability list of @p decl's 'captures' clause, with capability list aliases
 * already spliced in; empty for a declaration that captures nothing.
 *
 * Exposed here for package serialization, which must write the clause into the .cjo so that
 * construction sites in other packages demand it. The elaborated clause lives
 * on the AST, which serialization cannot reach through the Sema-private headers.
 */
std::vector<Ptr<AST::Ty>> GetCapturesCapTys(const AST::Decl& decl);
} // namespace Sema
} // namespace Cangjie

#endif // CANGJIE_SEMA_CAPABILITYCHECK_H
