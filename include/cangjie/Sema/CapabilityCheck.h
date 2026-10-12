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

#include <functional>
#include <string>
#include <unordered_map>
#include <unordered_set>
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
 * inference uses a collecting handler that gathers residual demands instead.
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
 * Whether the declaration leaves its module by effective visibility. Nested functions do not
 * inherit the export status of their enclosing function; interface members are authoritative.
 */
bool IsExportedDecl(const AST::Decl& decl);
/**
 * Whether a source callable infers requirements from its own body. Module-local callables may
 * omit the clause; nested functions opt in with ellipsis. Finalizers, static initializers,
 * interface members and default-argument clones never infer an independent contract.
 * Incremental invalidation uses this same predicate.
 */
bool IsInferenceEligible(const AST::FuncDecl& fd);

enum class CapabilityKind { UNTRACKED, EXCEPTION, EFFECT };
/// Classify nominal types and bounded type parameters without scheduling or reporting.
CapabilityKind ClassifyCapability(TypeManager& typeManager, const ImportManager& importManager, Ptr<AST::Ty> ty);

/** Lexical ownership is independent of canonical list positions. */
struct CapabilityScope {
    std::vector<Ptr<AST::Ty>> types;
    Ptr<const AST::Node> owner;
};
struct CapabilityContext {
    std::vector<CapabilityScope> scopes;
    Ptr<const AST::FuncDecl> inferenceOwner{nullptr};
};
enum class CapabilityResolutionKind { SUPPLIED, RESIDUAL, MISSING };
struct CapabilityResolution {
    CapabilityResolutionKind kind;
    CapabilityDemand demand;
    Ptr<const AST::Node> owner;
    Ptr<AST::Ty> supplyingType{nullptr};
};
/// Pure resolution: the caller owns accumulation and diagnostic delivery.
CapabilityResolution ResolveCapability(
    TypeManager& typeManager, const CapabilityContext& context, const CapabilityDemand& demand);
using EnsureCapabilityContract = std::function<bool(AST::FuncDecl&, const AST::Node&)>;
/// Collect from one accepted typed declaration. The callback completes implicit operations.
std::vector<Ptr<AST::Ty>> CollectCapabilityRequirements(TypeManager& typeManager, const ImportManager& importManager,
    AST::FuncDecl& decl, const EnsureCapabilityContract& ensure);
void CheckCompletedOverrides(TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg,
    DiagnosticEngine& diag, bool asWarning);
void CheckCapabilities(TypeManager& typeManager, const ImportManager& importManager, AST::Package& pkg,
    CapabilityMissHandler& missHandler, DiagnosticEngine& diag);

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
