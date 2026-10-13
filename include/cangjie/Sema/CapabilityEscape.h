// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#ifndef CANGJIE_SEMA_CAPABILITYESCAPE_H
#define CANGJIE_SEMA_CAPABILITYESCAPE_H

#include "cangjie/Sema/CapabilityCheck.h"
#include <limits>
#include <map>
#include <optional>
#include <set>

namespace Cangjie::Sema {
constexpr size_t NO_ESCAPE_VALUE = std::numeric_limits<size_t>::max();

/** References remain live: a captured mutable cell is not a snapshot of its contents. */
struct EscapeValue {
    std::set<size_t> origins;
    std::set<size_t> locations;
    bool unknownStorage{false};
    std::vector<EscapeValue> components;
    bool operator==(const EscapeValue& other) const;
};

struct EscapeLocation {
    std::set<const AST::Node*> boundaries;
    bool shared{true}; // Only proven unaliased local slots permit strong updates.
    EscapeValue initialValue;
};

enum class EscapeOp { NOP, VALUE, COPY, MERGE, TUPLE, PROJECT, LOAD, STORE, CALL, EXIT };
struct EscapeInstruction {
    EscapeOp kind{EscapeOp::NOP};
    Ptr<const AST::Node> site{nullptr};
    size_t result{NO_ESCAPE_VALUE};
    std::vector<size_t> inputs;
    EscapeValue value; // Constants, captures, and supplied implicit capability arguments.
    size_t component{0};
    std::vector<size_t> componentPath;        // STORE: a directly represented local tuple component.
    std::vector<const AST::Node*> boundaries; // EXIT: only the boundaries actually crossed.
    std::vector<size_t> mutableInputs;        // Indices in inputs: effective non-Copyable local! views.
    std::vector<size_t> writtenInputs;        // Indices in inputs: potentially mutated reachable storage.
    bool independentResult{false};            // Requires a Modal proof, not merely an unrestricted result mode.
    bool referenceResult{false};
    size_t freshLocation{NO_ESCAPE_VALUE}; // Explicit construction only; factories are not fresh.
};
struct EscapeFlowNode {
    EscapeInstruction instruction;
    std::vector<size_t> successors;
};
struct EscapeGraph {
    std::vector<CapabilityOrigin> origins;
    std::vector<EscapeLocation> locations;
    size_t valueCount{0};
    std::vector<EscapeFlowNode> nodes;
    size_t entry{0};
};

enum class EscapeAnalysisStatus { DISABLED, INVALID, COMPLETE };
enum class EscapeViolationKind { STORE, RESULT, MUTABLE_CALL };
struct EscapeViolation {
    Ptr<const AST::Node> site{nullptr};
    EscapeViolationKind reason{EscapeViolationKind::STORE};
    CapabilityKind kind{CapabilityKind::UNTRACKED};
    CheckingLevel level{CheckingLevel::OFF};
    std::set<size_t> origins;
    bool conservative{false};
    std::map<size_t, Ptr<const AST::Node>> captureSites;
};
struct EscapeAnalysisResult {
    EscapeAnalysisStatus status{EscapeAnalysisStatus::INVALID};
    std::vector<EscapeViolation> violations;
};

/** Stateless, read-only analysis. All worklist and flow state is owned by Analyze. */
class CapabilityEscapeAnalyzer {
public:
    EscapeAnalysisResult Analyze(const EscapeGraph& graph, CheckingLevel exceptions, CheckingLevel effects) const;
};

/** Accepted Sema facts only. A candidate transaction owns and discards its own copy. */
struct CapabilityCaptureFacts {
    bool complete{false};
    std::map<const AST::Node*, EscapeValue> captures;
};

/**
 * A description of one typed expression/statement. Modal supplies semantic leaf operations and
 * their evaluation order; the shared builder supplies branches, loops and exit/cleanup edges.
 * Generated source-equivalent nodes must use one authoritative representation.
 */
struct EscapeNodeFacts {
    std::vector<const AST::Node*> evaluationOrder;
    std::vector<EscapeInstruction> operations;
    size_t result{NO_ESCAPE_VALUE};
    bool mayThrow{true};
    std::vector<EscapeInstruction> entryOperations; // For-in iterator initialization, once after iterable evaluation.
};
class ModalEscapeFacts {
public:
    virtual ~ModalEscapeFacts() = default;
    /// False in the non-Modal compiler. Must include capture-driven modes and resumption checking.
    virtual bool IsEnabled() const = 0;
    virtual bool IsComplete(const AST::FuncBody& body) const = 0;
    virtual CapabilityCaptureFacts Captures(const AST::FuncBody&) const
    {
        return {}; // An enabled provider must explicitly publish complete accepted captures.
    }
    /// Map generated helpers/clones to their authoritative source body (including ownerFunc).
    virtual const AST::FuncBody& SourceBody(const AST::FuncBody& body) const
    {
        return body;
    }
    /// Initialize origins, locations, and the finite set of expression result identifiers.
    virtual EscapeGraph CreateGraph(const AST::FuncBody& body) const = 0;
    /// Missing facts invalidate analysis; they never mean an independent, non-throwing value.
    virtual std::optional<EscapeNodeFacts> Describe(const AST::Node& node) const = 0;
    /// Typed resource-close operations in reverse acquisition order, for the initialized prefix.
    virtual std::vector<EscapeInstruction> Cleanup(const AST::TryExpr& expr, size_t initialized) const = 0;
    /// Selected lexical handlers; an empty list means invocation supplied by an enclosing caller.
    virtual std::vector<const AST::Handler*> ResolvedHandlers(const AST::PerformExpr&) const
    {
        return {};
    }
};

struct EscapeBodyResult {
    EscapeGraph graph;
    EscapeAnalysisResult analysis;
};
/// Shared compiler/tooling entry. Null Modal facts preserve the non-Modal compiler's behavior.
EscapeBodyResult CheckCapabilityEscapes(const AST::FuncBody& body, const CapabilityCaptureFacts& captures,
    const ModalEscapeFacts* modal, CheckingLevel exceptions, CheckingLevel effects);
void ReportCapabilityEscapes(const EscapeBodyResult& result, DiagnosticEngine& diag);
bool CheckPackageCapabilityEscapes(AST::Package& package, const ModalEscapeFacts* modal, CheckingLevel exceptions,
    CheckingLevel effects, DiagnosticEngine& diag);
} // namespace Cangjie::Sema
#endif
