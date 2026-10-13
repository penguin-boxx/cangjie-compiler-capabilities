// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "cangjie/Sema/CapabilityEscape.h"
#include "cangjie/Basic/DiagnosticEngine.h"
#include "gtest/gtest.h"

using namespace Cangjie;
using namespace Cangjie::AST;
using namespace Cangjie::Sema;

namespace {
class CapabilityEscapeTest : public testing::Test {
protected:
    TryExpr outer;
    TryExpr inner;
    RefExpr site;
    EscapeGraph graph;

    void SetUp() override
    {
        graph.origins = {{CapabilityKind::EXCEPTION, nullptr, &outer, &outer, CapabilitySupplyKind::PROTECTED_BODY},
            {CapabilityKind::EFFECT, nullptr, &inner, &inner, CapabilitySupplyKind::PROTECTED_BODY}};
        // Local slots, shared/captured cells, heap storage, and external storage.
        graph.locations = {{{&outer}, false}, {{&outer, &inner}, false}, {{&outer}, true}, {{}, true}};
        graph.valueCount = 16;
    }

    size_t Emit(EscapeOp kind, size_t result = NO_ESCAPE_VALUE, std::vector<size_t> inputs = {})
    {
        EscapeInstruction op;
        op.kind = kind;
        op.site = &site;
        op.result = result;
        op.inputs = std::move(inputs);
        auto id = graph.nodes.size();
        if (id != 0) {
            graph.nodes.back().successors.push_back(id);
        }
        graph.nodes.push_back({op, {}});
        return id;
    }

    void Value(size_t result, std::set<size_t> origins = {}, std::set<size_t> locations = {}, bool unknown = false)
    {
        Emit(EscapeOp::VALUE, result);
        graph.nodes.back().instruction.value = {std::move(origins), std::move(locations), unknown, {}};
    }

    void Store(size_t value, size_t address)
    {
        Emit(EscapeOp::STORE, NO_ESCAPE_VALUE, {value, address});
    }

    void Exit(size_t value, const Node* boundary)
    {
        Emit(EscapeOp::EXIT, NO_ESCAPE_VALUE, {value});
        graph.nodes.back().instruction.boundaries = {boundary};
    }

    EscapeAnalysisResult Run(
        CheckingLevel exceptions = CheckingLevel::ERROR, CheckingLevel effects = CheckingLevel::ERROR)
    {
        return CapabilityEscapeAnalyzer().Analyze(graph, exceptions, effects);
    }
};

TEST_F(CapabilityEscapeTest, LocalStoreIsLegalButOuterStoreIsNot)
{
    Value(0, {0});
    Value(1, {}, {0});
    Store(0, 1);
    EXPECT_TRUE(Run().violations.empty());
    Value(2, {}, {3});
    Store(0, 2);
    auto result = Run();
    ASSERT_EQ(result.status, EscapeAnalysisStatus::COMPLETE);
    ASSERT_EQ(result.violations.size(), 1);
    EXPECT_EQ(result.violations[0].reason, EscapeViolationKind::STORE);
    EXPECT_EQ(result.violations[0].origins, std::set<size_t>{0});
}

TEST_F(CapabilityEscapeTest, AliasDeclarationDoesNotChangeStorageOrigin)
{
    Value(0, {0});
    Value(1, {}, {3});
    Emit(EscapeOp::COPY, 2, {1});
    Store(0, 2);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, UnknownStorageIsConservative)
{
    Value(0, {0});
    Value(1, {}, {}, true);
    Store(0, 1);
    auto result = Run();
    ASSERT_EQ(result.violations.size(), 1);
    EXPECT_TRUE(result.violations[0].conservative);
}

TEST_F(CapabilityEscapeTest, StrongLocalOverwriteClearsDependency)
{
    Value(0, {0});
    Value(1, {}, {0});
    Store(0, 1);
    Value(2);
    Store(2, 1);
    Emit(EscapeOp::LOAD, 3, {1});
    Exit(3, &outer);
    EXPECT_TRUE(Run().violations.empty());
}

TEST_F(CapabilityEscapeTest, SharedCellOverwriteDoesNotForgetAliasedContents)
{
    Value(0, {0});
    Value(1, {}, {2});
    Store(0, 1);
    Value(2);
    Store(2, 1);
    Emit(EscapeOp::LOAD, 3, {1});
    Exit(3, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, ClosureSeesLaterCapturedCellWrite)
{
    Value(0, {}, {2}); // Closure holds the captured cell, not a snapshot of its contents.
    Value(1, {0});
    Value(2, {}, {2});
    Store(1, 2);
    Exit(0, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, TupleProjectionDoesNotTaintIndependentComponent)
{
    Value(0, {0});
    Value(1);
    Emit(EscapeOp::TUPLE, 2, {0, 1});
    Emit(EscapeOp::PROJECT, 3, {2});
    graph.nodes.back().instruction.component = 1;
    Exit(3, &outer);
    EXPECT_TRUE(Run().violations.empty());
    Emit(EscapeOp::PROJECT, 4, {2});
    graph.nodes.back().instruction.component = 0;
    Exit(4, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, OuterOriginCanCrossInnerBoundary)
{
    Value(0, {0});
    Exit(0, &inner);
    EXPECT_TRUE(Run().violations.empty());
    Exit(0, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, InnerOriginCannotBeStoredInOuterTry)
{
    Value(0, {1});
    Value(1, {}, {0});
    Store(0, 1);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, IdentityCallAndNominalCastPreserveDependencies)
{
    Value(0, {0});
    Emit(EscapeOp::CALL, 1, {0});
    Emit(EscapeOp::COPY, 2, {1});
    Exit(2, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, IndependentCallResultMayLeaveTry)
{
    Value(0, {0});
    Emit(EscapeOp::CALL, 1, {0});
    graph.nodes.back().instruction.independentResult = true;
    Exit(1, &outer);
    EXPECT_TRUE(Run().violations.empty());
}

TEST_F(CapabilityEscapeTest, ImplicitCapabilityArgumentsTaintCallResult)
{
    Emit(EscapeOp::CALL, 0);
    graph.nodes.back().instruction.value.origins = {0};
    Exit(0, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, MutableCallRejectsExternalReceiverEvenWithIndependentResult)
{
    Value(0, {0});
    Value(1, {}, {3});
    Emit(EscapeOp::CALL, 2, {0, 1});
    graph.nodes.back().instruction.mutableInputs = {1};
    graph.nodes.back().instruction.independentResult = true;
    auto result = Run();
    ASSERT_EQ(result.violations.size(), 1);
    EXPECT_EQ(result.violations[0].reason, EscapeViolationKind::MUTABLE_CALL);
}

TEST_F(CapabilityEscapeTest, MutableCallAcceptsFreshInternalReceiver)
{
    Value(0, {0});
    Value(1, {}, {2});
    Emit(EscapeOp::CALL, 2, {0, 1});
    graph.nodes.back().instruction.mutableInputs = {1};
    EXPECT_TRUE(Run().violations.empty());
}

TEST_F(CapabilityEscapeTest, CallsCanMutateReachableHeap)
{
    Value(0, {0});
    Value(1, {}, {2});
    Emit(EscapeOp::CALL, 2, {0, 1});
    graph.nodes.back().instruction.writtenInputs = {1};
    graph.nodes.back().instruction.independentResult = true;
    Exit(1, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, FactoryResultsHaveUnknownStorageButConstructorsAreFresh)
{
    Value(0, {0});
    Emit(EscapeOp::CALL, 1);
    graph.nodes.back().instruction.referenceResult = true;
    Emit(EscapeOp::CALL, 2, {0, 1});
    graph.nodes.back().instruction.mutableInputs = {1};
    EXPECT_EQ(Run().violations.size(), 1);
    graph.nodes[1].instruction.freshLocation = 2;
    EXPECT_TRUE(Run().violations.empty());
}

TEST_F(CapabilityEscapeTest, BranchJoinRetainsEitherDependency)
{
    Value(0, {}, {0});
    Value(1, {0});
    Value(2);
    auto branch = Emit(EscapeOp::NOP);
    auto left = Emit(EscapeOp::STORE, NO_ESCAPE_VALUE, {1, 0});
    auto right = Emit(EscapeOp::STORE, NO_ESCAPE_VALUE, {2, 0});
    auto join = Emit(EscapeOp::LOAD, 3, {0});
    Exit(3, &outer);
    graph.nodes[branch].successors = {left, right};
    graph.nodes[left].successors = {join};
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, LoopBackedgeReachesFixedPoint)
{
    Value(0, {}, {0});
    Value(1, {0});
    auto header = Emit(EscapeOp::LOAD, 2, {0});
    auto body = Emit(EscapeOp::STORE, NO_ESCAPE_VALUE, {1, 0});
    Exit(2, &outer);
    graph.nodes[header].successors = {body, body + 1};
    graph.nodes[body].successors = {header};
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, UnreachableEscapeDoesNotReport)
{
    Value(0, {0});
    Exit(0, &outer);
    graph.nodes[0].successors.clear();
    EXPECT_TRUE(Run().violations.empty());
}

TEST_F(CapabilityEscapeTest, DisabledAxesDoNotIntroduceOrigins)
{
    Value(0, {0, 1});
    Emit(EscapeOp::EXIT, NO_ESCAPE_VALUE, {0});
    graph.nodes.back().instruction.boundaries = {&outer, &inner};
    auto result = Run(CheckingLevel::OFF, CheckingLevel::WARN);
    ASSERT_EQ(result.violations.size(), 1);
    EXPECT_EQ(result.violations[0].kind, CapabilityKind::EFFECT);
    EXPECT_EQ(result.violations[0].level, CheckingLevel::WARN);
    EXPECT_TRUE(Run(CheckingLevel::OFF, CheckingLevel::OFF).violations.empty());
}

TEST_F(CapabilityEscapeTest, SeparateKindsAreBatchedAtSameSite)
{
    Value(0, {0, 1});
    Value(1, {}, {3});
    Store(0, 1);
    auto result = Run(CheckingLevel::WARN, CheckingLevel::ERROR);
    ASSERT_EQ(result.violations.size(), 2);
    EXPECT_NE(result.violations[0].kind, result.violations[1].kind);
}

TEST_F(CapabilityEscapeTest, ClauseParametersAreNotLocalHandlerOrigins)
{
    graph.origins[0].boundary = nullptr;
    graph.origins[0].supplyKind = CapabilitySupplyKind::CLAUSE_PARAMETER;
    Value(0, {0});
    Exit(0, &outer);
    EXPECT_TRUE(Run().violations.empty());
}

TEST_F(CapabilityEscapeTest, MalformedFactsFailInsteadOfPublishingEmptySuccess)
{
    Value(0, {99});
    EXPECT_EQ(Run().status, EscapeAnalysisStatus::INVALID);
    graph.nodes[0].instruction.value.origins.clear();
    graph.nodes[0].successors = {99};
    EXPECT_EQ(Run().status, EscapeAnalysisStatus::INVALID);
}

TEST_F(CapabilityEscapeTest, ReusingAnalyzerDoesNotLeakState)
{
    Value(0, {0});
    Exit(0, &outer);
    CapabilityEscapeAnalyzer analyzer;
    EXPECT_EQ(analyzer.Analyze(graph, CheckingLevel::ERROR, CheckingLevel::ERROR).violations.size(), 1);
    graph.nodes[0].instruction.value.origins.clear();
    EXPECT_TRUE(analyzer.Analyze(graph, CheckingLevel::ERROR, CheckingLevel::ERROR).violations.empty());
}

class TestModalFacts : public ModalEscapeFacts {
public:
    bool enabled{true};
    bool complete{true};
    EscapeGraph graph;
    std::map<const Node*, EscapeNodeFacts> nodes;
    std::vector<EscapeInstruction> cleanup;
    std::map<const PerformExpr*, std::vector<const Handler*>> handlers;
    bool IsEnabled() const override
    {
        return enabled;
    }
    bool IsComplete(const FuncBody&) const override
    {
        return complete;
    }
    EscapeGraph CreateGraph(const FuncBody&) const override
    {
        return graph;
    }
    std::optional<EscapeNodeFacts> Describe(const Node& node) const override
    {
        auto it = nodes.find(&node);
        if (it != nodes.end()) {
            return it->second;
        }
        if (node.astKind == ASTKind::BLOCK || node.astKind == ASTKind::FUNC_BODY || node.astKind == ASTKind::TRY_EXPR ||
            node.astKind == ASTKind::IF_EXPR || node.astKind == ASTKind::RETURN_EXPR ||
            node.astKind == ASTKind::WHILE_EXPR || node.astKind == ASTKind::JUMP_EXPR) {
            EscapeNodeFacts facts;
            facts.mayThrow = false;
            return facts;
        }
        return {};
    }
    std::vector<EscapeInstruction> Cleanup(const TryExpr&, size_t initialized) const override
    {
        return initialized == 0 ? std::vector<EscapeInstruction>{} : cleanup;
    }
    std::vector<const Handler*> ResolvedHandlers(const PerformExpr& expr) const override
    {
        auto found = handlers.find(&expr);
        return found == handlers.end() ? std::vector<const Handler*>{} : found->second;
    }
    void Literal(const Node& node, size_t result, EscapeValue value = {})
    {
        EscapeInstruction op;
        op.kind = EscapeOp::VALUE;
        op.site = &node;
        op.result = result;
        op.value = std::move(value);
        nodes[&node] = {{}, {op}, result, false};
    }
};

TEST_F(CapabilityEscapeTest, NonModalEntryDoesNotInspectIncompleteFacts)
{
    FuncBody body;
    CapabilityCaptureFacts captures;
    auto result = CheckCapabilityEscapes(body, captures, nullptr, CheckingLevel::ERROR, CheckingLevel::ERROR);
    EXPECT_EQ(result.analysis.status, EscapeAnalysisStatus::DISABLED);
    TestModalFacts modal;
    modal.enabled = false;
    result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    EXPECT_EQ(result.analysis.status, EscapeAnalysisStatus::DISABLED);
    modal.enabled = true;
    result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    EXPECT_EQ(result.analysis.status, EscapeAnalysisStatus::INVALID);
}

TEST_F(CapabilityEscapeTest, AstTryResultCannotCarryItsOwnOrigin)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto handler = MakeOwned<TryExpr>();
    auto handlerPtr = handler.get();
    handler->tryBlock = MakeOwned<Block>();
    auto leaf = MakeOwned<RefExpr>();
    TestModalFacts modal;
    modal.graph = graph;
    modal.graph.origins[0].owner = handlerPtr;
    modal.graph.origins[0].boundary = handlerPtr;
    modal.Literal(*leaf, 0, {{0}, {}, false, {}});
    modal.nodes[handler->tryBlock.get()].result = 0;
    modal.nodes[handler->tryBlock.get()].mayThrow = false;
    handler->tryBlock->body.push_back(std::move(leaf));
    body.body->body.push_back(std::move(handler));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    ASSERT_EQ(result.analysis.violations.size(), 1);
    EXPECT_EQ(result.analysis.violations[0].reason, EscapeViolationKind::RESULT);
}

TEST_F(CapabilityEscapeTest, AstReturnCrossesProtectedBoundary)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto handler = MakeOwned<TryExpr>();
    auto handlerPtr = handler.get();
    handler->tryBlock = MakeOwned<Block>();
    auto ret = MakeOwned<ReturnExpr>();
    ret->expr = MakeOwned<RefExpr>();
    ret->refFuncBody = &body;
    TestModalFacts modal;
    modal.graph = graph;
    modal.graph.origins[0].boundary = handlerPtr;
    modal.Literal(*ret->expr, 0, {{0}, {}, false, {}});
    handler->tryBlock->body.push_back(std::move(ret));
    body.body->body.push_back(std::move(handler));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, AstReturnRunsFinallyAndSkipsFollowingStatements)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto handler = MakeOwned<TryExpr>();
    handler->tryBlock = MakeOwned<Block>();
    auto ret = MakeOwned<ReturnExpr>();
    ret->expr = MakeOwned<RefExpr>();
    ret->refFuncBody = &body;
    TestModalFacts modal;
    modal.graph = graph;
    modal.Literal(*ret->expr, 0);
    handler->tryBlock->body.push_back(std::move(ret));
    handler->finallyBlock = MakeOwned<Block>();
    auto finalValue = MakeOwned<RefExpr>();
    modal.Literal(*finalValue, 1, {{0}, {}, false, {}});
    auto finalExit = MakeOwned<RefExpr>();
    EscapeInstruction exit;
    exit.kind = EscapeOp::EXIT;
    exit.site = finalExit.get();
    exit.inputs = {1};
    exit.boundaries = {&outer};
    modal.nodes[finalExit.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    handler->finallyBlock->body.push_back(std::move(finalValue));
    handler->finallyBlock->body.push_back(std::move(finalExit));
    body.body->body.push_back(std::move(handler));
    auto unreachable = MakeOwned<RefExpr>(); // Missing facts here must not suppress finalizer validation.
    modal.Literal(*unreachable, 2);
    body.body->body.push_back(std::move(unreachable));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, AstMissingSemanticDescriptionIsInvalid)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    body.body->body.push_back(MakeOwned<RefExpr>());
    TestModalFacts modal;
    modal.graph = graph;
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    EXPECT_EQ(result.analysis.status, EscapeAnalysisStatus::INVALID);
}

TEST_F(CapabilityEscapeTest, AstClosureUsesCommittedCapturesWithoutExecutingBody)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto lambda = MakeOwned<LambdaExpr>();
    lambda->funcBody = MakeOwned<FuncBody>();
    lambda->funcBody->body = MakeOwned<Block>();
    lambda->funcBody->body->body.push_back(MakeOwned<RefExpr>()); // No enclosing-flow facts for its body.
    TestModalFacts modal;
    modal.graph = graph;
    modal.Literal(*lambda, 0);
    CapabilityCaptureFacts captures;
    captures.complete = true;
    captures.captures[lambda.get()] = {{0}, {}, false, {}};
    body.body->body.push_back(std::move(lambda));
    auto ret = MakeOwned<RefExpr>();
    EscapeInstruction exit;
    exit.kind = EscapeOp::EXIT;
    exit.site = ret.get();
    exit.inputs = {0};
    exit.boundaries = {&outer};
    modal.nodes[ret.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    body.body->body.push_back(std::move(ret));
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, ResumedValueKeepsItsCapabilityDependencies)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto handler = MakeOwned<TryExpr>();
    handler->tryBlock = MakeOwned<Block>();
    handler->handlers.emplace_back();
    auto& arm = handler->handlers.back();
    arm.block = MakeOwned<Block>();
    auto resume = MakeOwned<ResumeExpr>();
    resume->withExpr = MakeOwned<RefExpr>();
    auto perform = MakeOwned<PerformExpr>();
    perform->expr = MakeOwned<RefExpr>();
    TestModalFacts modal;
    modal.graph = graph;
    modal.Literal(*resume->withExpr, 0, {{0}, {}, false, {}});
    modal.nodes[resume.get()] = {{}, {}, NO_ESCAPE_VALUE, false};
    modal.Literal(*perform->expr, 1);
    modal.nodes[perform.get()] = {{}, {}, 2, false};
    modal.handlers[perform.get()] = {&arm};
    arm.block->body.push_back(std::move(resume));
    handler->tryBlock->body.push_back(std::move(perform));
    auto use = MakeOwned<RefExpr>();
    EscapeInstruction exit;
    exit.kind = EscapeOp::EXIT;
    exit.site = use.get();
    exit.inputs = {2};
    exit.boundaries = {&outer};
    modal.nodes[use.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    handler->tryBlock->body.push_back(std::move(use));
    body.body->body.push_back(std::move(handler));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, AstBreakPreservesTargetAndRunsFinally)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto loop = MakeOwned<WhileExpr>();
    loop->condExpr = MakeOwned<RefExpr>();
    loop->body = MakeOwned<Block>();
    auto handler = MakeOwned<TryExpr>();
    handler->tryBlock = MakeOwned<Block>();
    handler->finallyBlock = MakeOwned<Block>();
    auto jump = MakeOwned<JumpExpr>();
    jump->isBreak = true;
    jump->refLoop = loop.get();
    handler->tryBlock->body.push_back(std::move(jump));
    TestModalFacts modal;
    modal.graph = graph;
    modal.Literal(*loop->condExpr, 0, {{0}, {}, false, {}});
    auto check = MakeOwned<RefExpr>();
    EscapeInstruction exit;
    exit.kind = EscapeOp::EXIT;
    exit.site = check.get();
    exit.inputs = {0};
    exit.boundaries = {&outer};
    modal.nodes[check.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    handler->finallyBlock->body.push_back(std::move(check));
    loop->body->body.push_back(std::move(handler));
    // A use of an undefined register is unreachable after break.
    auto unreachable = MakeOwned<RefExpr>();
    exit.inputs = {15};
    exit.site = unreachable.get();
    modal.nodes[unreachable.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    loop->body->body.push_back(std::move(unreachable));
    body.body->body.push_back(std::move(loop));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, FailedFirstResourceAcquisitionDoesNotCloseUninitializedResource)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    TestModalFacts modal;
    modal.graph = graph;
    auto value = MakeOwned<RefExpr>();
    modal.Literal(*value, 0, {{0}, {}, false, {}});
    body.body->body.push_back(std::move(value));
    auto handler = MakeOwned<TryExpr>();
    handler->tryBlock = MakeOwned<Block>();
    auto resource = MakeOwned<VarDecl>();
    auto thrown = MakeOwned<ThrowExpr>();
    thrown->expr = MakeOwned<RefExpr>();
    modal.Literal(*thrown->expr, 1);
    modal.nodes[thrown.get()] = {{}, {}, NO_ESCAPE_VALUE, false};
    modal.nodes[resource.get()] = {{thrown.get()}, {}, NO_ESCAPE_VALUE, false};
    resource->initializer = std::move(thrown);
    handler->resourceSpec.push_back(std::move(resource));
    EscapeInstruction close;
    close.kind = EscapeOp::EXIT;
    close.site = &site;
    close.inputs = {0};
    close.boundaries = {&outer};
    modal.cleanup = {close};
    body.body->body.push_back(std::move(handler));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_TRUE(result.analysis.violations.empty());
}

TEST_F(CapabilityEscapeTest, ShortCircuitPreservesDependenciesOnEitherPath)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto binary = MakeOwned<BinaryExpr>();
    binary->op = TokenKind::COALESCING;
    binary->leftExpr = MakeOwned<RefExpr>();
    binary->rightExpr = MakeOwned<RefExpr>();
    TestModalFacts modal;
    modal.graph = graph;
    modal.Literal(*binary->leftExpr, 0);
    modal.Literal(*binary->rightExpr, 1, {{0}, {}, false, {}});
    modal.nodes[binary.get()] = {{}, {}, 2, false};
    body.body->body.push_back(std::move(binary));
    auto use = MakeOwned<RefExpr>();
    EscapeInstruction exit;
    exit.kind = EscapeOp::EXIT;
    exit.site = use.get();
    exit.inputs = {2};
    exit.boundaries = {&outer};
    modal.nodes[use.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    body.body->body.push_back(std::move(use));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, TupleComponentOverwriteKeepsOtherComponent)
{
    Value(0, {0});
    Value(1);
    Emit(EscapeOp::TUPLE, 2, {0, 0});
    Value(3, {}, {0});
    Store(2, 3);
    Store(1, 3);
    graph.nodes.back().instruction.componentPath = {0};
    Emit(EscapeOp::LOAD, 4, {3});
    Emit(EscapeOp::PROJECT, 5, {4});
    graph.nodes.back().instruction.component = 0;
    Exit(5, &outer);
    EXPECT_TRUE(Run().violations.empty());
    Emit(EscapeOp::PROJECT, 6, {4});
    graph.nodes.back().instruction.component = 1;
    Exit(6, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, DiagnosticKindsUseIndependentSeverities)
{
    SourceManager sources;
    auto file = sources.AddSource("escape-test.cj", "try { saved = value }\n");
    site.begin = Position{file, 1, 7};
    site.end = Position{file, 1, 12};
    outer.begin = inner.begin = Position{file, 1, 1};
    outer.end = inner.end = Position{file, 1, 4};
    Value(0, {0, 1});
    Value(1, {}, {3});
    Store(0, 1);
    DiagnosticEngine diag;
    diag.SetSourceManager(&sources);
    diag.SetIsEmitter(false);
    EscapeBodyResult result{graph, Run(CheckingLevel::WARN, CheckingLevel::ERROR)};
    ReportCapabilityEscapes(result, diag);
    EXPECT_EQ(diag.GetWarningCount(), 1);
    EXPECT_EQ(diag.GetErrorCount(), 1);
}

TEST_F(CapabilityEscapeTest, ThrowingOperationWithoutValueTransferStillReachesCatch)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    TestModalFacts modal;
    modal.graph = graph;
    auto value = MakeOwned<RefExpr>();
    modal.Literal(*value, 0, {{0}, {}, false, {}});
    body.body->body.push_back(std::move(value));
    auto handler = MakeOwned<TryExpr>();
    handler->tryBlock = MakeOwned<Block>();
    auto operation = MakeOwned<RefExpr>();
    modal.nodes[operation.get()] = {{}, {}, NO_ESCAPE_VALUE, true};
    handler->tryBlock->body.push_back(std::move(operation));
    auto catching = MakeOwned<Block>();
    auto use = MakeOwned<RefExpr>();
    EscapeInstruction exit;
    exit.kind = EscapeOp::EXIT;
    exit.site = use.get();
    exit.inputs = {0};
    exit.boundaries = {&outer};
    modal.nodes[use.get()] = {{}, {exit}, NO_ESCAPE_VALUE, false};
    catching->body.push_back(std::move(use));
    handler->catchBlocks.push_back(std::move(catching));
    body.body->body.push_back(std::move(handler));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, TupleProjectionFromAliasedHeapRetainsKnownCaptures)
{
    Value(0, {0});
    Value(1, {}, {2});
    Store(0, 1);
    Emit(EscapeOp::LOAD, 2, {1});
    Emit(EscapeOp::PROJECT, 3, {2});
    Exit(3, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, IteratorInitializationPrecedesRepeatedProtocolCalls)
{
    FuncBody body;
    body.body = MakeOwned<Block>();
    auto loop = MakeOwned<ForInExpr>();
    loop->inExpression = MakeOwned<RefExpr>();
    loop->body = MakeOwned<Block>();
    TestModalFacts modal;
    modal.graph = graph;
    modal.Literal(*loop->inExpression, 0);
    EscapeInstruction iterator;
    iterator.kind = EscapeOp::VALUE;
    iterator.site = loop.get();
    iterator.result = 1;
    iterator.value.origins = {0};
    EscapeInstruction next;
    next.kind = EscapeOp::EXIT;
    next.site = loop.get();
    next.inputs = {1};
    next.boundaries = {&outer};
    modal.nodes[loop.get()] = {{}, {next}, NO_ESCAPE_VALUE, false};
    modal.nodes[loop.get()].entryOperations = {iterator};
    body.body->body.push_back(std::move(loop));
    CapabilityCaptureFacts captures;
    captures.complete = true;
    auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
    ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
    EXPECT_EQ(result.analysis.violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, MutableReceiverCanBeWrittenWithoutSeparateMutationAnnotation)
{
    Value(0, {0});
    Value(1, {}, {2});
    Emit(EscapeOp::CALL, 2, {0, 1});
    graph.nodes.back().instruction.mutableInputs = {1};
    graph.nodes.back().instruction.independentResult = true;
    Exit(1, &outer);
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, FreshWrapperDoesNotMakeReachableOuterStorageSafe)
{
    graph.locations[2].initialValue.locations = {3};
    Value(0, {0});
    Value(1, {}, {2});
    Emit(EscapeOp::CALL, 2, {0, 1});
    graph.nodes.back().instruction.mutableInputs = {1};
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, MissingDiagnosticSiteCannotBeAcceptedAsSuccessfulValidation)
{
    Value(0, {0});
    Exit(0, &outer);
    graph.nodes.back().instruction.site = nullptr;
    EXPECT_EQ(Run().status, EscapeAnalysisStatus::INVALID);
}

TEST_F(CapabilityEscapeTest, LoopPropagationHasNoFixedIterationLimit)
{
    constexpr size_t count = 80;
    graph.locations.assign(count, {{&outer}, false, {}});
    graph.locations[0].initialValue.origins = {0};
    Value(0, {}, {count - 1});
    auto header = Emit(EscapeOp::LOAD, 2, {0});
    Exit(2, &outer);
    auto exit = graph.nodes.size() - 1;
    auto body = graph.nodes.size();
    // Reverse order forces one extra hop per loop iteration.
    for (size_t i = count - 1; i > 0; --i) {
        Value(1, {}, {i - 1});
        Emit(EscapeOp::LOAD, 2, {1});
        Value(1, {}, {i});
        Store(2, 1);
    }
    graph.nodes[header].successors = {body, exit};
    graph.nodes[exit].successors.clear();
    graph.nodes.back().successors = {header};
    EXPECT_EQ(Run().violations.size(), 1);
}

TEST_F(CapabilityEscapeTest, CleanupCannotAddACaptureToAnAlreadyEvaluatedResult)
{
    for (bool explicitReturn : {false, true}) {
        FuncBody body;
        body.body = MakeOwned<Block>();
        auto handler = MakeOwned<TryExpr>();
        handler->tryBlock = MakeOwned<Block>();
        TestModalFacts modal;
        modal.graph = graph;
        modal.graph.origins[0].boundary = handler.get();
        modal.graph.locations[2].boundaries = {handler.get()};
        auto resource = MakeOwned<VarDecl>();
        resource->initializer = MakeOwned<RefExpr>();
        modal.Literal(*resource->initializer, 0, {{}, {2}, false, {}});
        modal.nodes[resource.get()] = {{resource->initializer.get()}, {}, NO_ESCAPE_VALUE, false};
        handler->resourceSpec.push_back(std::move(resource));
        auto returned = MakeOwned<RefExpr>();
        EscapeInstruction copy;
        copy.kind = EscapeOp::COPY;
        copy.site = returned.get();
        copy.inputs = {0};
        copy.result = 2;
        modal.nodes[returned.get()] = {{}, {copy}, 2, false};
        if (explicitReturn) {
            auto ret = MakeOwned<ReturnExpr>();
            ret->refFuncBody = &body;
            ret->expr = std::move(returned);
            handler->tryBlock->body.push_back(std::move(ret));
        } else {
            modal.nodes[handler->tryBlock.get()] = {{}, {}, 2, false};
            handler->tryBlock->body.push_back(std::move(returned));
        }
        EscapeInstruction close;
        close.kind = EscapeOp::CALL;
        close.site = &site;
        close.inputs = {0};
        close.mutableInputs = {0};
        close.value.origins = {0};
        close.independentResult = true;
        modal.cleanup = {close};
        body.body->body.push_back(std::move(handler));
        CapabilityCaptureFacts captures;
        captures.complete = true;
        auto result = CheckCapabilityEscapes(body, captures, &modal, CheckingLevel::ERROR, CheckingLevel::ERROR);
        ASSERT_EQ(result.analysis.status, EscapeAnalysisStatus::COMPLETE);
        EXPECT_EQ(result.analysis.violations.size(), 1) << "explicit return: " << explicitReturn;
    }
}
} // namespace
