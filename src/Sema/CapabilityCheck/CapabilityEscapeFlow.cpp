// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "cangjie/AST/ASTCasting.h"
#include "cangjie/Sema/CapabilityEscape.h"

namespace Cangjie::Sema {
namespace {
using namespace AST;
struct Target {
    size_t node;
    std::vector<const Node*> boundaries;
};
struct HandlerFlow;
struct FlowContext {
    size_t exception;
    Target returning;
    std::map<const Expr*, std::pair<Target, Target>> loops;
    std::vector<const Node*> boundaries;
    std::vector<std::shared_ptr<HandlerFlow>> handlers;
    // Build value-specific return routes so boundary checks happen AFTER resource mutation.
    std::vector<std::function<size_t(size_t, const Node&, size_t)>> returnCleanups;
    std::vector<std::function<size_t(size_t, const Node&, size_t)>> resumeCleanups;
    std::optional<Target> resuming;
    size_t resumeResult{NO_ESCAPE_VALUE};
    size_t resumeException{NO_ESCAPE_VALUE};
};
struct HandlerFlow {
    const TryExpr* expr;
    FlowContext context;
    size_t normal;
    size_t result;
};

/** Continuation construction keeps return/break/continue targets intact across cleanup. */
class Builder {
public:
    Builder(const FuncBody& body, const CapabilityCaptureFacts& captures, const ModalEscapeFacts& modal)
        : body(body), captures(captures), modal(modal), graph(modal.CreateGraph(body))
    {
    }

    std::optional<EscapeGraph> Build()
    {
        if (!graph.nodes.empty()) {
            return {}; // The adapter describes semantics, not a second control-flow graph.
        }
        auto end = Add({}, {});
        FlowContext context{end, {end, {}}, {}, {}};
        graph.entry = Walk(&body, end, context);
        return valid ? std::optional<EscapeGraph>(std::move(graph)) : std::nullopt;
    }

private:
    const FuncBody& body;
    const CapabilityCaptureFacts& captures;
    const ModalEscapeFacts& modal;
    EscapeGraph graph;
    bool valid{true};

    size_t Add(EscapeInstruction op, std::vector<size_t> successors)
    {
        auto id = graph.nodes.size();
        graph.nodes.push_back({std::move(op), std::move(successors)});
        return id;
    }

    EscapeNodeFacts Facts(const Node& node)
    {
        auto facts = modal.Describe(node);
        if (!facts) {
            valid = false;
            return {};
        }
        return *facts;
    }

    size_t Operations(const std::vector<EscapeInstruction>& ops, size_t next, size_t exception, bool mayThrow)
    {
        if (ops.empty() && mayThrow) {
            return Add({}, {next, exception});
        }
        for (auto it = ops.rbegin(); it != ops.rend(); ++it) {
            std::vector<size_t> successors{next};
            if (mayThrow) {
                successors.push_back(exception);
            }
            next = Add(*it, std::move(successors));
        }
        return next;
    }

    size_t CopyResult(const Node* source, size_t destination, size_t next)
    {
        if (!source || destination == NO_ESCAPE_VALUE) {
            return next;
        }
        auto value = Facts(*source).result;
        if (value == NO_ESCAPE_VALUE) {
            if (auto expr = DynamicCast<const Expr*>(source);
                expr && Ty::IsTyCorrect(expr->GetTy()) && expr->GetTy()->IsNothing()) {
                return next; // This branch never reaches its result-copy continuation.
            }
            valid = false;
            return next;
        }
        EscapeInstruction copy;
        copy.kind = EscapeOp::COPY;
        copy.site = source;
        copy.inputs = {value};
        copy.result = destination;
        return Add(copy, {next});
    }

    size_t Exit(const Node& site, size_t value, const FlowContext& context, const Target& target)
    {
        if (value == NO_ESCAPE_VALUE) {
            return target.node;
        }
        EscapeInstruction exit;
        exit.kind = EscapeOp::EXIT;
        exit.site = &site;
        exit.inputs = {value};
        for (auto boundary : context.boundaries) {
            if (std::find(target.boundaries.begin(), target.boundaries.end(), boundary) == target.boundaries.end()) {
                exit.boundaries.push_back(boundary);
            }
        }
        return Add(exit, {target.node});
    }

    size_t Sequence(const std::vector<const Node*>& nodes, size_t next, const FlowContext& context)
    {
        for (auto it = nodes.rbegin(); it != nodes.rend(); ++it) {
            next = Walk(*it, next, context);
        }
        return next;
    }

    size_t Loop(const Expr& loop, const Node* condition, const Block* block, const Node* guard, size_t next,
        const FlowContext& context, bool doWhile = false)
    {
        auto branch = Add({}, {});
        auto conditionEntry = Walk(condition, branch, context);
        FlowContext inner = context;
        inner.loops[&loop] = {{next, context.boundaries}, {conditionEntry, context.boundaries}};
        auto bodyEntry = Walk(block, conditionEntry, inner);
        if (guard) {
            auto guardBranch = Add({}, {bodyEntry, conditionEntry});
            bodyEntry = Walk(guard, guardBranch, inner);
        }
        graph.nodes[branch].successors = {bodyEntry, next};
        return doWhile ? bodyEntry : conditionEntry;
    }

    size_t Match(const MatchExpr& match, size_t next, const FlowContext& context, size_t result)
    {
        // Pattern extraction and guards remain in the adapter's source-ordered case facts.
        auto fallback = context.exception;
        for (auto it = match.matchCases.rbegin(); it != match.matchCases.rend(); ++it) {
            auto& arm = **it;
            auto chosen = Walk(arm.exprOrDecls.get(), CopyResult(arm.exprOrDecls.get(), result, next), context);
            if (arm.patternGuard) {
                chosen = Walk(arm.patternGuard.get(), Add({}, {chosen, fallback}), context);
            }
            auto facts = Facts(arm);
            chosen = Operations(facts.operations, chosen, context.exception, facts.mayThrow);
            chosen = Sequence(facts.evaluationOrder, chosen, context);
            fallback = Add({}, {chosen, fallback});
        }
        for (auto it = match.matchCaseOthers.rbegin(); it != match.matchCaseOthers.rend(); ++it) {
            auto& arm = **it;
            auto chosen = Walk(arm.exprOrDecls.get(), CopyResult(arm.exprOrDecls.get(), result, next), context);
            fallback = Walk(arm.matchExpr.get(), Add({}, {chosen, fallback}), context);
        }
        return Walk(match.selector.get(), fallback, context);
    }

    // Each close can throw. On that edge, close the remaining resources before dispatching the
    // new exception, including when the original continuation was a return or loop jump.
    size_t Close(const TryExpr& expr, size_t initialized, size_t normal, size_t exceptional)
    {
        auto ops = modal.Cleanup(expr, initialized);
        size_t unwind = exceptional;
        for (auto it = ops.rbegin(); it != ops.rend(); ++it) {
            auto nextNormal = Add(*it, {normal, unwind});
            unwind = Add(*it, {unwind});
            normal = nextNormal;
        }
        return normal;
    }

    size_t Try(const TryExpr& expr, size_t next, const FlowContext& context, size_t result)
    {
        const Node* finallyBody =
            expr.finallyLambda ? expr.finallyLambda->funcBody->body.get() : expr.finallyBlock.get();
        auto finish = [&](size_t target) { return Walk(finallyBody, target, context); };
        auto normal = finish(next);
        auto exceptional = finish(context.exception);
        std::vector<size_t> catches{exceptional};
        for (const auto& block : expr.catchBlocks) {
            FlowContext catching = context;
            catching.exception = exceptional;
            catching.returnCleanups.push_back([this, finallyBody, context](size_t, const Node&, size_t target) {
                return Walk(finallyBody, target, context);
            });
            if (catching.resuming) {
                catching.resumeCleanups.push_back(catching.returnCleanups.back());
                catching.resumeException = finish(catching.resumeException);
            }
            for (auto& [loop, targets] : catching.loops) {
                targets.first.node = finish(targets.first.node);
                targets.second.node = finish(targets.second.node);
            }
            catches.push_back(Walk(block.get(), CopyResult(block.get(), result, normal), catching));
        }
        auto dispatch = Add({}, std::move(catches));
        auto protectedContext = [&](size_t initialized) {
            auto inner = context;
            inner.boundaries.push_back(&expr);
            inner.exception = Close(expr, initialized, dispatch, dispatch);
            inner.returnCleanups.push_back([this, &expr, initialized, finallyBody, context, dispatch](
                                               size_t value, const Node& site, size_t target) {
                target = Walk(finallyBody, target, context);
                auto leaving = context;
                leaving.boundaries.push_back(&expr);
                target = Exit(site, value, leaving, {target, context.boundaries});
                return Close(expr, initialized, target, dispatch);
            });
            for (auto& [loop, targets] : inner.loops) {
                targets.first.node = Close(expr, initialized, finish(targets.first.node), dispatch);
                targets.second.node = Close(expr, initialized, finish(targets.second.node), dispatch);
            }
            if (context.resuming) {
                inner.resumeCleanups.push_back(inner.returnCleanups.back());
                inner.resumeException = Close(expr, initialized, finish(context.resumeException), dispatch);
            }
            if (!expr.handlers.empty()) {
                auto handling = context;
                handling.exception = exceptional;
                handling.returnCleanups.push_back([this, finallyBody, context](size_t, const Node&, size_t target) {
                    return Walk(finallyBody, target, context);
                });
                for (auto& [loop, targets] : handling.loops) {
                    targets.first.node = finish(targets.first.node);
                    targets.second.node = finish(targets.second.node);
                }
                inner.handlers.push_back(std::make_shared<HandlerFlow>(HandlerFlow{&expr, handling, normal, result}));
            }
            return inner;
        };
        const Node* protectedBody = expr.tryLambda ? expr.tryLambda->funcBody->body.get() : expr.tryBlock.get();
        auto inner = protectedContext(expr.resourceSpec.size());
        auto continuation = normal;
        if (protectedBody) {
            continuation =
                Exit(*protectedBody, Facts(*protectedBody).result, inner, {continuation, context.boundaries});
        }
        continuation = Close(expr, expr.resourceSpec.size(), continuation, dispatch);
        continuation = CopyResult(protectedBody, result, continuation);
        auto entry = Walk(protectedBody, continuation, inner);
        for (size_t i = expr.resourceSpec.size(); i > 0; --i) {
            entry = Walk(expr.resourceSpec[i - 1].get(), entry, protectedContext(i - 1));
        }
        return entry;
    }

    size_t Perform(const PerformExpr& expr, size_t next, const FlowContext& context, size_t result)
    {
        auto selected = modal.ResolvedHandlers(expr);
        if (selected.empty()) {
            return Walk(expr.expr.get(), next, context);
        }
        std::vector<size_t> branches;
        for (auto handler : selected) {
            std::shared_ptr<HandlerFlow> owner;
            for (auto scope = context.handlers.rbegin(); scope != context.handlers.rend(); ++scope) {
                for (auto& candidate : (*scope)->expr->handlers) {
                    if (&candidate == handler) {
                        owner = *scope;
                        break;
                    }
                }
                if (owner) {
                    break;
                }
            }
            if (!owner) {
                valid = false;
                continue;
            }
            auto handling = owner->context;
            handling.resuming = Target{next, context.boundaries};
            handling.resumeCleanups.clear();
            handling.resumeResult = result;
            handling.resumeException = context.exception;
            const Node* handlerBody =
                handler->desugaredLambda ? handler->desugaredLambda->funcBody->body.get() : handler->block.get();
            branches.push_back(Walk(handlerBody, CopyResult(handlerBody, owner->result, owner->normal), handling));
        }
        return Walk(expr.expr.get(), Add({}, std::move(branches)), context);
    }

    size_t Walk(const Node* node, size_t next, const FlowContext& context)
    {
        if (!node) {
            return next;
        }
        auto facts = Facts(*node);
        auto capture = captures.captures.find(node);
        if (capture != captures.captures.end()) {
            if (facts.result == NO_ESCAPE_VALUE) {
                valid = false;
            } else {
                EscapeInstruction merge;
                merge.kind = EscapeOp::MERGE;
                merge.site = node;
                merge.result = facts.result;
                merge.inputs = {facts.result};
                merge.value = capture->second;
                next = Add(merge, {next});
            }
        }
        if (node->astKind != ASTKind::FOR_IN_EXPR) {
            next = Operations(facts.operations, next, context.exception, facts.mayThrow);
        }
        if (auto block = DynamicCast<const Block*>(node)) {
            if (!block->body.empty()) {
                next = CopyResult(block->body.back().get(), facts.result, next);
            }
            for (auto it = block->body.rbegin(); it != block->body.rend(); ++it) {
                next = Walk(it->get(), next, context);
            }
            return next;
        }
        if (auto function = DynamicCast<const FuncBody*>(node)) {
            if (function != &body) {
                valid = false; // Nested invocations require independent analysis contexts.
                return next;
            }
            next = Walk(function->body.get(), next, context);
            return Sequence(facts.evaluationOrder, next, context); // Defaults in ownerFunc context.
        }
        if (auto branch = DynamicCast<const IfExpr*>(node)) {
            auto yes = Walk(branch->thenBody.get(), CopyResult(branch->thenBody.get(), facts.result, next), context);
            auto no = Walk(branch->elseBody.get(), CopyResult(branch->elseBody.get(), facts.result, next), context);
            return Walk(branch->condExpr.get(), Add({}, {yes, no}), context);
        }
        if (auto loop = DynamicCast<const WhileExpr*>(node)) {
            return Loop(*loop, loop->condExpr.get(), loop->body.get(), nullptr, next, context);
        }
        if (auto loop = DynamicCast<const DoWhileExpr*>(node)) {
            return Loop(*loop, loop->condExpr.get(), loop->body.get(), nullptr, next, context, true);
        }
        if (auto loop = DynamicCast<const ForInExpr*>(node)) {
            // iterator()/next()/pattern binding are distinct adapter events. Evaluation order
            // contains the per-iteration events; the iterable itself is evaluated only once.
            auto branch = Add({}, {});
            auto iteration = Operations(facts.operations, branch, context.exception, facts.mayThrow);
            iteration = Sequence(facts.evaluationOrder, iteration, context);
            auto inner = context;
            inner.loops[loop] = {{next, context.boundaries}, {iteration, context.boundaries}};
            auto entry = Walk(loop->body.get(), iteration, inner);
            if (loop->patternGuard) {
                entry = Walk(loop->patternGuard.get(), Add({}, {entry, iteration}), inner);
            }
            graph.nodes[branch].successors = {entry, next};
            auto entryOperations = Operations(facts.entryOperations, iteration, context.exception, facts.mayThrow);
            return Walk(loop->inExpression.get(), entryOperations, context);
        }
        if (auto match = DynamicCast<const MatchExpr*>(node)) {
            return Match(*match, next, context, facts.result);
        }
        if (auto expr = DynamicCast<const TryExpr*>(node)) {
            return Try(*expr, next, context, facts.result);
        }
        if (auto ret = DynamicCast<const ReturnExpr*>(node)) {
            if (ret->refFuncBody && ret->refFuncBody != &body) {
                valid = false;
            }
            auto value = ret->expr ? Facts(*ret->expr).result : NO_ESCAPE_VALUE;
            auto target = context.returning.node;
            for (auto& cleanup : context.returnCleanups) {
                target = cleanup(value, *ret, target);
            }
            return Walk(ret->expr.get(), target, context);
        }
        if (auto jump = DynamicCast<const JumpExpr*>(node)) {
            auto found = context.loops.find(jump->refLoop);
            if (found == context.loops.end()) {
                valid = false;
                return next;
            }
            return jump->isBreak ? found->second.first.node : found->second.second.node;
        }
        if (auto thrown = DynamicCast<const ThrowExpr*>(node)) {
            return Walk(thrown->expr.get(), context.exception, context);
        }
        if (auto perform = DynamicCast<const PerformExpr*>(node)) {
            return Perform(*perform, next, context, facts.result);
        }
        if (auto resume = DynamicCast<const ResumeExpr*>(node)) {
            if (!context.resuming) {
                valid = false;
                return next;
            }
            if (resume->throwingExpr) {
                return Walk(resume->throwingExpr.get(), context.resumeException, context);
            }
            auto target = context.resuming->node;
            target = CopyResult(resume->withExpr.get(), context.resumeResult, target);
            auto value = resume->withExpr ? Facts(*resume->withExpr).result : NO_ESCAPE_VALUE;
            for (auto& cleanup : context.resumeCleanups) {
                target = cleanup(value, *resume, target);
            }
            return Walk(resume->withExpr.get(), target, context);
        }
        if (auto binary = DynamicCast<const BinaryExpr*>(node); binary &&
            (binary->op == TokenKind::AND || binary->op == TokenKind::OR || binary->op == TokenKind::COALESCING)) {
            auto rhs = Walk(binary->rightExpr.get(), CopyResult(binary->rightExpr.get(), facts.result, next), context);
            auto lhs = CopyResult(binary->leftExpr.get(), facts.result, next);
            return Walk(binary->leftExpr.get(), Add({}, {rhs, lhs}), context);
        }
        if (node->IsFuncLike() || node->astKind == ASTKind::FUNC_DECL) {
            return next; // Capture facts describe the value; the nested body is never executed here.
        }
        return Sequence(facts.evaluationOrder, next, context);
    }
};
} // namespace

EscapeBodyResult CheckCapabilityEscapes(const AST::FuncBody& body, const CapabilityCaptureFacts& captures,
    const ModalEscapeFacts* modal, CheckingLevel exceptions, CheckingLevel effects)
{
    if (!modal || !modal->IsEnabled() || (exceptions == CheckingLevel::OFF && effects == CheckingLevel::OFF)) {
        return {{}, {EscapeAnalysisStatus::DISABLED, {}}};
    }
    if (!captures.complete || !modal->IsComplete(body)) {
        return {};
    }
    auto graph = Builder(body, captures, *modal).Build();
    if (!graph) {
        return {};
    }
    auto analysis = CapabilityEscapeAnalyzer().Analyze(*graph, exceptions, effects);
    return {std::move(*graph), std::move(analysis)};
}
} // namespace Cangjie::Sema
