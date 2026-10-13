// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
// See https://cangjie-lang.cn/pages/LICENSE for license information.

#include "cangjie/Sema/CapabilityEscape.h"

#include <algorithm>
#include <deque>

namespace Cangjie::Sema {
bool EscapeValue::operator==(const EscapeValue& other) const
{
    return origins == other.origins && locations == other.locations && unknownStorage == other.unknownStorage &&
        components == other.components;
}

namespace {
// Structured values have a bounded shape fixed by the typed expression. An unstructured summary
// is a conservative upper bound of every component; joins never invent component precision.
EscapeValue Flatten(const EscapeValue& value)
{
    EscapeValue result{value.origins, value.locations, value.unknownStorage, {}};
    for (const auto& component : value.components) {
        auto flat = Flatten(component);
        result.origins.insert(flat.origins.begin(), flat.origins.end());
        result.locations.insert(flat.locations.begin(), flat.locations.end());
        result.unknownStorage |= flat.unknownStorage;
    }
    return result;
}

bool Join(EscapeValue& into, const EscapeValue& from)
{
    auto previous = into;
    into.origins.insert(from.origins.begin(), from.origins.end());
    into.locations.insert(from.locations.begin(), from.locations.end());
    into.unknownStorage |= from.unknownStorage;
    if (into.components.size() == from.components.size()) {
        for (size_t i = 0; i < into.components.size(); ++i) {
            Join(into.components[i], from.components[i]);
        }
    } else {
        auto flat = Flatten(from);
        into = Flatten(into);
        into.origins.insert(flat.origins.begin(), flat.origins.end());
        into.locations.insert(flat.locations.begin(), flat.locations.end());
        into.unknownStorage |= flat.unknownStorage;
    }
    return !(into == previous);
}

struct State {
    std::vector<EscapeValue> values;
    std::vector<EscapeValue> storage;
    std::set<size_t> defined;
};

bool Join(State& into, const State& from)
{
    bool changed = false;
    for (size_t i = 0; i < into.values.size(); ++i) {
        changed |= Join(into.values[i], from.values[i]);
    }
    for (size_t i = 0; i < into.storage.size(); ++i) {
        changed |= Join(into.storage[i], from.storage[i]);
    }
    for (auto it = into.defined.begin(); it != into.defined.end();) {
        if (from.defined.count(*it) == 0) {
            it = into.defined.erase(it);
            changed = true;
        } else {
            ++it;
        }
    }
    return changed;
}

CheckingLevel Level(const CapabilityOrigin& origin, CheckingLevel exceptions, CheckingLevel effects)
{
    return origin.kind == CapabilityKind::EFFECT   ? effects
        : origin.kind == CapabilityKind::EXCEPTION ? exceptions
                                                   : CheckingLevel::OFF;
}

bool ValidValue(const EscapeGraph& graph, const EscapeValue& value)
{
    return std::all_of(value.origins.begin(), value.origins.end(), [&](auto i) { return i < graph.origins.size(); }) &&
        std::all_of(
            value.locations.begin(), value.locations.end(), [&](auto i) { return i < graph.locations.size(); }) &&
        std::all_of(value.components.begin(), value.components.end(), [&](auto& v) { return ValidValue(graph, v); });
}

bool ValidGraph(const EscapeGraph& graph)
{
    if (graph.nodes.empty() || graph.entry >= graph.nodes.size()) {
        return false;
    }
    for (const auto& location : graph.locations) {
        if (!ValidValue(graph, location.initialValue)) {
            return false;
        }
    }
    for (const auto& node : graph.nodes) {
        const auto& op = node.instruction;
        if ((op.kind == EscapeOp::STORE || op.kind == EscapeOp::EXIT || op.kind == EscapeOp::CALL) && !op.site) {
            return false;
        }
        if (!ValidValue(graph, op.value) || (op.result != NO_ESCAPE_VALUE && op.result >= graph.valueCount) ||
            (op.freshLocation != NO_ESCAPE_VALUE && op.freshLocation >= graph.locations.size()) ||
            std::any_of(op.inputs.begin(), op.inputs.end(), [&](auto i) { return i >= graph.valueCount; }) ||
            std::any_of(
                node.successors.begin(), node.successors.end(), [&](auto i) { return i >= graph.nodes.size(); }) ||
            std::any_of(
                op.mutableInputs.begin(), op.mutableInputs.end(), [&](auto i) { return i >= op.inputs.size(); }) ||
            std::any_of(
                op.writtenInputs.begin(), op.writtenInputs.end(), [&](auto i) { return i >= op.inputs.size(); })) {
            return false;
        }
        switch (op.kind) {
            case EscapeOp::COPY:
            case EscapeOp::PROJECT:
            case EscapeOp::LOAD:
            case EscapeOp::EXIT:
                if (op.inputs.size() != 1) {
                    return false;
                }
                break;
            case EscapeOp::STORE:
                if (op.inputs.size() != 2) {
                    return false;
                }
                break;
            default:
                break;
        }
    }
    return true;
}

EscapeValue Reachable(const State& state, const EscapeValue& value)
{
    auto result = Flatten(value);
    std::set<size_t> visited;
    std::vector<size_t> pending(result.locations.begin(), result.locations.end());
    while (!pending.empty()) {
        auto location = pending.back();
        pending.pop_back();
        if (!visited.insert(location).second) {
            continue;
        }
        auto contents = Flatten(state.storage[location]);
        result.origins.insert(contents.origins.begin(), contents.origins.end());
        result.unknownStorage |= contents.unknownStorage;
        for (auto target : contents.locations) {
            result.locations.insert(target);
            pending.push_back(target);
        }
    }
    return result;
}

void Write(State& state, const EscapeGraph& graph, const EscapeValue& address, const EscapeValue& value, bool weak,
    const std::vector<size_t>& path = {})
{
    auto targets = Flatten(address);
    // Unknown aliases may denote any modeled storage. Never erase a known dependency.
    if (targets.unknownStorage) {
        for (auto& contents : state.storage) {
            Join(contents, Flatten(value));
        }
    }
    for (auto location : targets.locations) {
        if (!weak && !targets.unknownStorage && targets.locations.size() == 1 && !graph.locations[location].shared) {
            auto target = &state.storage[location];
            for (auto component : path) {
                if (component >= target->components.size()) {
                    target = nullptr;
                    break;
                }
                target = &target->components[component];
            }
            if (target) {
                *target = value;
            } else {
                Join(state.storage[location], Flatten(value));
            }
        } else {
            Join(state.storage[location], Flatten(value));
        }
    }
}

// A malformed adapter must not make a growing tuple cycle an unbounded analysis. Typed tuple
// nesting cannot exceed the finite source graph plus the nesting of its constant values.
size_t Depth(const EscapeValue& value)
{
    size_t result = 0;
    for (auto& component : value.components) {
        result = std::max(result, 1 + Depth(component));
    }
    return result;
}

State Transfer(const EscapeGraph& graph, const EscapeInstruction& op, State state)
{
    EscapeValue result = op.value;
    switch (op.kind) {
        case EscapeOp::COPY:
            result = state.values[op.inputs[0]];
            break;
        case EscapeOp::MERGE:
        case EscapeOp::CALL:
            for (auto input : op.inputs) {
                Join(result, Flatten(state.values[input]));
            }
            if (op.kind == EscapeOp::CALL) {
                auto retained = Reachable(state, result);
                auto writes = op.writtenInputs;
                writes.insert(writes.end(), op.mutableInputs.begin(), op.mutableInputs.end());
                for (auto index : writes) {
                    auto targets = Reachable(state, state.values[op.inputs[index]]);
                    Write(state, graph, targets, retained, true);
                }
                // Refresh after mutation so aliases of mutated inputs also retain dependencies.
                result = Reachable(state, result);
                if (op.independentResult) {
                    result = {};
                } else if (op.freshLocation != NO_ESCAPE_VALUE) {
                    Join(state.storage[op.freshLocation], result);
                    result = {{}, {op.freshLocation}, false, {}};
                } else if (op.referenceResult) {
                    result.unknownStorage = true;
                }
            }
            break;
        case EscapeOp::TUPLE:
            for (auto input : op.inputs) {
                result.components.push_back(state.values[input]);
            }
            break;
        case EscapeOp::PROJECT: {
            const auto& tuple = state.values[op.inputs[0]];
            result = {tuple.origins, tuple.locations, tuple.unknownStorage, {}};
            if (op.component < tuple.components.size()) {
                auto component = tuple.components[op.component];
                component.origins.insert(result.origins.begin(), result.origins.end());
                component.locations.insert(result.locations.begin(), result.locations.end());
                component.unknownStorage |= result.unknownStorage;
                result = std::move(component);
            } else {
                result = Flatten(tuple);
            }
            break;
        }
        case EscapeOp::LOAD: {
            const auto& address = state.values[op.inputs[0]];
            bool first = true;
            for (auto location : Flatten(address).locations) {
                if (first) {
                    result = state.storage[location];
                    first = false;
                } else {
                    Join(result, state.storage[location]);
                }
            }
            result.origins.insert(address.origins.begin(), address.origins.end());
            if (address.unknownStorage) {
                for (auto& contents : state.storage) {
                    Join(result, Flatten(contents));
                }
                result.unknownStorage = true;
            }
            break;
        }
        case EscapeOp::STORE:
            Write(state, graph, state.values[op.inputs[1]], state.values[op.inputs[0]], false, op.componentPath);
            break;
        default:
            break;
    }
    if (op.result != NO_ESCAPE_VALUE) {
        state.values[op.result] = std::move(result);
        state.defined.insert(op.result);
    }
    return state;
}

bool Outside(const EscapeGraph& graph, const EscapeValue& address, const AST::Node* boundary)
{
    auto targets = Flatten(address);
    return targets.unknownStorage || targets.locations.empty() ||
        std::any_of(targets.locations.begin(), targets.locations.end(),
            [&](auto location) { return graph.locations[location].boundaries.count(boundary) == 0; });
}

void Check(const EscapeGraph& graph, const EscapeInstruction& op, const State& state, CheckingLevel exceptions,
    CheckingLevel effects, std::vector<EscapeViolation>& violations)
{
    if (op.kind != EscapeOp::STORE && op.kind != EscapeOp::EXIT && op.kind != EscapeOp::CALL) {
        return;
    }
    EscapeValue value;
    if (op.kind == EscapeOp::CALL) {
        value = op.value;
        for (auto input : op.inputs) {
            Join(value, Flatten(state.values[input]));
        }
    } else {
        value = state.values[op.inputs[0]];
    }
    value = Reachable(state, value);
    for (auto id : value.origins) {
        const auto& origin = graph.origins[id];
        auto level = Level(origin, exceptions, effects);
        if (!origin.boundary || level == CheckingLevel::OFF) {
            continue;
        }
        bool bad = false;
        bool conservative = false;
        auto reason = EscapeViolationKind::RESULT;
        if (op.kind == EscapeOp::STORE) {
            auto address = Flatten(state.values[op.inputs[1]]);
            bad = Outside(graph, address, origin.boundary);
            conservative = address.unknownStorage || address.locations.empty();
            reason = EscapeViolationKind::STORE;
        } else if (op.kind == EscapeOp::EXIT) {
            bad = std::find(op.boundaries.begin(), op.boundaries.end(), origin.boundary) != op.boundaries.end();
        } else {
            // Mutated captured cells must also obey the store rule, even when the corresponding
            // explicit parameter has a local? view rather than a local! view.
            auto checkedInputs = op.mutableInputs;
            checkedInputs.insert(checkedInputs.end(), op.writtenInputs.begin(), op.writtenInputs.end());
            for (auto index : checkedInputs) {
                auto address = Reachable(state, state.values[op.inputs[index]]);
                bad |= Outside(graph, address, origin.boundary);
                conservative |= address.unknownStorage || address.locations.empty();
            }
            reason = EscapeViolationKind::MUTABLE_CALL;
        }
        if (!bad) {
            continue;
        }
        auto found = std::find_if(violations.begin(), violations.end(),
            [&](auto& violation) { return violation.site == op.site && violation.kind == origin.kind; });
        if (found == violations.end()) {
            violations.push_back({op.site, reason, origin.kind, level, {id}, conservative});
        } else {
            found->origins.insert(id);
            found->conservative |= conservative;
        }
    }
}
} // namespace

EscapeAnalysisResult CapabilityEscapeAnalyzer::Analyze(
    const EscapeGraph& graph, CheckingLevel exceptions, CheckingLevel effects) const
{
    if (exceptions == CheckingLevel::OFF && effects == CheckingLevel::OFF) {
        return {EscapeAnalysisStatus::DISABLED, {}};
    }
    if (!ValidGraph(graph)) {
        return {};
    }
    State initial;
    initial.values.resize(graph.valueCount);
    size_t maxDepth = graph.nodes.size();
    for (auto& location : graph.locations) {
        initial.storage.push_back(location.initialValue);
        maxDepth += Depth(location.initialValue);
    }
    for (auto& node : graph.nodes) {
        maxDepth += Depth(node.instruction.value);
    }
    std::vector<std::optional<State>> inputs(graph.nodes.size());
    inputs[graph.entry] = initial;
    std::deque<size_t> pending{graph.entry};
    std::vector<bool> queued(graph.nodes.size(), false);
    queued[graph.entry] = true;
    while (!pending.empty()) {
        auto index = pending.front();
        pending.pop_front();
        queued[index] = false;
        auto state = Transfer(graph, graph.nodes[index].instruction, *inputs[index]);
        if (std::any_of(state.values.begin(), state.values.end(), [&](auto& v) { return Depth(v) > maxDepth; })) {
            return {}; // Ill-typed recursive tuple shape in adapter facts.
        }
        for (auto successor : graph.nodes[index].successors) {
            bool changed = false;
            if (!inputs[successor]) {
                inputs[successor] = state;
                changed = true;
            } else {
                changed = Join(*inputs[successor], state);
            }
            if (changed && !queued[successor]) {
                queued[successor] = true;
                pending.push_back(successor);
            }
        }
    }
    EscapeAnalysisResult result{EscapeAnalysisStatus::COMPLETE, {}};
    for (size_t i = 0; i < graph.nodes.size(); ++i) {
        if (!inputs[i]) {
            continue;
        }
        const auto& op = graph.nodes[i].instruction;
        if (std::any_of(op.inputs.begin(), op.inputs.end(), [&](auto id) { return !inputs[i]->defined.count(id); })) {
            return {}; // Missing prerequisite facts must not be mistaken for an empty value.
        }
        Check(graph, op, *inputs[i], exceptions, effects, result.violations);
    }
    for (auto& violation : result.violations) {
        for (size_t i = 0; i < graph.nodes.size(); ++i) {
            if (!inputs[i]) {
                continue;
            }
            const auto& op = graph.nodes[i].instruction;
            for (auto origin : Flatten(op.value).origins) {
                if (violation.origins.count(origin) && op.site) {
                    violation.captureSites.emplace(origin, op.site);
                }
            }
        }
    }
    return result;
}
} // namespace Cangjie::Sema
