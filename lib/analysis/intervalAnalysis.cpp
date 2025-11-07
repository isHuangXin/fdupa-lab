#include "intervalAnalysis.h"
#include <queue>

using namespace fdlang;
using namespace fdlang::analysis;

void IntervalAnalysis::fixedPoint() {
    // ini States and worklist
    inputStates[0] = iniStates();
    worklist.push(0);

    // worklist Iteration here
    while (!worklist.empty()) {
        auto label = worklist.front();
        worklist.pop();
        auto inst = insts[label];
        States &inputState = inputStates[label];
        States outputState;
        // transfer Inst
        outputState = transfer(inst, inputState);
        // add Successors
        addSuccessors(label, outputState);
    }
}

/****************************************************************
********************* Your code starts here *********************
*****************************************************************/

void IntervalAnalysis::checkInstsStates() {
    // You can modify this function arbitrarily
    for (auto inst : insts) {
        if (inst->getInstType() != IR::InstType::CheckIntervalInst)
            continue;

        IR::CheckIntervalInst *checkInst = (IR::CheckIntervalInst *)inst;
        std::string variable = checkInst->getOperand(0)->getAsVariable();
        long long l = checkInst->getOperand(1)->getAsNumber();
        long long r = checkInst->getOperand(2)->getAsNumber();

        results[checkInst] = ResultType::UNREACHABLE;
    }
}

States IntervalAnalysis::iniStates() {
    // You can modify this function arbitrarily
    States states;
    for (auto inst : insts) {
        for (size_t i = 0; i < inst->getOperandSize(); i++) {
            IR::Value *val = inst->getOperand(i);
            if (val->isVariable()) {
                std::string varName = val->getAsVariable();
                states[varName] = Interval(); // bottom
            }
        }
    }
    // optionally change s[var] to [0,0] for all var
    // for (auto &pair : states) {
    //     pair.second.isBottom = false;
    //     pair.second.l = 0;
    //     pair.second.r = 0;
    // }
    return states;
    //
    //return States();
}

States IntervalAnalysis::transfer(IR::Inst *inst, States &input) {
    // Transfer function: compute output states from input states for a single inst
    States out = input; // copy input by default

    auto getIv = [&](IR::Value *v) -> Interval {
        if (v->isNumber()) {
            Interval iv;
            iv.isBottom = false;
            iv.l = iv.r = v->getAsNumber();
            // clamp to [0,255]
            if (iv.l < 0) iv.l = 0;
            if (iv.r < 0) iv.r = 0;
            if (iv.l > 255) iv.l = 255;
            if (iv.r > 255) iv.r = 255;
            return iv;
        }
        std::string name = v->getAsVariable();
        auto it = input.find(name);
        if (it == input.end())
            return Interval();
        return it->second;
    };

    auto clampInterval = [&](Interval &iv) {
        if (iv.isBottom) return;
        if (iv.l < 0) iv.l = 0;
        if (iv.r < 0) iv.r = 0;
        if (iv.l > 255) iv.l = 255;
        if (iv.r > 255) iv.r = 255;
    };

    auto addIv = [&](const Interval &a, const Interval &b) -> Interval {
        if (a.isBottom || b.isBottom) return Interval();
        Interval res;
        res.isBottom = false;
        long long nl = a.l + b.l;
        long long nr = a.r + b.r;
        if (nl < 0) nl = 0;
        if (nr > 255) nr = 255;
        res.l = nl;
        res.r = nr;
        return res;
    };

    auto subIv = [&](const Interval &a, const Interval &b) -> Interval {
        if (a.isBottom || b.isBottom) return Interval();
        Interval res;
        res.isBottom = false;
        long long nl = a.l - b.r;
        long long nr = a.r - b.l;
        if (nl < 0) nl = 0;
        if (nr > 255) nr = 255;
        res.l = nl;
        res.r = nr;
        return res;
    };

    switch (inst->getInstType()) {
        case IR::InstType::InputInst: {
            // operand0 is destination variable
            IR::Value *dstVal = inst->getOperand(0);
            std::string dst = dstVal->getAsVariable();
            Interval iv;
            iv.isBottom = false;
            iv.l = 0;
            iv.r = 255;
            out[dst] = iv;
            break;
        }
        case IR::InstType::AssignInst: {
            IR::Value *dstVal = inst->getOperand(0);
            IR::Value *srcVal = inst->getOperand(1);
            std::string dst = dstVal->getAsVariable();
            Interval rhs = getIv(srcVal);
            out[dst] = rhs;
            break;
        }
        case IR::InstType::AddInst: {
            IR::Value *dstVal = inst->getOperand(0);
            IR::Value *leftVal = inst->getOperand(1);
            IR::Value *rightVal = inst->getOperand(2);
            std::string dst = dstVal->getAsVariable();
            Interval leftIv = getIv(leftVal);
            Interval rightIv = getIv(rightVal);
            Interval res = addIv(leftIv, rightIv);
            clampInterval(res);
            out[dst] = res;
            break;
        }
        case IR::InstType::SubInst: {
            IR::Value *dstVal = inst->getOperand(0);
            IR::Value *leftVal = inst->getOperand(1);
            IR::Value *rightVal = inst->getOperand(2);
            std::string dst = dstVal->getAsVariable();
            Interval leftIv = getIv(leftVal);
            Interval rightIv = getIv(rightVal);
            Interval res = subIv(leftIv, rightIv);
            clampInterval(res);
            out[dst] = res;
            break;
        }
        case IR::InstType::CheckIntervalInst:
        case IR::InstType::IfInst:
        case IR::InstType::GotoInst:
        case IR::InstType::LabelInst:
        case IR::InstType::CallInst:
        default:
            // by default, do not change states
            break;
    }

    return out;
}

bool IntervalAnalysis::joinInto(const States &x, States &y) {
    // You can modify this function arbitrarily
    bool changed = false;
    for (const auto &pair : x) {
        const std::string &varName = pair.first;
        const Interval &xInterval = pair.second;
        Interval &yInterval = y[varName];
        if (yInterval.isBottom) {
            yInterval = xInterval;
            changed = true;
        } else if (!xInterval.isBottom) {
            long long newL = std::min(yInterval.l, xInterval.l);
            long long newR = std::max(yInterval.r, xInterval.r);
            if (newL != yInterval.l || newR != yInterval.r) {
                yInterval.l = newL;
                yInterval.r = newR;
                changed = true;
            }
        }
    }
    return changed;
    //
    // return true;
}

void IntervalAnalysis::addSuccessors(size_t nowLabel, States outputState) {
    // Safely retrieve the Inst* corresponding to nowLabel.
    // `nowLabel` is a label value (not necessarily a direct index into `insts`),
    // so do not index `insts` with it directly to avoid out-of-range access.
    fdlang::IR::Inst *inst = nullptr;
    if (nowLabel < insts.size()) {
        // fast path: treat nowLabel as index
        if (insts[nowLabel] && insts[nowLabel]->getLabel() == nowLabel)
            inst = insts[nowLabel];
    }
    if (!inst) {
        // fallback: search for the instruction whose label equals nowLabel
        for (auto cand : insts) {
            if (cand && cand->getLabel() == nowLabel) {
                inst = cand;
                break;
            }
        }
    }

    if (!inst) {
        // couldn't find the instruction for the given label; nothing to do
        return;
    }

    for (auto sucInst : inst->getSuccessors()) {
        if (!sucInst) continue;
        size_t sucLabel = sucInst->getLabel();
        States &sucInputState = inputStates[sucLabel];
        if (joinInto(outputState, sucInputState)) {
            worklist.push(sucLabel);
        }
    }
}