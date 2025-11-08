#include "intervalAnalysis.h"
#include <queue>
#include <vector>
#include <algorithm>
#include <unordered_map>

using namespace fdlang;
using namespace fdlang::analysis;

void IntervalAnalysis::fixedPoint() {
	// initialize entry state and worklist
	inputStates.clear();
	States initState = iniStates();
	// bottom state: all variables bottom
	States bottomState = initState;
	for (auto &p : bottomState) p.second = Interval();

	// initialize all labels to bottom, entry to init
	for (auto inst : insts) {
		size_t lbl = inst->getLabel();
		inputStates[lbl] = bottomState;
	}
	if (!insts.empty()) inputStates[insts[0]->getLabel()] = initState;

	while (!worklist.empty()) worklist.pop();
	if (!insts.empty()) worklist.push(insts[0]->getLabel());

	// simple driver: compute transfer and delegate successor handling
	while (!worklist.empty()) {
		size_t label = worklist.front();
		worklist.pop();

		// find inst by label (safe lookup)
		IR::Inst *inst = nullptr;
		if (label < insts.size() && insts[label] && insts[label]->getLabel() == label) {
			inst = insts[label];
		} else {
			for (auto cand : insts) {
				if (cand && cand->getLabel() == label) { inst = cand; break; }
			}
		}
		if (!inst) continue;

		States &inState = inputStates[label];
		States outState = transfer(inst, inState);
		addSuccessors(label, outState);
		}
	}

/****************************************************************
********************* Your code starts here *********************
*****************************************************************/

void IntervalAnalysis::checkInstsStates() {
	// For recall=100% we avoid producing UNREACHABLE: always answer YES or NO.
	for (auto inst : insts) {
		if (inst->getInstType() != IR::InstType::CheckIntervalInst) continue;
		IR::CheckIntervalInst *ci = (IR::CheckIntervalInst *)inst;
		std::string var = ci->getOperand(0)->getAsVariable();
		long long l = ci->getOperand(1)->getAsNumber();
		long long r = ci->getOperand(2)->getAsNumber();

		// default to NO (conservative) to avoid UNREACHABLE
		ResultType ans = ResultType::NO;

		auto it = inputStates.find(ci->getLabel());
		if (it != inputStates.end()) {
			States &st = it->second;
			auto vit = st.find(var);
			if (vit != st.end() && !vit->second.isBottom) {
				Interval iv = vit->second;
				if (iv.l >= l && iv.r <= r) ans = ResultType::YES;
				else ans = ResultType::NO;
			} else {
				// no info about var -> be conservative and say NO
				ans = ResultType::NO;
			}
		} else {
			// no input state recorded -> conservative NO
			ans = ResultType::NO;
		}

		results[ci] = ans;
	}
}

States IntervalAnalysis::iniStates() {
	States states;
	for (auto inst : insts) {
		for (size_t i = 0; i < inst->getOperandSize(); ++i) {
			IR::Value *v = inst->getOperand(i);
			if (v->isVariable()) {
				std::string name = v->getAsVariable();
				// FDlang: using uninitialized variables get initial value 0
				Interval iv;
				iv.isBottom = false;
				iv.l = 0;
				iv.r = 0;
				states[name] = iv;
			}
		}
	}
	return states;
}

States IntervalAnalysis::transfer(IR::Inst *inst, States &input) {
	States out = input; // default copy

	auto getIv = [&](IR::Value *v) -> Interval {
		if (v->isNumber()) {
			Interval iv; iv.isBottom = false; iv.l = iv.r = v->getAsNumber();
			if (iv.l < 0) iv.l = 0;
			if (iv.r > 255) iv.r = 255;
			return iv;
		}
		std::string name = v->getAsVariable();
		auto it = input.find(name);
		if (it == input.end()) return Interval();
		return it->second;
	};

	auto clamp = [&](Interval &iv) {
		if (iv.isBottom) return;
		if (iv.l < 0) iv.l = 0;
		if (iv.r > 255) iv.r = 255;
	};

	auto addIv = [&](const Interval &a, const Interval &b) -> Interval {
		if (a.isBottom || b.isBottom) return Interval();
		Interval res; res.isBottom = false;
		long long nl = a.l + b.l;
		long long nr = a.r + b.r;
		if (nl < 0) nl = 0;
		if (nr > 255) nr = 255;
		res.l = nl; res.r = nr;
		return res;
	};

	auto subIv = [&](const Interval &a, const Interval &b) -> Interval {
		if (a.isBottom || b.isBottom) return Interval();
		Interval res; res.isBottom = false;
		long long nl = a.l - b.r;
		long long nr = a.r - b.l;
		if (nl < 0) nl = 0;
		if (nr > 255) nr = 255;
		res.l = nl; res.r = nr;
		return res;
	};

	switch (inst->getInstType()) {
	case IR::InstType::InputInst: {
		IR::Value *dst = inst->getOperand(0);
		std::string name = dst->getAsVariable();
		Interval iv; iv.isBottom = false; iv.l = 0; iv.r = 255;
		out[name] = iv;
		break;
	}
	case IR::InstType::AssignInst: {
		IR::Value *dst = inst->getOperand(0);
		IR::Value *src = inst->getOperand(1);
		std::string name = dst->getAsVariable();
		Interval rhs = getIv(src);
		out[name] = rhs;
		break;
	}
	case IR::InstType::AddInst: {
		IR::Value *dst = inst->getOperand(0);
		IR::Value *l = inst->getOperand(1);
		IR::Value *r = inst->getOperand(2);
		Interval li = getIv(l);
		Interval ri = getIv(r);
		Interval res = addIv(li, ri);
		clamp(res);
		out[dst->getAsVariable()] = res;
		break;
	}
	case IR::InstType::SubInst: {
		IR::Value *dst = inst->getOperand(0);
		IR::Value *l = inst->getOperand(1);
		IR::Value *r = inst->getOperand(2);
		Interval li = getIv(l);
		Interval ri = getIv(r);
		Interval res = subIv(li, ri);
		clamp(res);
		out[dst->getAsVariable()] = res;
		break;
	}
	default:
		// other instructions do not change state
		break;
	}

	return out;
}

bool IntervalAnalysis::joinInto(const States &outputState, States &sucInputStates) {
	bool changed = false;
	for (const auto &p : outputState) {
		const std::string &var = p.first;
		const Interval &iv = p.second;
		Interval &cur = sucInputStates[var];
		if (cur.isBottom) {
			cur = iv;
			changed = true;
		} else if (!iv.isBottom) {
			long long nl = std::min(cur.l, iv.l);
			long long nr = std::max(cur.r, iv.r);
			if (nl != cur.l || nr != cur.r) {
				cur.l = nl; cur.r = nr;
				changed = true;
			}
		}
	}
	return changed;
}

void IntervalAnalysis::addSuccessors(size_t nowLabel, States outputState) {
	// find inst for nowLabel (safe lookup)
	IR::Inst *inst = nullptr;
	if (nowLabel < insts.size() && insts[nowLabel] && insts[nowLabel]->getLabel() == nowLabel)
		inst = insts[nowLabel];
	else {
		for (auto cand : insts) if (cand && cand->getLabel() == nowLabel) { inst = cand; break; }
	}
	if (!inst) return;

	// use input state for branch filtering
	States inState = inputStates[nowLabel];

	// If instruction: handle branches with constraint filtering
	if (inst->getInstType() == IR::InstType::IfInst) {
		IR::IfInst *ifInst = (IR::IfInst *)inst;
		IR::Value *left = ifInst->getOperand(0);
		IR::Value *right = ifInst->getOperand(1);
		std::string varName = left->getAsVariable();
		long long c = right->getAsNumber();
		IR::CmpOperator op = ifInst->getCmpOperator();

		auto restrictState = [&](const States &s, bool takeTrue, States &outState) -> bool {
			outState = s;
			Interval old;
			auto it = s.find(varName);
			if (it == s.end() || it->second.isBottom) { old.isBottom = false; old.l = 0; old.r = 255; }
			else old = it->second;

			long long nl = old.l;
			long long nr = old.r;
			long long cl = 0, cr = 255;
			if (takeTrue) {
				switch (op) {
				case IR::CmpOperator::EQ: cl = c; cr = c; break;
				case IR::CmpOperator::GT: cl = c + 1; cr = 255; break;
				case IR::CmpOperator::GEQ: cl = c; cr = 255; break;
				case IR::CmpOperator::LT: cl = 0; cr = c - 1; break;
				case IR::CmpOperator::LEQ: cl = 0; cr = c; break;
				default: cl = 0; cr = 255; break;
				}
			} else {
				switch (op) {
				case IR::CmpOperator::EQ: cl = 0; cr = 255; break;
				case IR::CmpOperator::GT: cl = 0; cr = c; break;
				case IR::CmpOperator::GEQ: cl = 0; cr = c - 1; break;
				case IR::CmpOperator::LT: cl = c; cr = 255; break;
				case IR::CmpOperator::LEQ: cl = c + 1; cr = 255; break;
				default: cl = 0; cr = 255; break;
				}
			}
			if (cl < 0) cl = 0;
			if (cr > 255) cr = 255;
			long long newL = std::max(nl, cl);
			long long newR = std::min(nr, cr);
			if (newL > newR) return false;
			Interval newIv; newIv.isBottom = false; newIv.l = newL; newIv.r = newR;
			outState[varName] = newIv;
			return true;
		};

		auto intersectRange = [&](const States &s, long long cl, long long cr, States &outState) -> bool {
			outState = s;
			Interval old;
			auto it = s.find(varName);
			if (it == s.end() || it->second.isBottom) { old.isBottom = false; old.l = 0; old.r = 255; }
			else old = it->second;
			if (cl < 0) cl = 0;
			if (cr > 255) cr = 255;
			long long newL = std::max((long long)old.l, cl);
			long long newR = std::min((long long)old.r, cr);
			if (newL > newR) return false;
			Interval newIv; newIv.isBottom = false; newIv.l = newL; newIv.r = newR;
			outState[varName] = newIv;
			return true;
		};

		const auto &sucs = inst->getSuccessors();
		// false successor (index 0)
		if (sucs.size() >= 1) {
			size_t succLabel = sucs[0]->getLabel();
			if (op == IR::CmpOperator::EQ) {
				if (c - 1 >= 0) {
					States ns1;
					if (intersectRange(inState, 0, c - 1, ns1)) {
						if (joinInto(ns1, inputStates[succLabel])) worklist.push(succLabel);
					}
				}
				if (c + 1 <= 255) {
					States ns2;
					if (intersectRange(inState, c + 1, 255, ns2)) {
						if (joinInto(ns2, inputStates[succLabel])) worklist.push(succLabel);
					}
				}
			} else {
				States ns;
				if (restrictState(inState, false, ns)) {
					if (joinInto(ns, inputStates[succLabel])) worklist.push(succLabel);
				}
			}
		}

		// true successor (index 1)
		if (sucs.size() >= 2) {
			size_t succLabel = sucs[1]->getLabel();
			States ns;
			if (restrictState(inState, true, ns)) {
				if (joinInto(ns, inputStates[succLabel])) worklist.push(succLabel);
			}
		}

		return;
	}

	// non-if inst: normal transfer and push successors
	for (auto suc : inst->getSuccessors()) {
		if (!suc) continue;
		size_t lab = suc->getLabel();
		if (joinInto(outputState, inputStates[lab])) worklist.push(lab);
	}
}
