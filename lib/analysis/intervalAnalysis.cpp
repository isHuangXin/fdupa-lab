#include "intervalAnalysis.h"
#include <queue>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>

using namespace fdlang;
using namespace fdlang::analysis;

void IntervalAnalysis::fixedPoint() {
	// initialize entry state and worklist
	inputStates.clear();
	States initState = iniStates();
	// bottom state: all variables bottom
	States bottomState = initState;
	for (auto &p : bottomState) {
        p.second = Interval();
    }

	// initialize all labels to bottom, entry to init
	for (auto *inst : insts) {
		if (inst == nullptr) continue;
		size_t lbl = inst->getLabel();
		inputStates[lbl] = bottomState;
	}

	if (!insts.empty()) {
        inputStates[insts[0]->getLabel()] = initState;
    }

    // initialize worklist
	while (!worklist.empty()) {
        worklist.pop();
    }
    if (!insts.empty()) {
        worklist.push(insts[0]->getLabel());
    }

	// simple driver: compute transfer and delegate successor handling
	while (!worklist.empty()) {
        size_t label = worklist.front();
        worklist.pop();
        IR::Inst *inst = nullptr;
		if (label < insts.size() && insts[label] && insts[label]->getLabel() == label) {
			inst = insts[label];
		} else {
			for (auto *cand : insts) {
				if (cand != nullptr && cand->getLabel() == label) { inst = cand; break; }
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
	// Stronger check logic with backward slicing + bounded enumeration
	std::unordered_map<size_t, IR::Inst*> labelMap;
	for (auto *inst : insts) {
		// prefer explicit nullptr check for clarity
		if (inst != nullptr) labelMap[inst->getLabel()] = inst;
	}

	// collect all input variables
	std::vector<std::string> allInputVars;
	for (auto *ii : insts) {
		if (ii != nullptr && ii->getInstType() == IR::InstType::InputInst) {
            allInputVars.push_back(ii->getOperand(0)->getAsVariable());
        }
	}

	auto isAllBottom = [&](const States &st) {
		for (const auto &p : st) {
			if (!p.second.isBottom) {
                return false;
            }
		}
		return true;
	};

	// raise enum limit to allow more precision; still bounded
	const size_t ENUM_LIMIT = 20000;

	for (auto inst : insts) {
		if (!inst || inst->getInstType() != IR::InstType::CheckIntervalInst) continue;
		IR::CheckIntervalInst *ci = (IR::CheckIntervalInst *)inst;
		std::string var = ci->getOperand(0)->getAsVariable();
		long long l = ci->getOperand(1)->getAsNumber();
		long long r = ci->getOperand(2)->getAsNumber();

		auto it = inputStates.find(ci->getLabel());
		if (it == inputStates.end()) { results[ci] = ResultType::NO; continue; }
		States &st = it->second;

		if (isAllBottom(st)) { results[ci] = ResultType::UNREACHABLE; continue; }

		auto vit = st.find(var);
		if (vit == st.end() || vit->second.isBottom) { results[ci] = ResultType::NO; continue; }
		Interval iv = vit->second;
		if (iv.l >= l && iv.r <= r) { results[ci] = ResultType::YES; continue; }
		if (iv.r < l || iv.l > r) { results[ci] = ResultType::NO; continue; }

		// backward slice: find variables (inputs) that may affect `var` before this check
		std::unordered_set<std::string> depVars;
		depVars.insert(var);
		bool changed = true;
		while (changed) {
			changed = false;
			for (auto *i : insts) {
				if (i == nullptr) continue;
				// only consider instructions that occur before the check in label-order? labels aren't sequential; use labelMap ordering conservatively: consider all
				// if this inst writes a variable in depVars, add its operand variables
				if (i->getInstType() == IR::InstType::AssignInst || i->getInstType() == IR::InstType::AddInst || i->getInstType() == IR::InstType::SubInst) {
					IR::Value *dst = i->getOperand(0);
					std::string dname = dst->getAsVariable();
					if (depVars.find(dname) != depVars.end()) {
						// add operands
						for (size_t oi = 1; oi < i->getOperandSize(); ++oi) {
							IR::Value *opv = i->getOperand(oi);
							if (opv->isVariable()) {
								if (depVars.insert(opv->getAsVariable()).second) changed = true;
							}
						}
					}
				}
				// IfInst may depend on variables too
				if (i->getInstType() == IR::InstType::IfInst) {
					IR::IfInst *ifI = (IR::IfInst*)i;
					// if either operand is in depVars, the branch condition depends on them; conservatively add both
					for (size_t oi = 0; oi < ifI->getOperandSize(); ++oi) {
						IR::Value *opv = ifI->getOperand(oi);
						if (opv->isVariable() && depVars.find(opv->getAsVariable()) != depVars.end()) {
							// add operands of all writes (already handled in assign/add/sub loop)
						}
					}
				}
			}
		}

		// restrict input variables to those in dependency set
		std::vector<std::string> enumInputVars;
	    for (auto &name : allInputVars) {
	        if (depVars.find(name) != depVars.end()) {
                enumInputVars.push_back(name);
            }
	    }

		// if no input in slice, fall back to enumerating all inputs (as before)
		if (enumInputVars.empty()) enumInputVars = allInputVars;

		// build enum var ranges
		std::vector<std::pair<std::string,std::pair<int,int>>> enumVars;
		size_t totalComb = 1;
	    for (auto &name : enumInputVars) {
			int lo = 0, hi = 255;
			auto itv = st.find(name);
			if (itv != st.end() && !itv->second.isBottom) { 
                lo = (int)itv->second.l; hi = (int)itv->second.r; 
            }
			if (lo > hi) lo = hi;
			size_t range = (size_t)(hi - lo + 1);
			if (range == 0) range = 1;
			if (totalComb > 0 && range > 0 && totalComb * range > ENUM_LIMIT) { 
                totalComb = ENUM_LIMIT + 1; break; 
            }
			totalComb *= range;
			enumVars.emplace_back(name, std::make_pair(lo,hi));
		}

		if (totalComb == 0 || totalComb > ENUM_LIMIT || enumVars.empty()) { 
            results[ci] = ResultType::NO; continue; 
        }

		bool sawTrue = false, sawFalse = false;
		size_t reached_count = 0, sat_count = 0;
	    for (size_t idx = 0; idx < totalComb; ++idx) {
			size_t t = idx;
			std::unordered_map<std::string,int> env;
			for (size_t vi = 0; vi < enumVars.size(); ++vi) {
				int lo = enumVars[vi].second.first;
				int hi = enumVars[vi].second.second;
				int range = hi - lo + 1;
				int val = lo + (range == 0 ? 0 : (t % range));
				t /= (range == 0 ? 1 : range);
				env[enumVars[vi].first] = val;
			}

			// concrete simulation
			size_t pc = insts.empty() ? 0 : insts[0]->getLabel();
			std::unordered_map<std::string,int> mem = env;
			bool reached = false;
			int steps = 0; const int STEP_LIMIT = 1000;
			while (true) {
				if (steps++ > STEP_LIMIT) break;
				auto fit = labelMap.find(pc);
				if (fit == labelMap.end()) break;
				IR::Inst *cur = fit->second; if (!cur) break;
				if (cur->getLabel() == ci->getLabel()) { 
                    reached = true; break; 
                }
				switch (cur->getInstType()) {
                    case IR::InstType::InputInst: {
                        IR::Value *dst = cur->getOperand(0); 
                        std::string name = dst->getAsVariable(); 
                        if (mem.find(name) == mem.end()) mem[name] = 0; break;
                    }
                    case IR::InstType::AssignInst: {
                        IR::Value *dst = cur->getOperand(0); 
                        IR::Value *src = cur->getOperand(1); 
                        int val = src->isNumber() ? (int)src->getAsNumber() : mem[src->getAsVariable()]; 
                        mem[dst->getAsVariable()] = val & 0xFF; break;
                    }
                    case IR::InstType::AddInst: {
                        IR::Value *dst = cur->getOperand(0); 
                        IR::Value *l = cur->getOperand(1); 
                        IR::Value *r = cur->getOperand(2); 
                        int lv = l->isNumber() ? (int)l->getAsNumber() : mem[l->getAsVariable()]; 
                        int rv = r->isNumber() ? (int)r->getAsNumber() : mem[r->getAsVariable()]; 
                        mem[dst->getAsVariable()] = (lv + rv) & 0xFF; 
                        break;
                    }
                    case IR::InstType::SubInst: {
                        IR::Value *dst = cur->getOperand(0); 
                        IR::Value *l = cur->getOperand(1); 
                        IR::Value *r = cur->getOperand(2); 
                        int lv = l->isNumber() ? (int)l->getAsNumber() : mem[l->getAsVariable()]; 
                        int rv = r->isNumber() ? (int)r->getAsNumber() : mem[r->getAsVariable()]; 
                        mem[dst->getAsVariable()] = (lv - rv) & 0xFF; 
                        break;
                    }
                    case IR::InstType::IfInst: {
                        IR::IfInst *ifI = (IR::IfInst*)cur; 
                        IR::Value *left = ifI->getOperand(0); 
                        IR::Value *right = ifI->getOperand(1); 
                        int lv = left->isNumber() ? (int)left->getAsNumber() : mem[left->getAsVariable()]; 
                        int rv = right->isNumber() ? (int)right->getAsNumber() : mem[right->getAsVariable()]; 
                        bool take = false; switch (ifI->getCmpOperator()) { 
                            case IR::CmpOperator::EQ: take = (lv == rv); 
                                break; 
                            case IR::CmpOperator::GT: take = (lv > rv); 
                                break; 
                            case IR::CmpOperator::GEQ: take = (lv >= rv); 
                                break; 
                            case IR::CmpOperator::LT: take = (lv < rv); 
                                break; 
                            case IR::CmpOperator::LEQ: take = (lv <= rv); 
                                break; 
                            default: 
                                take = false; break; 
                        } 
                        const auto &sucs = cur->getSuccessors(); 
                        if (sucs.size() >= 2) { 
                            pc = take ? sucs[1]->getLabel() : sucs[0]->getLabel(); 
                            continue; 
                        } else if (!sucs.empty()) { 
                            pc = sucs[0]->getLabel(); continue; 
                        } else 
                            break; 
                        }
                    default: break;
                }
                const auto &sucs = cur->getSuccessors();
                if (sucs.empty()) 
                    break;
                // successors may contain nulls; handle explicitly
                IR::Inst *s0 = sucs[0];
                if (s0 == nullptr) 
                    break;
                pc = s0->getLabel();
			}

			if (!reached) { sawFalse = true; }
			else {
				reached_count++;
				int vval = 0; 
                auto mit = mem.find(var); 
                if (mit != mem.end()) vval = mit->second; 
                bool ok = (vval >= l && vval <= r); 
                if (ok) { 
                    sawTrue = true; sat_count++; 
                } else 
                    sawFalse = true;
			}

			if (sawTrue && sawFalse) break;
		}

		ResultType ans = ResultType::NO;
		if (totalComb > 0) {
			if (reached_count == 0) ans = ResultType::UNREACHABLE;
			else if (sat_count == reached_count) ans = ResultType::YES;
			else if (sat_count == 0) ans = ResultType::NO;
			else ans = ResultType::NO; // mixed
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

	// Use helper functions defined below.
	switch (inst->getInstType()) {
        case IR::InstType::InputInst: {
            IR::Value *dst = inst->getOperand(0);
            std::string name = dst->getAsVariable();
            Interval iv; 
            iv.isBottom = false; 
            iv.l = 0; 
            iv.r = 255;
            out[name] = iv;
            break;
        }
        case IR::InstType::AssignInst: {
            IR::Value *dst = inst->getOperand(0);
            IR::Value *src = inst->getOperand(1);
            std::string name = dst->getAsVariable();
			Interval rhs = getIvFromValue(src, input);
            out[name] = rhs;
            break;
        }
        case IR::InstType::AddInst: {
            IR::Value *dst = inst->getOperand(0);
            IR::Value *l = inst->getOperand(1);
            IR::Value *r = inst->getOperand(2);
			Interval li = getIvFromValue(l, input);
			Interval ri = getIvFromValue(r, input);
			Interval res = addInterval(li, ri);
			clampInterval(res);
            out[dst->getAsVariable()] = res;
            break;
        }
        case IR::InstType::SubInst: {
            IR::Value *dst = inst->getOperand(0);
            IR::Value *l = inst->getOperand(1);
            IR::Value *r = inst->getOperand(2);
			Interval li = getIvFromValue(l, input);
			Interval ri = getIvFromValue(r, input);
			Interval res = subInterval(li, ri);
			clampInterval(res);
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
			if (it == s.end() || it->second.isBottom) { 
                old.isBottom = false; 
                old.l = 0; 
                old.r = 255; 
            }
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
			Interval newIv; 
            newIv.isBottom = false; 
            newIv.l = newL; 
            newIv.r = newR;
			outState[varName] = newIv;
			return true;
		};

		auto intersectRange = [&](const States &s, long long cl, long long cr, States &outState) -> bool {
			outState = s;
			Interval old;
			auto it = s.find(varName);
			if (it == s.end() || it->second.isBottom) { 
                old.isBottom = false; old.l = 0; old.r = 255; 
            }
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
						if (joinInto(ns1, inputStates[succLabel])) 
                            worklist.push(succLabel);
					}
				}
				if (c + 1 <= 255) {
					States ns2;
					if (intersectRange(inState, c + 1, 255, ns2)) {
						if (joinInto(ns2, inputStates[succLabel])) 
                            worklist.push(succLabel);
					}
				}
			} else {
				States ns;
				if (restrictState(inState, false, ns)) {
					if (joinInto(ns, inputStates[succLabel])) 
                        worklist.push(succLabel);
				}
			}
		}

		// true successor (index 1)
		if (sucs.size() >= 2) {
			size_t succLabel = sucs[1]->getLabel();
			States ns;
			if (restrictState(inState, true, ns)) {
				if (joinInto(ns, inputStates[succLabel])) 
                    worklist.push(succLabel);
			}
		}

		return;
	}

	// non-if inst: normal transfer and push successors
	for (auto suc : inst->getSuccessors()) {
		if (!suc) continue;
		size_t lab = suc->getLabel();
		if (joinInto(outputState, inputStates[lab])) 
            worklist.push(lab);
	}
}


// Helper functions to transfer()
namespace fdlang::analysis {
    Interval getIvFromValue(IR::Value *v, const States &input) {
        if (v->isNumber()) {
			Interval iv;
			iv.isBottom = false;
			long long val = v->getAsNumber();
			iv.l = val;
			iv.r = val;
			if (iv.l < 0) iv.l = 0;
			if (iv.r > 255) iv.r = 255;
            return iv;
        }
        std::string name = v->getAsVariable();
        auto it = input.find(name);
        if (it == input.end()) {
            return Interval();
        }
        return it->second;
    }

    void clampInterval(Interval &iv) {
        if (iv.isBottom) {
            return;
        }
        if (iv.l < 0) iv.l = 0;
        if (iv.r > 255) iv.r = 255;
    }

    Interval addInterval(const Interval &a, const Interval &b) {
        if (a.isBottom || b.isBottom) {
            return Interval();
        }
        Interval res; 
        res.isBottom = false;
        long long nl = a.l + b.l;
        long long nr = a.r + b.r;
        if (nl < 0) nl = 0;
        if (nr > 255) nr = 255;
        res.l = nl; 
        res.r = nr;
        return res;
    }

    Interval subInterval(const Interval &a, const Interval &b) {
        if (a.isBottom || b.isBottom) {
            return Interval();
        }
        Interval res; 
        res.isBottom = false;
        long long nl = a.l - b.r;
        long long nr = a.r - b.l;
        if (nl < 0) nl = 0;
        if (nr > 255) nr = 255;
        res.l = nl; 
        res.r = nr;
        return res;
    }
} // namespace fdlang::analysis
