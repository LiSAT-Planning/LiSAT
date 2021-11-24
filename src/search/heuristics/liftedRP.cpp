//
// Created by Daniel Höller on 27.08.21.
//

#include "liftedRP.h"
#include "sat_encoder.h"
#include "ipasir.h"
#include "../action.h"
#include "../search_engines/utils.h"
#include <unordered_set>
#include <cassert>
#include <chrono>

using namespace std;

liftedRP::liftedRP(const Task task) {
    numActions = task.actions.size();
    numObjs = task.objects.size();

	map<int,int> maxNum;
	map<int,int> objCount;

    for (auto a: task.actions) {
        maxArity = max(maxArity, (int) a.get_parameters().size());
        maxPrec = max(maxPrec, (int) a.get_precondition().size());
		
		map<int,int> thisCount;
		for (auto para : a.get_parameters())
			thisCount[para.type] += 1;

		for (auto p : thisCount)
			if (maxNum[p.first] < p.second)
				maxNum[p.first] = p.second;
    }
    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++)
			objCount[oTypes[i]] += 1;
	}

	int ss = 0;
	for (auto p : maxNum){
		cout << "T " << setw(2) << p.first << " # " << setw(2) << p.second << " size " << setw(3) << objCount[p.first] << endl;
		ss += p.second;
	}
	cout << "Max Arity: " << maxArity << " diffSum: " << ss << endl; 
	//exit(0);
    
    cout << "- re-inferring type hierarchy..." << endl;
    int numTypes = task.type_names.size();
    types = new unordered_set<int>[numTypes];
    for (tSize obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (tSize i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            types[j].insert(obj);
        }
    }
    unordered_set<int> parents[numTypes]; // todo: equal sets
    for (int child = 0; child < numTypes; child++) {
        for (int parent = 0; parent < numTypes; parent++) {
            if (child == parent) continue;
            if (types[child].size() <= types[parent].size()) {
                bool isSubset = true;
                for (int elem: types[child]) {
                    if (types[parent].find(elem) == types[parent].end()) {
                        isSubset = false;
                        break;
                    }
                }
                if (isSubset) {
                    parents[child].insert(parent);
                }
            }
        }
    }

    // create data structure for nullary precs/effects -> from bitmap to iterable set
    for (tSize a = 0; a < task.actions.size(); a++) {
        setPosNullaryPrec.push_back(new unordered_set<int>);
        setNegNullaryPrec.push_back(new unordered_set<int>);
        setPosNullaryEff.push_back(new unordered_set<int>);
        setNegNullaryEff.push_back(new unordered_set<int>);

        auto posPrec = task.actions[a].get_positive_nullary_precond();
        for (tSize f = 0; f < posPrec.size(); f++) {
            if (posPrec[f]) {
                setPosNullaryPrec[a]->insert(f);
            }
        }
        auto negPrec = task.actions[a].get_negative_nullary_precond();
        for (tSize f = 0; f < negPrec.size(); f++) {
            if (negPrec[f]) {
                setNegNullaryPrec[a]->insert(f);
            }
        }
        auto posEff = task.actions[a].get_positive_nullary_effects();
        for (tSize f = 0; f < posEff.size(); f++) {
            if (posEff[f]) {
                setPosNullaryEff[a]->insert(f);
				nullaryAchiever[f].push_back(a);
            }
        }
        auto negEff = task.actions[a].get_negative_nullary_effects();
        for (tSize f = 0; f < negEff.size(); f++) {
            if (negEff[f]) {
                setNegNullaryEff[a]->insert(f);
				nullaryDestroyer[f].push_back(a);
            }
        }
    }

    cout << "- building achiever lookup tables..." << endl;
    // !!! this code assumes the non-sparse (i.e. transitively closed) typing !!!
    for (tSize iAction = 0; iAction < task.actions.size(); iAction++) {
        auto consumer = task.actions[iAction];
        achievers.push_back(new ActionPrecAchievers);
        const auto precs = consumer.get_precondition();
        for (tSize iPrec = 0; iPrec < precs.size(); iPrec++) {
            achievers[iAction]->precAchievers.push_back(new ActionPrecAchiever);
            const auto prec = precs[iPrec];
            // check for this single prec which other actions can achieve it. need to check
            // - predicate
            // - typing of the specific parameters
            for (tSize iPosAch = 0; iPosAch < task.actions.size(); iPosAch++) {
                auto posAchAction = task.actions[iPosAch];
                for (tSize ie = 0; ie < posAchAction.get_effects().size(); ie++) {
                    auto eff = posAchAction.get_effects()[ie];
                    if (eff.predicate_symbol == prec.predicate_symbol) {
                        /* ** check typing **
                         * what shall be excluded is that the predicate is defined on consumer
                         * parent type, but the effect and the precondition are siblings
                         *
                         * example: In consumer transport domain, consumer locatable object may be consumer
                         * transporter or consumer package. The "at" predicate may be defined
                         * on "locatable"s. However, the "at" predicate of consumer package
                         * cannot be fulfilled with consumer drive action.
                         */
                        bool typesCompatible = true;
                        for (tSize iArg = 0; iArg < prec.arguments.size(); iArg++) {
                            int varP = prec.arguments[iArg].index;
                            int varE = eff.arguments[iArg].index;
                            const bool pIsConst = prec.arguments[iArg].constant;
                            const bool eIsConst = eff.arguments[iArg].constant;
                            if (pIsConst && eIsConst) {
                                if (varP == varE) {
                                    continue;
                                }
                            } else if (pIsConst) {
                                int typeE = posAchAction.get_parameters()[varE].type;
                                if (types[typeE].find(varP) != types[typeE].end()) {
                                    continue;
                                }
                            } else if (eIsConst) {
                                int typeP = consumer.get_parameters()[varP].type;
                                if (types[typeP].find(varE) != types[typeP].end()) {
                                    continue;
                                }
                            } else {
                                int typeP = consumer.get_parameters()[varP].type;
                                int typeE = posAchAction.get_parameters()[varE].type;
                                if (typeP == typeE) continue;
                                if (parents[typeP].find(typeE) != parents[typeP].end()) continue;
                                if (parents[typeE].find(typeP) != parents[typeE].end()) continue;
                            }
                            typesCompatible = false;
                            break;
                        }
                        if (typesCompatible) {
                            Achiever *ach = new Achiever;
                            ach->action = iPosAch;
                            ach->effect = ie;
                            for (tSize ip = 0; ip < eff.arguments.size(); ip++) {
                                auto args = eff.arguments[ip];
                                if (!args.constant) {
                                    ach->params.push_back(args.index);
                                } else {
                                    ach->params.push_back((args.index + 1) * -1);
                                }
                            }
                            if (eff.negated == prec.negated) {
                                achievers[iAction]->precAchievers[iPrec]->achievers.push_back(ach);
                            } else {
                                achievers[iAction]->precAchievers[iPrec]->destroyers.push_back(ach);
                            }
                        }
                    }
                }
            }
        }
        for (int posPrec: *setPosNullaryPrec[iAction]) {
            achievers[iAction]->posNullaryPrecAchievers[posPrec] = new ActionPrecAchiever;
            for (tSize iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
                auto possAchAction = task.actions[iPossibleAch];
                if (possAchAction.get_positive_nullary_effects()[posPrec]) {
                    Achiever *ach = new Achiever;
                    ach->action = iPossibleAch;
                    achievers[iAction]->posNullaryPrecAchievers[posPrec]->achievers.push_back(ach);
                }
            }
        }
        for (int negPrec: *setNegNullaryPrec[iAction]) {
            achievers[iAction]->negNullaryPrecAchievers[negPrec] = new ActionPrecAchiever;
            for (tSize iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
                auto possAchAction = task.actions[iPossibleAch];
                if (possAchAction.get_negative_nullary_effects()[negPrec]) {
                    Achiever *ach = new Achiever;
                    ach->action = iPossibleAch;
                    achievers[iAction]->negNullaryPrecAchievers[negPrec]->achievers.push_back(ach);
                }
            }
        }
    }

    // same for goals
    goalAchievers = new ActionPrecAchievers;
    for (tSize iGoal = 0; iGoal < task.goal.goal.size(); iGoal++) {
        AtomicGoal goal = task.goal.goal[iGoal];
        goalAchievers->precAchievers.push_back(new ActionPrecAchiever);
        for (tSize iPosAch = 0; iPosAch < task.actions.size(); iPosAch++) {
            auto posAchAction = task.actions[iPosAch];
            for (tSize ie = 0; ie < posAchAction.get_effects().size(); ie++) {
                auto eff = posAchAction.get_effects()[ie];
                if (eff.predicate_symbol == goal.predicate) {
                    bool typesCompatible = true;
                    for (tSize iArg = 0; iArg < goal.args.size(); iArg++) {
                        int goalObj = goal.args[iArg];
                        int varE = eff.arguments[iArg].index;
                        if (eff.arguments[iArg].constant) {
                            if (varE != goalObj) {
                                typesCompatible = false;
                                break;
                            }
                        } else {
                            int typeE = posAchAction.get_parameters()[varE].type;
                            if (types[typeE].find(goalObj) == types[typeE].end()) {
                                typesCompatible = false;
                                break;
                            }
                        }
                    }
                    if (typesCompatible) {
                        Achiever *ach = new Achiever;
                        ach->action = iPosAch;
                        ach->effect = ie;
                        for (tSize ip = 0; ip < eff.arguments.size(); ip++) {
                            auto args = eff.arguments[ip];
                            if (!args.constant) {
                                ach->params.push_back(args.index);
                            } else {
                                ach->params.push_back((args.index + 1) * -1);
                            }
                        }
                        if (eff.negated == goal.negated) {
                            goalAchievers->precAchievers[iGoal]->achievers.push_back(ach);
                        } else {
                            goalAchievers->precAchievers[iGoal]->destroyers.push_back(ach);
                        }
                    }
                }
            }
        }
    }
    for (int posGoal: task.goal.positive_nullary_goals) {
        goalAchievers->posNullaryPrecAchievers[posGoal] = new ActionPrecAchiever;
        for (tSize iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
            auto possAchAction = task.actions[iPossibleAch];
            if (possAchAction.get_positive_nullary_effects()[posGoal]) {
                Achiever *ach = new Achiever;
                ach->action = iPossibleAch;
                goalAchievers->posNullaryPrecAchievers[posGoal]->achievers.push_back(ach);
            }
        }
    }
    for (int negGoal: task.goal.negative_nullary_goals) {
        goalAchievers->negNullaryPrecAchievers[negGoal] = new ActionPrecAchiever;
        for (tSize iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
            auto possAchAction = task.actions[iPossibleAch];
            if (possAchAction.get_negative_nullary_effects()[negGoal]) {
                Achiever *ach = new Achiever;
                ach->action = iPossibleAch;
                goalAchievers->negNullaryPrecAchievers[negGoal]->achievers.push_back(ach);
            }
        }
    }

    DEBUG(
    for (auto pred : task.predicates) {
        cout << pred.getName();
        for(auto type: pred.getTypes()) {
            cout << " " << task.type_names[type];
        }
        cout << endl;
    });

    // typing needs to be done when the precondition predicate is less specific than the action's parameter type
    for (size_t iAct = 0; iAct < task.actions.size(); iAct++) {
        auto precs = task.actions[iAct].get_precondition();
        auto args = task.actions[iAct].get_parameters();
        for (size_t iArg = 0; iArg < args.size(); iArg++) {
            needToType[make_pair(iAct, iArg)] = true;
        }
        for (size_t iPrec = 0; iPrec < precs.size(); iPrec++) {
            auto prec = precs[iPrec];
            for (size_t iPrecArg = 0; iPrecArg < prec.arguments.size(); iPrecArg++) {
                if (!prec.arguments[iPrecArg].constant) {
                    const int var = prec.arguments[iPrecArg].index;
                    const int actionType = args[var].type;
                    const int precType = task.predicates[prec.predicate_symbol].getTypes()[iPrecArg];
                    if (parents[actionType].find(precType) == parents[actionType].end()) {
                        needToType[make_pair(iAct, var)] = false;
                    }
                }
            }
        }
	DEBUG(
        cout << "action: " << task.actions[iAct].get_name();
        for (int j = 0; j < args.size(); j++) {
            if (needToType[make_pair(iAct, j)]) {
                cout << " T";
            } else {
                cout << " F";
            }
        }
        cout << endl;);

    }

	DEBUG(
    cout << "found achievers:" << endl;
    for (tSize iAction = 0; iAction < task.actions.size(); iAction++) {
        cout << "- action '" << task.actions[iAction].get_name() << "'";
        auto precs = task.actions[iAction].get_precondition();
        int numPrecs = precs.size() + setPosNullaryPrec[iAction]->size() + setNegNullaryPrec[iAction]->size();
        cout << ", which has " << numPrecs << " preconditions" << endl;
        for (tSize iPrec = 0; iPrec < precs.size(); iPrec++) {
            cout << "  - prec: ";
            if (precs[iPrec].negated) {
                cout << "not ";
            }
            cout << "'" << task.predicates[precs[iPrec].predicate_symbol].getName() << "' achieved by";
            auto achs = achievers[iAction]->precAchievers[iPrec]->achievers;
            for (tSize iAchiever = 0; iAchiever < achs.size(); iAchiever++) {
                auto achieverAction = task.actions[achs[iAchiever]->action];
                cout << endl << "    - '" << achieverAction.get_name() << "'";
                cout << " eff: " << achs[iAchiever]->effect;
                cout << " pred: '"
                     << task.predicates[achieverAction.get_effects()[achs[iAchiever]->effect].predicate_symbol].getName()
                     << "'";
            }
            if (achs.empty()) { cout << " s0 only."; }
            cout << endl;
        }
        for (int iPrec: *setPosNullaryPrec[iAction]) {
            cout << "  - prec: nullary" << iPrec;
            auto achs = achievers[iAction]->posNullaryPrecAchievers[iPrec]->achievers;
            for (auto ach: achs) {
                auto achieverAction = task.actions[ach->action];
                cout << endl << "    - '" << achieverAction.get_name() << "'";
            }
        }
        for (int iPrec: *setNegNullaryPrec[iAction]) {
            cout << "  - prec: not nullary" << iPrec;
            auto achs = achievers[iAction]->negNullaryPrecAchievers[iPrec]->achievers;
            for (auto ach: achs) {
                auto achieverAction = task.actions[ach->action];
                cout << endl << "    - '" << achieverAction.get_name() << "'";
            }
        }
    }

    cout << "goal achievers:" << endl;
    for (tSize iGoal = 0; iGoal < task.goal.goal.size(); iGoal++) {
        cout << "- goal ";
        if (task.goal.goal[iGoal].negated) {
            cout << "not ";
        }
        cout << "'" << task.predicates[task.goal.goal[iGoal].predicate].getName() << "'";
        for (tSize iAchiever = 0; iAchiever < goalAchievers->precAchievers[iGoal]->achievers.size(); iAchiever++) {
            auto ach = goalAchievers->precAchievers[iGoal]->achievers[iAchiever];
            auto achieverAction = task.actions[ach->action];
            cout << endl << "    - '" << achieverAction.get_name() << "'";
            cout << " eff: " << ach->effect;
            cout << " pred: '" << task.predicates[achieverAction.get_effects()[ach->effect].predicate_symbol].getName()
                 << "'";
        }
        if (goalAchievers->precAchievers[iGoal]->achievers.empty()) { cout << " s0 only."; }
        cout << endl;
    }
    for (int g: task.goal.positive_nullary_goals) {
        cout << "  - prec: nullary" << g;
        auto achs = goalAchievers->posNullaryPrecAchievers[g]->achievers;
        for (auto ach: achs) {
            auto achieverAction = task.actions[ach->action];
            cout << endl << "    - '" << achieverAction.get_name() << "'";
        }
    }
    for (int g: task.goal.negative_nullary_goals) {
        cout << "  - prec: not nullary" << g;
        auto achs = goalAchievers->negNullaryPrecAchievers[g]->achievers;
        for (auto ach: achs) {
            auto achieverAction = task.actions[ach->action];
            cout << endl << "    - '" << achieverAction.get_name() << "'";
        }
    });

    // make directional if there are multiple identical types
	for (int i = 0; i < numTypes; i++) {
        for (int j = 0; j < numTypes; j++) {
            if (i == j) continue;
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(i) != parents[j].end())) {
                    parents[i].erase(parents[i].find(j));
                }
		}
	}
    
    // make sparse
	for (int i = 0; i < numTypes; i++) {
        for (int j = 0; j < numTypes; j++) {
            if (i == j) continue;
            for (int k = 0; k < numTypes; k++) {
                if ((i == k) || (j == k)) continue;
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(k) != parents[j].end())
                    && (parents[i].find(k) != parents[i].end())) {
                    parents[i].erase(parents[i].find(k));
                }
            }
        }
    }

	DEBUG(
    for (int i = 0; i < numTypes; i++) {
        cout << task.type_names[i] << " -> {";
        bool first = true;
        for (auto p : parents[i]) {
            if (first) {
                first = false;
            } else {
                cout << ", ";
            }
            cout << task.type_names[p];
        }
        cout << "}" << endl;
    });

    children = new unordered_set<int>[numTypes];
    toptypes = new unordered_set<int>;
    for (int i = 0; i < numTypes; i++) {
        if (parents[i].size() == 0) {
            toptypes->insert(i);
        } else {
            for (int p: parents[i]) {
                children[p].insert(i);
                //ps[i].insert(p);
            }
        }
    }

    // sort obj such that objects of same parent type are adjacent
    upperTindex = new int[numTypes];
    lowerTindex = new int[numTypes];
    objToIndex = new int[numObjs];
    indexToObj = new int[numObjs];

    int r = 0;
    for (int t: *toptypes) {
        r = sortObjs(r, t);
    }

	DEBUG(
    for (tSize i = 0; i < task.objects.size(); i++) {
        cout << task.objects[i].getName() << " ";
    }
    cout << endl;

    for (int i = 0; i < numTypes; i++) {
        cout << task.type_names[i] << ":\t" << lowerTindex[i] << "-" << upperTindex[i] << " = {";
        for (int j = lowerTindex[i]; j <= upperTindex[i]; j++) {
            if (j > lowerTindex[i]) {
                cout << ", ";
            }
            int k = indexToObj[j];
            cout << task.objects[k].getName();
        }
        cout << "}" << endl;
    }
	);

    cout << "- num actions " << numActions << endl;
    cout << "- num objects " << numObjs << endl;
    cout << "- max arity " << maxArity << endl;

    for (tSize i = 0; i < task.predicates.size(); i++) {
        cout << i << " " << task.predicates[i].getName() << endl;
    }

	DEBUG(
    cout << endl << "Initial state (static):" << endl;
    for (tSize i = 0; i < task.get_static_info().get_relations().size(); i++) {
        auto rel = task.get_static_info().get_relations()[i];
        auto tuple = task.get_static_info().get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            cout << "(" << task.predicates[task.get_static_info().get_relations()[i].predicate_symbol].getName();
            for (int obj: groundA) {
                cout << " " << task.objects[obj].getName();
            }
            cout << ")" << endl;
        }
    }

    cout << endl << "Initial state (non-static):" << endl;
    for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
        auto rel = task.initial_state.get_relations()[i];
        auto tuple = task.initial_state.get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            cout << "(" << task.predicates[task.initial_state.get_relations()[i].predicate_symbol].getName();
            for (int obj: groundA) {
                cout << " " << task.objects[obj].getName();
            }
            cout << ")" << endl;
        }
    }
	);
}


bool satMode = true;

void printVariableTruth(void* solver, sat_capsule & capsule){
	for (int v = 1; v <= capsule.number_of_variables; v++){
		int val = ipasir_val(solver,v);
	
		std::string s = std::to_string(v);
		int x = 4 - s.size();
		cout << "TRUTH ";
		while (x-- && x > 0) std::cout << " ";
		std::cout << v << ": ";
		if (val > 0) std::cout << "    ";
		else         std::cout << "not ";
#ifndef NDEBUG
		std::cout << capsule.variableNames[v] << endl; 
#else
		std::cout << v << endl;
#endif
	}
}

bool liftedRP::atom_not_satisfied(const DBState &s,
                                   const AtomicGoal &atomicGoal) const {
    const auto &tuples = s.get_relations()[atomicGoal.predicate].tuples;
    const auto it = tuples.find(atomicGoal.args);
    const auto end = tuples.end();
    return (!atomicGoal.negated && it==end) || (atomicGoal.negated && it!=end);
}


vector<vector<int>> goalSupporterVars;
std::vector<std::vector<std::vector<int>>> parameterVars;
std::vector<std::vector<int>> actionVars;
std::unordered_map<int,int> lastNullary;
double solverTotal;

bool liftedRP::compute_heuristic_sat(const DBState &s, const Task &task, const std::clock_t & startTime, void* solver, sat_capsule & capsule, bool onlyGenerate, bool forceActionEveryStep) {
	// indices: timestep -> parameter -> object
	for (int time = planLength-1; time < planLength; time++){
		DEBUG(cout << "Generating time = " << time << endl);

		// generate nullary variables
		std::unordered_map<int,int> currentNullary;
		for (int n : task.nullary_predicates){
			int nullVar = capsule.new_variable();
			currentNullary[n] = nullVar;
			DEBUG(capsule.registerVariable(nullVar,	"nullary#" + to_string(n) + "_" + to_string(time)));
		}


		//cout << "O " << task.objects.size() << " A " << maxArity << endl;
		std::vector<std::vector<int>> parameterVarsTime(maxArity);
    	for (int paramter = 0; paramter < maxArity; paramter++){
			parameterVarsTime[paramter].resize(task.objects.size());

			for (size_t o = 0; o < task.objects.size(); o++){
				int objectVar = capsule.new_variable();
				parameterVarsTime[paramter][o] = objectVar;
				DEBUG(capsule.registerVariable(objectVar, "const@" + to_string(time) + "#" + to_string(paramter) + "-" + task.objects[indexToObj[o]].getName()));
			}
			// each parameter can have at most one value
			atMostOne(solver,capsule,parameterVarsTime[paramter]);
		}
		parameterVars.push_back(parameterVarsTime);

		/// General supporter selection (no specific precondition is considered here)
		std::vector<std::vector<int>> precSupporter;
		// precondition support selection
		for (int p = 0; p < maxPrec; p++){
			std::vector<int> precSupporterPrec;
			for (int pTime = -1; pTime < time; pTime++){
				int preSuppVar = capsule.new_variable();
				precSupporterPrec.push_back(preSuppVar);
				DEBUG(capsule.registerVariable(preSuppVar, "preSupp@" + to_string(time) + "#" + to_string(p) + "-" + to_string(pTime)));
			}

			precSupporter.push_back(precSupporterPrec);
		}

		/// variables stating over which variables a support spans
		// precSupporterOver[p][ptime] is true if there is support for precondition p spanning *over* time ptime
		std::vector<std::vector<int>> precSupporterOver;
		for (int p = 0; p < maxPrec; p++){
			std::vector<int> supportOver;
			for (int pTime = 0; pTime < time; pTime++){
				int overVar = capsule.new_variable();
				implies(solver,precSupporter[p][pTime], overVar);
				if (pTime > 0)
					implies(solver,supportOver.back(),overVar);
				
				supportOver.push_back(overVar);
				DEBUG(capsule.registerVariable(overVar, "supportOver@" + to_string(time) + "#" + to_string(p) + "-" + to_string(pTime)));
			}

			precSupporterOver.push_back(supportOver);
		}


		/// Variables tracking equality of task parameters	
		std::vector<std::vector<std::vector<int>>> parameterEquality;
    	for (int paramterThis = 0; paramterThis < maxArity; paramterThis++){
    		vector<vector<int>> equalVarsP;
			for (int pTime = 0; pTime < time; pTime++){
    			vector<int> equalVarsB;
				for (int paramterBefore = 0; paramterBefore < maxArity; paramterBefore++){
					int equalsVar = capsule.new_variable();
					equalVarsB.push_back(equalsVar);
					DEBUG(capsule.registerVariable(equalsVar, "equal@" + to_string(time) + "#" + to_string(paramterThis) + "@" + to_string(pTime) + "#" + to_string(paramterBefore)));
					
					for(size_t o = 0; o < task.objects.size(); o++){
						andImplies(solver,equalsVar, parameterVars[time][paramterThis][o], parameterVars[pTime][paramterBefore][o]);
						andImplies(solver,equalsVar, parameterVars[pTime][paramterBefore][o], parameterVars[time][paramterThis][o]);
						andImplies(solver,parameterVars[pTime][paramterBefore][o], parameterVars[time][paramterThis][o], equalsVar);
					}
				}
				equalVarsP.push_back(equalVarsB);
			}
			parameterEquality.push_back(equalVarsP);
		}

		/// action variables
		std::vector<int> actionVarsTime;	
		for (size_t action = 0; action < task.actions.size(); action++){
            DEBUG(cout << "\t" << task.actions[action].get_name() << endl);

			int actionVar = capsule.new_variable();
			actionVarsTime.push_back(actionVar);
			DEBUG(capsule.registerVariable(actionVar,"action@" + to_string(time) + "-" + task.actions[action].get_name()));

			// typing implications!
            auto params = task.actions[action].get_parameters();
            for (size_t l = 0; l < params.size(); l++) {
                DEBUG(cout << "\t\t" << task.type_names[params[l].type] << ": ");
                if (!needToType[{action,l}]){
                	DEBUG(cout << "no need to type " << endl);
					continue;
				}
				
				int lower = lowerTindex[params[l].type];
                int upper = upperTindex[params[l].type];
                DEBUG(for (int m = lower; m <= upper; m++) {
                    cout << task.objects[indexToObj[m]].getName() << " ";
                }
                cout << endl);

				for (int i = 0; i < lower; i++){
					int parameterConstantVar = parameterVars[time][l][i];
					impliesNot(solver,actionVar,parameterConstantVar);
				}

				for (int i = upper + 1; i < int(task.objects.size()); i++){
					int parameterConstantVar = parameterVars[time][l][i];
					impliesNot(solver,actionVar,parameterConstantVar);
				}

				std::vector<int> allowed;
				for (int i = lower; i <= upper; i++){
					int parameterConstantVar = parameterVars[time][l][i];
					allowed.push_back(parameterConstantVar);
				}
				impliesOr(solver,actionVar,allowed);
            }


			// TODO this is actually not necessary ... I will never access these variables anyway
            for (int l = params.size(); l < maxArity; l++) {
				impliesAllNot(solver,actionVar,parameterVars[time][l]);
			}


			// nullary preconditions
			for (int p : *setPosNullaryPrec[action])
				implies(solver,actionVar,lastNullary[p]);
			for (int p : *setNegNullaryPrec[action])
				impliesNot(solver,actionVar,lastNullary[p]);

			for (int p : *setPosNullaryEff[action])
				implies(solver,actionVar,currentNullary[p]);
			for (int p : *setNegNullaryEff[action])
				impliesNot(solver,actionVar,currentNullary[p]);


			// if this action is chosen, it has to be executable
			// this means that every precondition is supported by a prior action or the initial state
	        const auto precs = task.actions[action].get_precondition();
	        for (size_t prec = 0; prec < precs.size(); prec++) {
            	
				const auto & precObjec = precs[prec];
				int predicate = precObjec.predicate_symbol;
				if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
				
				if (task.predicates[predicate].getName().rfind("=", 0) == 0){
					if (precObjec.negated){
						// not equals
						if (precObjec.arguments[0].constant){
							int myObjIndex = objToIndex[precObjec.arguments[0].index];
							impliesNot(solver,actionVar, parameterVars[time][1][myObjIndex]);
						} else if (precObjec.arguments[1].constant){
							int myObjIndex = objToIndex[precObjec.arguments[1].index];
							impliesNot(solver,actionVar, parameterVars[time][0][myObjIndex]);
						} else {
							for(size_t o = 0; o < task.objects.size(); o++){
								andImpliesNot(solver,actionVar,parameterVars[time][precObjec.arguments[0].index][o], parameterVars[time][precObjec.arguments[1].index][o]);
							}
						}
					} else {
						// equals
						if (precObjec.arguments[0].constant){
							int myObjIndex = objToIndex[precObjec.arguments[0].index];
							implies(solver,actionVar, parameterVars[time][1][myObjIndex]);
						} else if (precObjec.arguments[1].constant){
							int myObjIndex = objToIndex[precObjec.arguments[1].index];
							implies(solver,actionVar, parameterVars[time][0][myObjIndex]);
						} else {
							for(size_t o = 0; o < task.objects.size(); o++){
								andImplies(solver,actionVar,parameterVars[time][precObjec.arguments[0].index][o], parameterVars[time][precObjec.arguments[1].index][o]);
								andImplies(solver,actionVar,parameterVars[time][precObjec.arguments[1].index][o], parameterVars[time][precObjec.arguments[0].index][o]);
							}
						}
					}
					continue;
				}

				// 1. Step: select the time step which supports
				// precSupporter is a generic variable that just tells you from which timestep we take the support
				impliesOr(solver,actionVar,precSupporter[prec]);
			
				// 2. Step: Supporter of type 1: initial state
				vector<pair<vector<int>,bool>> supportingTuples;

				// TODO: sind die nicht nach den predikaten sortiert????
    			for (size_t i = 0; i < task.get_static_info().get_relations().size(); i++) {
    			    auto rel = task.get_static_info().get_relations()[i];
    			    auto tuple = task.get_static_info().get_tuples_of_relation(i);

					if (predicate != rel.predicate_symbol) continue;
					
					// this is the correct predicate
    			    for (vector<int> groundA: tuple) {
    			    	supportingTuples.push_back({groundA,true});
					}
    			}

    			for (tSize i = 0; i < s.get_relations().size(); i++) {
    			    auto rel = s.get_relations()[i];
    			    auto tuple = s.get_tuples_of_relation(i);
					
					if (predicate != rel.predicate_symbol) continue;
    			    
					for (vector<int> groundA: tuple) {
    			    	supportingTuples.push_back({groundA,false});
    			    }
    			}
				
				
				// achiever structure contains both achievers and deleters
				ActionPrecAchiever* myAchievers = achievers[action]->precAchievers[prec];

				if (supportingTuples.size() == 0){
					DEBUG(cout << "\t\tno init support for precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
					impliesNot(solver,actionVar,precSupporter[prec][0]); // cannot be supported by init!
				} else {
					DEBUG(cout << "\t\tinit support for precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
					vector<int> suppOptions;
					for (size_t i = 0; i < supportingTuples.size(); i++){
						int suppVar = capsule.new_variable();
						suppOptions.push_back(suppVar);
						DEBUG(capsule.registerVariable(suppVar, "initAchiever@" + to_string(time) + "#" + to_string(action) + "-" + to_string(-1) + "_" + to_string(i)));
					}
					// one supporter must be chosen
					impliesOr(solver,actionVar,precSupporter[prec][0],suppOptions);

					for (size_t i = 0; i < supportingTuples.size(); i++){
						vector<int> tuple = supportingTuples[i].first;

						for (size_t j = 0; j < tuple.size(); j++){
							int myObjIndex = objToIndex[tuple[j]];
							if (precObjec.arguments[j].constant){
								if (precObjec.arguments[j].index != tuple[j])
									assertNot(solver,suppOptions[i]);
							} else {
								int myParam = precObjec.arguments[j].index;
								implies(solver,suppOptions[i], parameterVars[time][myParam][myObjIndex]);
							}
						}

						//// if init fact is not static, it may not be destroyed on the way ...
						//if (!supportingTuples[i].second){
						//	for (int prevTime = 0; prevTime < planLength-1; prevTime++){
						//		for (size_t del = 0; del < myAchievers->destroyers.size(); del++){
						//			Achiever* deleter = myAchievers->destroyers[del];

						//			set<int> criticalVars;
						//			bool noNeed = false; // if the deleting effect is statically unequal to the tuple we don't have to check it
						//			criticalVars.insert(actionVars[prevTime][deleter->action]);
						//
						//			for (size_t j = 0; j < tuple.size(); j++){
						//				int myObjIndex = objToIndex[tuple[j]];
						//				
						//				int deleterParam = deleter->params[j];
						//				if (deleterParam < 0){
						//					// its a constant!
						//					int deleterConst = -deleterParam-1;

						//					if (deleterConst != myObjIndex){
						//						noNeed = true;
						//					}
						//					//else equals no nothing to assert
						//				} else
						//					criticalVars.insert(parameterVars[prevTime][deleterParam][myObjIndex]);
						//			}

						//			if (noNeed) continue;

						//			criticalVars.insert(suppOptions[i]);

						//			notAll(solver,criticalVars);
						//		}
						//	}
						//}
					}
				}

				// 3. Step: Supporter of type 2: other actions
				for (size_t i = 1; i < precSupporter[prec].size(); i++){

					if (myAchievers->achievers.size() == 0){
						DEBUG(cout << "\t\tnon-achievable precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
						impliesNot(solver,actionVar,precSupporter[prec][i]);
					} else {
						DEBUG(cout << "\t\tachievable precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
						
						// check if achiever have disjunct predicates
						unordered_set<int> setset;
						for (size_t j = 0; j < myAchievers->achievers.size(); j++)
							setset.insert(myAchievers->achievers[j]->action);
						
						bool allDifferentActions = false;
						if (setset.size() == myAchievers->achievers.size())
							allDifferentActions = true;
						
						
						vector<int> achieverSelection;
						for (size_t j = 0; j < myAchievers->achievers.size(); j++){
							Achiever* achiever = myAchievers->achievers[j];
							
							int achieverVar = 0;
							if (! allDifferentActions){
								achieverVar = capsule.new_variable();
								DEBUG(capsule.registerVariable(achieverVar,
											"preAchieve@" + to_string(time) + "#" + to_string(action) + 
											"-" + to_string(i) + "_" + to_string(j)));

								// if the achiever has been selected then it must be present!
								implies(solver,achieverVar,actionVars[i-1][achiever->action]);
							
							} else {
								// the action var plays the role of the achiever var
								achieverVar = actionVars[i-1][achiever->action];
							}
							achieverSelection.push_back(achieverVar);
							
							
							for (size_t k = 0; k < achiever->params.size(); k++){
								int theirParam = achiever->params[k];
								
								if (!precObjec.arguments[k].constant){
									int myParam = precObjec.arguments[k].index; // my index position

									if (theirParam < 0){
										int theirConst  = -theirParam-1;
										if (!allDifferentActions)
											implies(solver,achieverVar,parameterVars[time][myParam][objToIndex[theirConst]]);
										else
											andImplies(solver,actionVar,precSupporter[prec][i],achieverVar,parameterVars[time][myParam][objToIndex[theirConst]]);
									} else {
										
										if (!allDifferentActions)
											implies(solver,achieverVar,parameterEquality[myParam][i-1][theirParam]);
										else
											andImplies(solver,actionVar,precSupporter[prec][i],achieverVar,parameterEquality[myParam][i-1][theirParam]);
									}
								} else {
									// my param is a const
									int myConst = precObjec.arguments[k].index; // my const ID
									
									if (theirParam >= 0){

										if (!allDifferentActions)
											implies(solver,achieverVar,parameterVars[i-1][theirParam][objToIndex[myConst]]);
										else
											andImplies(solver,actionVar,precSupporter[prec][i],achieverVar,parameterVars[i-1][theirParam][objToIndex[myConst]]);
									
									} // else two constants, this has been checked statically
								}
							}
						}
						impliesOr(solver,actionVar,precSupporter[prec][i],achieverSelection);
					}
				}


				// no deleter in between
				for (int deleterTime = 0; deleterTime < planLength - 1; deleterTime++){
					for (size_t del = 0; del < myAchievers->destroyers.size(); del++){
						Achiever* deleter = myAchievers->destroyers[del];

						vector<int> criticalVars;
						bool noNeed = false; // if the deleting effect is statically unequal to the tuple we don't have to check it
						criticalVars.push_back(actionVars[deleterTime][deleter->action]);
			
						for (size_t k = 0; k < deleter->params.size(); k++){
							int deleterParam = deleter->params[k];
							
							if (!precObjec.arguments[k].constant){
								int myParam = precObjec.arguments[k].index; // my index position
								
								// both are actual variables
								if (deleterParam >= 0){
									criticalVars.push_back(parameterEquality[myParam][deleterTime][deleterParam]);
								} else {
									// deleter is a constant
									int deleterConst  = -deleterParam-1;
									criticalVars.push_back(parameterVars[time][myParam][objToIndex[deleterConst]]);
								}
							} else {
								int myConst = precObjec.arguments[k].index; // my index position
								
								// deleter is a variable
								if (deleterParam >= 0){
									criticalVars.push_back(parameterVars[deleterTime][deleterParam][objToIndex[myConst]]);
								} else if (myConst != -deleterParam-1)
									noNeed = true;
								//else equals no nothing to assert
							}
						}

						if (noNeed) continue;
						
						criticalVars.push_back(precSupporterOver[prec][deleterTime]);
						criticalVars.push_back(actionVar);
						//cout << "CRIT";
						//for (int x : criticalVars)
						//	cout << " " << x << " " << capsule.variableNames[x];
						//cout << endl;

						set<int> temp(criticalVars.begin(), criticalVars.end());
						notAll(solver,temp);
					}
				}

	
			}
		}

		// frame axioms for nullary predicates
		for (int n : task.nullary_predicates){
			vector<int> adder;
			for (int a : nullaryAchiever[n])
			   adder.push_back(actionVarsTime[a]);
			impliesPosAndNegImpliesOr(solver,currentNullary[n], lastNullary[n], adder);

			vector<int> deleter;
			for (int d : nullaryDestroyer[n])
			   deleter.push_back(actionVarsTime[d]);
			impliesPosAndNegImpliesOr(solver,lastNullary[n], currentNullary[n], deleter);
		}


		actionVars.push_back(actionVarsTime);
		if (forceActionEveryStep) atLeastOne(solver,capsule,actionVarsTime); // correct for incremental solving
		atMostOne(solver,capsule,actionVarsTime);
	
		
		lastNullary = currentNullary;
	}

	int nullaryGoalBlocker = capsule.new_variable();
	DEBUG(capsule.registerVariable(nullaryGoalBlocker,"nullaryGoalBlocker#" + to_string(planLength)));
	if (!onlyGenerate) ipasir_assume(solver,nullaryGoalBlocker);

	
    for (int g : task.goal.positive_nullary_goals)
		implies(solver,nullaryGoalBlocker,lastNullary[g]);	
    for (int g : task.goal.negative_nullary_goals)
		impliesNot(solver,nullaryGoalBlocker,lastNullary[g]);	


	// the goal must be achieved!
	for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
		const AtomicGoal & goalAtom = task.goal.goal[goal];
		if (goalAtom.negated) continue; // TODO don't know what to do ...
		//if (!atom_not_satisfied(s,goalAtom)) continue; // goal is satisfied so we don't have to achieve it via actions

		ActionPrecAchiever* thisGoalAchievers = goalAchievers->precAchievers[goal];
	
	
		std::vector<int> goalSupporter;
		for (int pTime = planLength-1; pTime < planLength; pTime++){
			int goalSuppVar = goalSupporterVars[goal][pTime+1];

			vector<int> achieverSelection;
			for (size_t j = 0; j < thisGoalAchievers->achievers.size(); j++){
				Achiever* achiever = thisGoalAchievers->achievers[j];
				int achieverVar = capsule.new_variable();
				achieverSelection.push_back(achieverVar);
				DEBUG(capsule.registerVariable(achieverVar,
							"goalAchieve#" + to_string(goal) + 
							"-" + to_string(pTime) + "_" + to_string(j)));

				// if the achiever has been selected then it must be present!
				implies(solver,achieverVar,actionVars[pTime][achiever->action]);
				for (size_t k = 0; k < achiever->params.size(); k++){
					int myConst = goalAtom.args[k]; // my object (main index)
					int theirParam = achiever->params[k];

					if (theirParam >= 0){
						implies(solver,achieverVar, parameterVars[pTime][theirParam][objToIndex[myConst]]);
					} // else it is a constant and has already been checked
				}
			}
			impliesOr(solver,goalSuppVar,achieverSelection);
		}
	
		// don't use later support ... These assumptions are cleared after each call
		
		if (!onlyGenerate)
			for (size_t time = planLength + 1; time < goalSupporterVars[goal].size(); time++)
				ipasir_assume(solver,-goalSupporterVars[goal][time]);
	}

	// this timestep might disable goal achievers ...
	for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
		const AtomicGoal & goalAtom = task.goal.goal[goal];
		if (goalAtom.negated) continue; // TODO don't know what to do ...
		//if (!atom_not_satisfied(s,goalAtom)) {
		//	cout << "GOAL already satisfied in init ... we have not implemeted this ... " << endl;
		//	//exit(0);	
		//}

		ActionPrecAchiever* thisGoalDestroyers = goalAchievers->precAchievers[goal];
	
	
		std::vector<int> goalSupporter;
		// from the beginning ... 
		for (int pTime = 0; pTime <= planLength; pTime++){
			int goalSuppVar = goalSupporterVars[goal][pTime];

			for (size_t j = 0; j < thisGoalDestroyers->destroyers.size(); j++){
				Achiever* destroyer = thisGoalDestroyers->destroyers[j];
				
				vector<int> criticalVars;
				criticalVars.push_back(actionVars[planLength-1][destroyer->action]);

				for (size_t k = 0; k < destroyer->params.size(); k++){
					int myConst = goalAtom.args[k]; // my object (main index)
					int theirParam = destroyer->params[k];

					if (theirParam >= 0){
						criticalVars.push_back(parameterVars[planLength-1][theirParam][objToIndex[myConst]]);
					} // else it is a constant and has already been checked
				}

				criticalVars.push_back(goalSuppVar);
				set<int> temp(criticalVars.begin(), criticalVars.end());
				notAll(solver,temp);
			}
		}
	}

	if (onlyGenerate) return false;
		
	DEBUG(capsule.printVariables());

	DEBUG(cout << "Starting solver" << endl);
	std::clock_t solver_start = std::clock();
	int state = ipasir_solve(solver);
	std::clock_t solver_end = std::clock();
	double solver_time_in_ms = 1000.0 * (solver_end-solver_start) / CLOCKS_PER_SEC;
	DEBUG(cout << "Solver time: " << fixed << solver_time_in_ms << "ms" << endl);
	solverTotal += solver_time_in_ms;

	std::clock_t end = std::clock();
	double time_in_ms = 1000.0 * (end-startTime) / CLOCKS_PER_SEC;
	cout << "Overall time: " << fixed << time_in_ms << "ms of that Solver: " << solverTotal << "ms   Variables " << capsule.number_of_variables << " Clauses: " << get_number_of_clauses() << " length " << planLength << endl;
	

	DEBUG(cout << "Solver State: " << state << endl);
	if (state == 10){
#if NDEBUG
		//std::clock_t end = std::clock();
		//double time_in_ms = 1000.0 * (end-startTime) / CLOCKS_PER_SEC;
		//return true;
#endif
		DEBUG(printVariableTruth(solver,capsule));
	}
	else return false;


	// extract the plan
	vector<LiftedOperatorId> plan;
	for (int time = 0; time < planLength; time++){
		cout << "timestep " << time << endl;
		for (size_t action = 0; action < task.actions.size(); action++){
			int var = actionVars[time][action];
			if (ipasir_val(solver,var) > 0){

				cout << "  " << task.actions[action].get_name();
            	auto params = task.actions[action].get_parameters();
				vector<int> arguments;
            	for (size_t l = 0; l < params.size(); l++) {
					cout << " " << l << ":";
					for (size_t o = 0; o < task.objects.size(); o++){
						if (ipasir_val(solver,parameterVars[time][l][o]) > 0){
							cout << " " << task.objects[indexToObj[o]].getName();
							arguments.push_back(indexToObj[o]);
						}
					}
				}
				cout << endl;
				
				LiftedOperatorId op (action, move(arguments));
				plan.push_back(op);
			}
		}
	}

	print_plan(plan,task);
	cout << "Solution found." << endl;
	exit(0);
	return true;
}



int liftedRP::compute_heuristic(const DBState &s, const Task &task) {
	if (satMode){
		DEBUG(cout << "Parameter arity " << maxArity << " Objects " << task.objects.size() << endl);
		
		std::clock_t start = std::clock();
		void* solver = ipasir_init();
		sat_capsule capsule;
		reset_number_of_clauses();
		int maxPlanLength = 100;
		solverTotal = 0;

		goalSupporterVars.clear();
		parameterVars.clear();
		actionVars.clear();

		// the goal must be achieved!
		int gc = 0;
		for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
			const AtomicGoal & goalAtom = task.goal.goal[goal];
			std::vector<int> goalSupporter;
			
			if (goalAtom.negated) {
				goalSupporterVars.push_back(goalSupporter);
				continue; // TODO don't know what to do ...
			}
			gc++;
	
			//ActionPrecAchiever* thisGoalAchievers = goalAchievers->precAchievers[goal];
		
			for (int pTime = 0; pTime < maxPlanLength+1; pTime++){
				int goalSuppVar = capsule.new_variable();
				goalSupporter.push_back(goalSuppVar);
				DEBUG(capsule.registerVariable(goalSuppVar,
							"goalSupp#" + to_string(goal) + "-" + to_string(pTime-1)));
	
			}
			if (atom_not_satisfied(s,goalAtom)) assertNot(solver,goalSupporter[0]);	
			
			atLeastOne(solver,capsule,goalSupporter);
			goalSupporterVars.push_back(goalSupporter);
		}

		// we only test executable plans and if the goal is a dead end ...
		if (!gc) return 0;

		
		for (int n : task.nullary_predicates){
			int nullaryInInit = capsule.new_variable();
			lastNullary[n] = nullaryInInit;
			DEBUG(capsule.registerVariable(nullaryInInit,
						"nullary#" + to_string(n) + "_" + to_string(-1)));

			if (s.get_nullary_atoms()[n])
				assertYes(solver,nullaryInInit);
			else
				assertNot(solver,nullaryInInit);
		}


		// start the incremental search for a plan	
		planLength = 0;
		bool linearIncrease = true;
		for (int i = 0; i < 10; i++){
			if (!linearIncrease)
				while (planLength < (1 << i)-1){
					planLength++;
					compute_heuristic_sat(s,task,start,solver,capsule,true,false);
				}
			
			planLength++;
			if (compute_heuristic_sat(s,task,start,solver,capsule,false,linearIncrease)){
				ipasir_release(solver);
				cout << "\t\tPlan of length: " << planLength << endl;
				DEBUG(cout << "\t\tPlan of length: " << planLength << endl);
				exit(0);
				return planLength;
			} else {
				cout << "\t\tNo plan of length: " << planLength << endl;
				DEBUG(cout << "\t\tNo plan of length: " << planLength << endl);
				std::clock_t end = std::clock();
				double time_in_ms = 1000.0 * (end-start) / CLOCKS_PER_SEC;
				//cout << "Total time: " << fixed << time_in_ms << "ms" << endl;
				if (time_in_ms > 300000000){
					ipasir_release(solver);
					return planLength + 1;
				}
			}
			//exit(0);
		}
		exit(0);
		ipasir_release(solver);
		return 501;
	}


	IloEnv env;
    IloNumVarArray v(env);
    IloModel model(env);

    // create variables representing lifted relaxed plan
    // a1 p1_1 p1_2 ... p1_k a2 p2_1 p2_2 ... p2_k ... an pn_1 pn_2 ... pn_k
    for (int i = 0; i < planLength; i++) {
        v.add(IloNumVar(env, 0, numActions, IloNumVar::Int));
        string vName = "a" + to_string(i);
        v[v.getSize() - 1].setName(vName.c_str());
        for (int j = 0; j < maxArity; j++) {
            v.add(IloNumVar(env, 0, numObjs, IloNumVar::Int));
            string vName2 = "p" + to_string(i);
            vName2 += "_" + to_string(j);
            v[v.getSize() - 1].setName(vName2.c_str());
            model.add(v[actionID(i)] * largeC >= v[paramID(i, j)]); // if action schema is 0, the parameter also need to be 0
        }
    }

    // create main optimization function
    IloNumExpr mainExp(env);
    for (int i = 0; i < planLength; i++) {
        v.add(IloNumVar(env, 0, 1, IloNumVar::Bool));
        string vName = "a_opt" + to_string(i);
        v[v.getSize() - 1].setName(vName.c_str());
        model.add(v[v.getSize() - 1] * largeC >= v[actionID(i)]);
        mainExp = mainExp + (v[v.getSize() - 1]);
    }
    model.add(IloMinimize(env, mainExp));

    // enforce typing of action parameters
    for (int i = 0; i < planLength; i++) {
        int iSchema = actionID(i);
        for (int j = 1; j <= numActions; j++) { // actions with initial index 1 (!)
            //cout << task.actions[j - 1].get_name() << endl;
            IloConstraint schemaEq = (v[iSchema] == j);
            auto params = task.actions[j - 1].get_parameters();
            for (size_t l = 0; l < params.size(); l++) {
                //cout << "- " << task.type_names[params[l].type] << ": ";
                int lower = lowerTindex[params[l].type];
                int upper = upperTindex[params[l].type];
//                for (int m = lower; m <= upper; m++) {
//                    cout << task.objects[indexToObj[m]].getName() << " ";
//                }
//                cout << endl;
                int iP = paramID(i, l);
                IloIfThen lowerVarRange(env, schemaEq, (v[iP] - 1) > (lower - 1));
                IloIfThen upperVarRange(env, schemaEq, (v[iP] - 1) < (upper + 1));
                model.add(lowerVarRange);
                model.add(upperVarRange);
            }
        }
    }

    // add goal condition
    // todo: check for containment in current state

//    for (int pred : task.goal.positive_nullary_goals) {
//        if (!s.get_nullary_atoms()[pred]) {
//
//        }
//    }
//    for (int pred : task.goal.negative_nullary_goals) {
//        if (!s.get_nullary_atoms()[pred]) {
//
//        }
//    }
//    for (const AtomicGoal &atomicGoal : task.goal.goal) {
//        int goal_predicate = atomicGoal.predicate;
//        const Relation &relation_at_goal_predicate = s.get_relations()[goal_predicate];
//
//        const auto it = relation_at_goal_predicate.tuples.find(atomicGoal.args);
//        const auto end = relation_at_goal_predicate.tuples.end();
//        if ((!atomicGoal.negated && it == end) || (atomicGoal.negated && it != end)) {
//            return false;
//        }
//    }
//    return true;











//    for (int j = 0; j < task.goal.goal.size(); j++) {
//        auto g = task.goal.goal[j];
//        auto sPart = s.get_tuples_of_relation(g.predicate);
//        if(sPart.find(g) == sPart.end()) {
//
//        }
//        int pred = task.goal.goal[j].predicate;
//        cout << "goal: " << task.predicates[pred].getName();
//        for (int k = 0; k < task.goal.goal[j].args.size(); k++) {
//            int obj = task.goal.goal[j].args[k];
//            cout << " " << task.objects[obj].getName();
//        }
//        cout << endl;
//    }
    //model.add(v[0] == 3);

    IloCplex cplex(model);
    cplex.exportModel("/home/dh/Schreibtisch/LiftedDelRel/test.lp");
    cplex.setParam(IloCplex::Param::Threads, 1);

    // no output
    // cplex.setOut(env.getNullStream());
    // cplex.setWarning(env.getNullStream());

    int res = -1;
    if (cplex.solve()) {
        res = round(cplex.getObjValue()); // todo: use ceil for LP
        //cout << "a" << "=" << round(cplex.getValue(v[0])) << endl;
        //cout << "b" << "=" << round(cplex.getValue(v[1])) << endl;

        for (int i = 0; i < planLength; i++) {
            int x = round(cplex.getValue(v[actionID(i)])) - 1;
            if (x >= 0) {
                cout << "a" << i << "=" << task.actions[x].get_name();
                for (int j = 0; j < maxArity; j++) {
                    int x = round(cplex.getValue(v[paramID(i, j)])) - 1;
                    if (x >= 0) {
                        cout << " p" << j << "=" << task.objects[indexToObj[x]].getName();
                    }
                }
                cout << endl;
            }
        }
    }
    cout << "res: " << res << endl;
    exit(0);
    return 0;
}

int liftedRP::sortObjs(int index, int type) {
    lowerTindex[type] = index;
    for (int st : children[type]) {
        index = sortObjs(index, st);
    }
    for(int o : types[type]) {
        if (done.find(o) == done.end()) {
            objToIndex[o] = index;
            indexToObj[index] = o;
            index++;
            done.insert(o);
        }
    }
    upperTindex[type] = index - 1;
    return index;
}

int liftedRP::actionID(int i) {
    return (maxArity + 1) * i;
}

int liftedRP::paramID(int i, int j) {
    return (maxArity + 1) * i + (j + 1);
}
