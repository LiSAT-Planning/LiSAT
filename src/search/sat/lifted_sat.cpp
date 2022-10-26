//
// Created by Daniel Höller on 27.08.21.
//

#include "lifted_sat.h"
#include "sat_encoder.h"
#include "sat_termination.h"
#include "ipasir.h"
#include "../action.h"
#include "../search_engines/utils.h"
#include <unordered_set>
#include <cassert>
#include <chrono>
#include <iomanip>

using namespace std;

map<int,map<int,int>> actionArgumentPositions;
int numberOfArgumentPositions = 0;
map<int,int> firstArgumentOfType;
map<int,int> typeOfArgument;

vector<vector<vector<pair<vector<int>,int>>>> supportingTuples; // action -> precondition
vector<vector<vector<pair<vector<int>,int>>>> deletedTuples; // action -> precondition


LiftedSAT::LiftedSAT(const Task & task) {
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

	for (auto p : maxNum){
		firstArgumentOfType[p.first] = numberOfArgumentPositions;
		for (int i = numberOfArgumentPositions; i < numberOfArgumentPositions + p.second; i++)
			typeOfArgument[i] = p.first;
		numberOfArgumentPositions += p.second;
	}


	for (auto a: task.actions) {
		map<int,int> thisCount;
		for (auto para : a.get_parameters()){
			actionArgumentPositions[a.get_index()][para.index] = firstArgumentOfType[para.type] + thisCount[para.type];
			thisCount[para.type] += 1;
		}

		
		cout << "Action #" << a.get_index() << " "  << a.get_name() << ":";
		for (auto [a,b] : actionArgumentPositions[a.get_index()])
			cout << " " << a << "->" << b;
		cout << endl;
	}


    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++)
			objCount[oTypes[i]] += 1;
	}

	for (auto p : maxNum){
		cout << "T " << setw(2) << p.first << " # " << setw(2) << p.second << " size " << setw(5) << objCount[p.first] << endl;
	}
	cout << "Max Arity: " << maxArity << " diffSum: " << numberOfArgumentPositions << endl; 
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
        cout << i << " " << task.predicates[i].getName() << " isStatic " << task.predicates[i].isStaticPredicate() << endl;
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


	supportingTuples.resize(task.actions.size());
	deletedTuples.resize(task.actions.size());
	for (size_t action = 0; action < task.actions.size(); action++){
        const auto precs = task.actions[action].get_precondition();
		
		supportingTuples[action].resize(precs.size());
        for (size_t prec = 0; prec < precs.size(); prec++) {
        	DEBUG(cout << "\t\tprecondition #" << prec << endl);
        	
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue;


			vector<pair<vector<int>,int>> & mySupportingTuples = supportingTuples[action][prec];

			// TODO: sind die nicht nach den predikaten sortiert????
			for (size_t i = 0; i < task.get_static_info().get_relations().size(); i++) {
			    auto rel = task.get_static_info().get_relations()[i];
			    auto tuple = task.get_static_info().get_tuples_of_relation(i);

				if (predicate != rel.predicate_symbol) continue;
				
				// this is the correct predicate
			    for (vector<int> groundA: tuple) {
					bool notApplicable = false;
					for (size_t j = 0; j < groundA.size(); j++){
						int myObjIndex = objToIndex[groundA[j]];
						if (precObjec.arguments[j].constant){
							if (precObjec.arguments[j].index != groundA[j])
								notApplicable = true;
						} else {
							int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
							if (myObjIndex < lowerTindex[typeOfArgument[myParam]] ||
									myObjIndex > upperTindex[typeOfArgument[myParam]])
								notApplicable = true;
						}
					}
			    	
					if (notApplicable) continue;
					mySupportingTuples.push_back({groundA,-1}); // static ..
				}
			}

			int currentStartingPos = 0;
			for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
			    auto rel = task.initial_state.get_relations()[i];
			    auto tuple = task.initial_state.get_tuples_of_relation(i);
				
				if (predicate != rel.predicate_symbol) {
					currentStartingPos += tuple.size();
					continue;
				}
			    
				for (vector<int> groundA: tuple) {
					bool notApplicable = false;
					for (size_t j = 0; j < groundA.size(); j++){
						int myObjIndex = objToIndex[groundA[j]];
						if (precObjec.arguments[j].constant){
							if (precObjec.arguments[j].index != groundA[j])
								notApplicable = true;
						} else {
							int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
							if (myObjIndex < lowerTindex[typeOfArgument[myParam]] ||
									myObjIndex > upperTindex[typeOfArgument[myParam]])
								notApplicable = true;
						}
					}
			    	
					if (notApplicable) {
						currentStartingPos++;
						continue;
					}
			    	mySupportingTuples.push_back({groundA,currentStartingPos++});
			    }
			}
		}

		deletedTuples[action].resize(task.actions[action].get_effects().size());
        for (tSize ie = 0; ie < task.actions[action].get_effects().size(); ie++) {
            auto eff = task.actions[action].get_effects()[ie];
			if (!eff.negated) continue; // only negative effects can delete init facts
			int predicate = eff.predicate_symbol;

			//// gather the possibly deleted facts
			int currentStartingPos = 0;
			for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
			    auto rel = task.initial_state.get_relations()[i];
			    auto tuple = task.initial_state.get_tuples_of_relation(i);
				
				if (predicate != rel.predicate_symbol) {
					currentStartingPos += tuple.size();
					continue;
				}
			
				vector<pair<vector<int>,int>> & possiblyDeletedTuples = deletedTuples[action][ie];
				for (vector<int> groundA: tuple) {
					bool notApplicable = false;
					for (size_t j = 0; j < groundA.size(); j++){
						int myObjIndex = objToIndex[groundA[j]];
						if (eff.arguments[j].constant){
							if (eff.arguments[j].index != groundA[j])
								notApplicable = true;
						} else {
							int myParam = actionArgumentPositions[action][eff.arguments[j].index];
							if (myObjIndex < lowerTindex[typeOfArgument[myParam]] ||
									myObjIndex > upperTindex[typeOfArgument[myParam]])
								notApplicable = true;
						}
					}
			    	
					if (notApplicable) {
						currentStartingPos++;
						continue;
					}
			    	possiblyDeletedTuples.push_back({groundA,currentStartingPos++});
			    }
			}
		}
	}
}



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

bool LiftedSAT::atom_not_satisfied(const DBState &s,
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
std::vector<std::vector<int>> initNotTrueAfter;

std::vector<std::vector<std::vector<std::vector<int>>>> parameterEquality;
std::vector<std::vector<std::vector<int>>> precSupporter;
std::vector<std::vector<std::vector<int>>> precSupporterOver;

double solverTotal;


int actionTyping = 0;
int atMostOneParamterValue = 0;
int variableInitMaintenance = 0; 
int precSupport = 0;
int equals = 0;
int initSupp = 0;
int staticInitSupp = 0;
int nullary = 0;
int equalsPrecs = 0; 
int achieverImplications = 0; 
int noDeleter = 0; 
int oneAction = 0; 
int goalAchiever = 0; 
int goalDeleter = 0; 



// Generator function for the formula.
// This function generates *one* time step of the formula
// assumes that the number of the currently to generated time step is stored in the member variable planLength
//
// The semantics of the argument flags is as follows:
//
// onlyGenerate - true -> only generate the formula but do not attempt to solve it yet.
// forceActionEveryStep - true -> every timestep must contain an action
// onlyHardConstraints - true -> generate the formula with hard constraint clauses
//                       false -> generate the formula with assumptions instead of hard constraints
// pastIncremental - true -> we are in an incremental run over the ACD

bool LiftedSAT::generate_formula(const Task &task, const std::clock_t & startTime, void* solver, sat_capsule & capsule,
		bool onlyGenerate, bool forceActionEveryStep, bool onlyHardConstraints, bool pastIncremental,
		int pastLimit, long long time_limit_in_ms) {
	//for (size_t action = 0; action < task.actions.size(); action++){
	//	for (size_t param = 0; param < task.actions[action].get_parameters().size(); param++){
	//		int myType = task.actions[action].get_parameters()[param].type;

	//		int lower = lowerTindex[myType];
    //	    int upper = upperTindex[myType];
	//		cout << param << " " << upper - lower + 1 << endl;
	//	}
	//}

	//exit(0);


	bool generateBaseFormula = true;
	// don't generate the base formula if we are generating for a past limit other than one and we are in a satisficing run
	if (pastIncremental && pastLimit != 1) generateBaseFormula = false; 


	map<pair<int,int>,set<int>> equalsPairs;
	for (size_t action = 0; action < task.actions.size(); action++){
		// if this action is chosen, it has to be executable
		// this means that every precondition is supported by a prior action or the initial state
        const auto precs = task.actions[action].get_precondition();
        for (size_t prec = 0; prec < precs.size(); prec++) {
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 
			
			ActionPrecAchiever* myAchievers = achievers[action]->precAchievers[prec];
			
			// 3. Step: Supporter of type 2: other actions
			if (myAchievers->achievers.size() != 0){
				for (size_t j = 0; j < myAchievers->achievers.size(); j++){
					Achiever* achiever = myAchievers->achievers[j];
					for (size_t k = 0; k < achiever->params.size(); k++){
						int theirParam = achiever->params[k];
						
						if (!precObjec.arguments[k].constant){
							int myParam = precObjec.arguments[k].index; // my index position

							if (theirParam >= 0) {
								int myType = task.actions[action].get_parameters()[myParam].type;
								int theirType = task.actions[achiever->action].get_parameters()[theirParam].type; 

								int lower = min(lowerTindex[myType],lowerTindex[theirType]);
				                int upper = max(upperTindex[myType],upperTindex[theirType]);
								//cout << myParam << " " << theirParam << " " << upper - lower + 1 << endl;
			
								if (lowerTindex[myType] != lowerTindex[theirType] || upperTindex[myType] != upperTindex[theirType]){
									//cout << "type clash in achiever" << endl;
									//exit(0);
								}

                				for (int m = lower; m <= upper; m++)
									equalsPairs[{actionArgumentPositions[action][myParam],actionArgumentPositions[achiever->action][theirParam]}].insert(m);
							}
						} 
					}
				}
			}
			

			// no deleter in between
			for (size_t del = 0; del < myAchievers->destroyers.size(); del++){
				Achiever* deleter = myAchievers->destroyers[del];

				for (size_t k = 0; k < deleter->params.size(); k++){
					int deleterParam = deleter->params[k];
					
					if (!precObjec.arguments[k].constant){
						int myParam = precObjec.arguments[k].index; // my index position
						
						if (deleterParam >= 0) {
							int myType = task.actions[action].get_parameters()[myParam].type;
							int theirType = task.actions[deleter->action].get_parameters()[deleterParam].type; 

							int lower = min(lowerTindex[myType],lowerTindex[theirType]);
				            int upper = max(upperTindex[myType],upperTindex[theirType]);
                				
							for (int m = lower; m <= upper; m++)
								equalsPairs[{actionArgumentPositions[action][myParam],actionArgumentPositions[deleter->action][deleterParam]}].insert(m);
						}
					}
				}
			}
		}
	}

	DEBUG(
		for (auto x : equalsPairs)
			cout << "\t\tEquals Pair: " << x.first.first << " " << x.first.second << ": " << x.second.size() << endl;
			);



	int bef = get_number_of_clauses();
	// indices: timestep -> parameter -> object
	for (int time = planLength-1; time < planLength; time++){
		cout << "Generating time = " << setw(3) << time << " past limit = " << setw(7) << pastLimit << endl;

		// generate nullary variables
		std::unordered_map<int,int> currentNullary;
		
		if (generateBaseFormula){
			for (int n : task.nullary_predicates){
				int nullVar = capsule.new_variable();
				currentNullary[n] = nullVar;
				DEBUG(capsule.registerVariable(nullVar,	"nullary#" + to_string(n) + "_" + to_string(time)));
			}


			std::vector<int> initNotTrueAfterThis;
			for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
			    auto rel = task.initial_state.get_relations()[i];
			    auto tuple = task.initial_state.get_tuples_of_relation(i);
				
				for (size_t j = 0; j < tuple.size(); j++){
					int initAtom = capsule.new_variable();
					DEBUG(capsule.registerVariable(initAtom, "initAtomFalseAfter@" + to_string(time) + "#" + to_string(i) + "-" + to_string(j)));
					// if init atom as false after previous step, it is false now!
					if (initNotTrueAfter.size())
						implies(solver,initNotTrueAfter.back()[initNotTrueAfterThis.size()],initAtom);
					initNotTrueAfterThis.push_back(initAtom);
				}
			}
			initNotTrueAfter.push_back(initNotTrueAfterThis);
			bef = get_number_of_clauses();
			variableInitMaintenance += get_number_of_clauses() - bef;

			std::vector<std::vector<int>> parameterVarsTime(numberOfArgumentPositions);
    		for (int paramter = 0; paramter < numberOfArgumentPositions; paramter++){
				int type = typeOfArgument[paramter];
				int lower = lowerTindex[type];
				int upper = upperTindex[type];
				
				parameterVarsTime[paramter].resize(upper - lower + 1);

				for (int o = 0; o < upper - lower + 1; o++){
					int objectVar = capsule.new_variable();
					parameterVarsTime[paramter][o] = objectVar;
					DEBUG(capsule.registerVariable(objectVar, "const@" + to_string(time) + "#" + to_string(paramter) + "-" + task.objects[indexToObj[o + lower]].getName()));
				}
				// each parameter can have at most one value
				atMostOne(solver,capsule,parameterVarsTime[paramter]);
			}
			parameterVars.push_back(parameterVarsTime);

			atMostOneParamterValue += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();

			/// General supporter selection (no specific precondition is considered here)
			std::vector<std::vector<int>> precSupporterThisTime;
			// precondition support selection
			for (int p = 0; p < maxPrec; p++){
				std::vector<int> precSupporterPrec;
				for (int pTime = -1; pTime < time; pTime++){
					int preSuppVar = capsule.new_variable();
					precSupporterPrec.push_back(preSuppVar);
					DEBUG(capsule.registerVariable(preSuppVar, "preSupp@" + to_string(time) + "#" + to_string(p) + "-" + to_string(pTime)));
				}

				precSupporterThisTime.push_back(precSupporterPrec);
			}
			precSupporter.push_back(precSupporterThisTime);

			/// variables stating over which variables a support spans
			// precSupporterOver[p][ptime] is true if there is support for precondition p spanning *over* time ptime
			std::vector<std::vector<int>> precSupporterOverThisTime;
			for (int p = 0; p < maxPrec; p++){
				std::vector<int> supportOver;
				for (int pTime = 0; pTime < time; pTime++){
					int overVar = capsule.new_variable();
					implies(solver,precSupporter[time][p][pTime], overVar);
					if (pTime > 0)
						implies(solver,supportOver.back(),overVar);
					
					supportOver.push_back(overVar);
					DEBUG(capsule.registerVariable(overVar, "supportOver@" + to_string(time) + "#" + to_string(p) + "-" + to_string(pTime)));
				}

				precSupporterOverThisTime.push_back(supportOver);
			}
			precSupporterOver.push_back(precSupporterOverThisTime);

			precSupport += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();
		}	
		
		int startTime = max(0,time-pastLimit);

		/// Variables tracking equality of task parameters	
		std::vector<std::vector<std::vector<int>>> parameterEqualityThisTime;
		for (int paramterThis = 0; paramterThis < numberOfArgumentPositions; paramterThis++){
    		vector<vector<int>> equalVarsP;
			
			if (generateBaseFormula){
				// fill with empty entries
				for (int pTime = 0; pTime < startTime; pTime++){
    				vector<int> equalVarsB (numberOfArgumentPositions);
					equalVarsP.push_back(equalVarsB);
				}
			}


			int endTime = time;
			if (!generateBaseFormula && endTime) endTime = startTime+1;

			for (int pTime = startTime; pTime < endTime; pTime++){
    			vector<int> equalVarsB;
				for (int paramterBefore = 0; paramterBefore < numberOfArgumentPositions; paramterBefore++){
					DEBUG(cout << paramterThis << " = " << paramterBefore << " @ " << pTime); 
					if (!equalsPairs.count({paramterThis,paramterBefore})){
						equalVarsB.push_back(0); // illegal variable
						DEBUG(cout << " not relevant" << endl); 
						continue;
					}

					int equalsVar = capsule.new_variable();
					equalVarsB.push_back(equalsVar);
					DEBUG(capsule.registerVariable(equalsVar, "equal@" + to_string(time) + "#" + to_string(paramterThis) + "@" + to_string(pTime) + "#" + to_string(paramterBefore)));
				
					if (equalsPairs[{paramterThis,paramterBefore}].size() == 1){
						DEBUG(cout << " always true" << endl); 
						assertYes(solver,equalsVar);
					} else {
						int thisLower = lowerTindex[typeOfArgument[paramterThis]];
						int beforeLower = lowerTindex[typeOfArgument[paramterBefore]];
						for(int o : equalsPairs[{paramterThis,paramterBefore}]){
							if (o < lowerTindex[typeOfArgument[paramterThis]] || o > upperTindex[typeOfArgument[paramterThis]]){
								impliesNot(solver,equalsVar, parameterVars[pTime][paramterBefore][o-beforeLower]);
							} else if (o < lowerTindex[typeOfArgument[paramterBefore]] || o > upperTindex[typeOfArgument[paramterBefore]]){
								impliesNot(solver,equalsVar, parameterVars[time][paramterThis][o-thisLower]);
							} else {
								// need to subtract the starting values of the types
								andImplies(solver,equalsVar, parameterVars[time][paramterThis][o-thisLower], parameterVars[pTime][paramterBefore][o-beforeLower]);
								andImplies(solver,equalsVar, parameterVars[pTime][paramterBefore][o-beforeLower], parameterVars[time][paramterThis][o-thisLower]);
								andImplies(solver,parameterVars[pTime][paramterBefore][o-beforeLower], parameterVars[time][paramterThis][o-thisLower], equalsVar);
							}
						}
#ifndef NDEBUG
						int sz = equalsPairs[{paramterThis,paramterBefore}].size();
						cout << " generated " << sz << endl; 
#endif
					}
				}
				if (generateBaseFormula)
					equalVarsP.push_back(equalVarsB);
				else{
					//cout << parameterEquality[time][paramterThis].size() << " " << pTime << " " << time << endl; 
					parameterEquality[time][paramterThis][pTime] = equalVarsB;
				}
			}
			if (generateBaseFormula) parameterEqualityThisTime.push_back(equalVarsP);
		}
		if (generateBaseFormula) parameterEquality.push_back(parameterEqualityThisTime);
		
		equals += get_number_of_clauses() - bef;
		DEBUG(cout << "EQUALS clauses " << equals << endl);
		//exit(0);
		bef = get_number_of_clauses();


		// times not to use
		for (int p = 0; p < maxPrec; p++)
			for (int i = 1; i < startTime + 1; i++){
				if (onlyHardConstraints){
					assertNot(solver,precSupporter[time][p][i]);
				} else {
					ipasir_assume(solver,-precSupporter[time][p][i]);
				}
			}



		/// action variables
		std::vector<int> actionVarsTime;
		for (size_t action = 0; action < task.actions.size(); action++){
            DEBUG(cout << "\t" << task.actions[action].get_name() << endl);

			int actionVar;
			if (generateBaseFormula){  
				actionVar = capsule.new_variable();
				actionVarsTime.push_back(actionVar);
				DEBUG(capsule.registerVariable(actionVar,"action@" + to_string(time) + "-" + task.actions[action].get_name()));
			} else {
				actionVar = actionVars[time][action];
			}
		
			bef = get_number_of_clauses();

			// typing implications!
            auto params = task.actions[action].get_parameters();
			if (generateBaseFormula){
            	for (size_t l = 0; l < params.size(); l++) {
					int thisParameterIndex = actionArgumentPositions[action][l];
            	    DEBUG(cout << "\t\t" << task.type_names[params[l].type] << ": ");
            	    //if (!needToType[{action,l}]){
            	    //	DEBUG(cout << "no need to type " << endl);
					//	continue;
					//}
					
					int lower = lowerTindex[params[l].type];
            	    int upper = upperTindex[params[l].type];
            	    DEBUG(for (int m = lower; m <= upper; m++) {
            	        cout << task.objects[indexToObj[m]].getName() << " ";
            	    }
            	    cout << endl);

					//for (int i = 0; i < lower; i++){
					//	int parameterConstantVar = parameterVars[time][l][i];
					//	impliesNot(solver,actionVar,parameterConstantVar);
					//}

					//for (int i = upper + 1; i < int(task.objects.size()); i++){
					//	int parameterConstantVar = parameterVars[time][l][i];
					//	impliesNot(solver,actionVar,parameterConstantVar);
					//}

					std::vector<int> allowed;
					for (int i = 0; i <= upper - lower; i++){
						int parameterConstantVar = parameterVars[time][thisParameterIndex][i];
						allowed.push_back(parameterConstantVar);
					}
					impliesOr(solver,actionVar,allowed);
            	}
			}

			// TODO this is actually not necessary ... I will never access these variables anyway
            //for (int l = params.size(); l < maxArity; l++) {
			//	impliesAllNot(solver,actionVar,parameterVars[time][l]);
			//}
		
			actionTyping += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();


			if (generateBaseFormula){
        	    DEBUG(cout << "\t\tnullary" << endl);

				// nullary preconditions
				for (int p : *setPosNullaryPrec[action])
					implies(solver,actionVar,lastNullary[p]);
				for (int p : *setNegNullaryPrec[action])
					impliesNot(solver,actionVar,lastNullary[p]);

				for (int p : *setPosNullaryEff[action])
					implies(solver,actionVar,currentNullary[p]);
				for (int p : *setNegNullaryEff[action])
					impliesNot(solver,actionVar,currentNullary[p]);
			}
			
			nullary += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();
			

			// if this action is chosen, it has to be executable
			// this means that every precondition is supported by a prior action or the initial state
	        const auto precs = task.actions[action].get_precondition();
	        for (size_t prec = 0; prec < precs.size(); prec++) {
            	DEBUG(cout << "\t\tprecondition #" << prec << endl);
            	
				const auto & precObjec = precs[prec];
				int predicate = precObjec.predicate_symbol;
				if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			
				bef = get_number_of_clauses();
			
				if (task.predicates[predicate].getName().rfind("=", 0) == 0){
					if (generateBaseFormula){
						int varA = precObjec.arguments[0].index;
						int varB = precObjec.arguments[1].index;

						if (precObjec.negated){
							// not equals
							if (precObjec.arguments[0].constant){
								int myObjIndex = objToIndex[varA];
								varB = actionArgumentPositions[action][varB];
								impliesNot(solver,actionVar, parameterVars[time][varB][myObjIndex - lowerTindex[typeOfArgument[varB]]]);
							} else if (precObjec.arguments[1].constant){
								int myObjIndex = objToIndex[varB];
								varA = actionArgumentPositions[action][varA];
								impliesNot(solver,actionVar, parameterVars[time][varA][myObjIndex - lowerTindex[typeOfArgument[varA]]]);
							} else {
								varA = actionArgumentPositions[action][varA];
								varB = actionArgumentPositions[action][varB];
								for(int o = max(lowerTindex[typeOfArgument[varA]],lowerTindex[typeOfArgument[varB]]);
										o <= min(upperTindex[typeOfArgument[varA]],upperTindex[typeOfArgument[varB]]); o++){
									andImpliesNot(solver,actionVar,parameterVars[time][varA][o - lowerTindex[typeOfArgument[varA]]],
											parameterVars[time][varB][o - lowerTindex[typeOfArgument[varB]]]);
								}
							}
						} else {
							// equals
							if (precObjec.arguments[0].constant){
								int myObjIndex = objToIndex[varA];
								varB = actionArgumentPositions[action][varB];
								implies(solver,actionVar, parameterVars[time][varB][myObjIndex - lowerTindex[typeOfArgument[varB]]]);
							} else if (precObjec.arguments[1].constant){
								int myObjIndex = objToIndex[varB];
								varA = actionArgumentPositions[action][varA];
								implies(solver,actionVar, parameterVars[time][varA][myObjIndex - lowerTindex[typeOfArgument[varA]]]);
							} else {
								varA = actionArgumentPositions[action][varA];
								varB = actionArgumentPositions[action][varB];
								for(int o = max(lowerTindex[typeOfArgument[varA]],lowerTindex[typeOfArgument[varB]]);
										o <= min(upperTindex[typeOfArgument[varA]],upperTindex[typeOfArgument[varB]]); o++){
									andImplies(solver,actionVar,parameterVars[time][varA][o - lowerTindex[typeOfArgument[varA]]],
											parameterVars[time][varB][o - lowerTindex[typeOfArgument[varB]]]);
									andImplies(solver,actionVar,parameterVars[time][varB][o - lowerTindex[typeOfArgument[varB]]],
											parameterVars[time][varA][o - lowerTindex[typeOfArgument[varA]]]);
								}
							}
						}
					}
		
					equalsPrecs += get_number_of_clauses() - bef;
					bef = get_number_of_clauses();
					continue;
				}

				// 1. Step: select the time step which supports
				// precSupporter is a generic variable that just tells you from which timestep we take the support
				if (generateBaseFormula) impliesOr(solver,actionVar,precSupporter[time][prec]);
			
				// 2. Step: Supporter of type 1: initial state
				// achiever structure contains both achievers and deleters
				ActionPrecAchiever* myAchievers = achievers[action]->precAchievers[prec];

				bef = get_number_of_clauses();
				if (generateBaseFormula){
					if (supportingTuples[action][prec].size() == 0){
						DEBUG(cout << "\t\tno init support for precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
						impliesNot(solver,actionVar,precSupporter[time][prec][0]); // cannot be supported by init!
					} else {
						if (supportingTuples[action][prec].size() == 1){
							// if this action is chosen, exactly this tuple has to be used as the precondition
							vector<int> tuple = supportingTuples[action][prec][0].first;
							for (size_t j = 0; j < tuple.size(); j++){
								int myObjIndex = objToIndex[tuple[j]];
								if (precObjec.arguments[j].constant){
									if (precObjec.arguments[j].index != tuple[j]){
										if (task.predicates[predicate].isStaticPredicate())
											assertNot(solver,actionVar);
										else
											impliesNot(solver,actionVar,precSupporter[time][prec][0]);
									}
								} else {
									int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
									if (myObjIndex < lowerTindex[typeOfArgument[myParam]] || myObjIndex > upperTindex[typeOfArgument[myParam]]){
										if (task.predicates[predicate].isStaticPredicate())
											assertNot(solver,actionVar);
										else
											impliesNot(solver,actionVar,precSupporter[time][prec][0]);
									} else {
										if (task.predicates[predicate].isStaticPredicate())
											implies(solver,actionVar, parameterVars[time][myParam][myObjIndex - lowerTindex[typeOfArgument[myParam]]]);
										else
											impliesAnd(solver,actionVar,precSupporter[time][prec][0], parameterVars[time][myParam][myObjIndex - lowerTindex[typeOfArgument[myParam]]]);
									}
								}
							}
						} else {
							if (precObjec.arguments.size() == 1){
								vector<int> possibleValues;
								
								for (size_t i = 0; i < supportingTuples[action][prec].size(); i++){
									vector<int> tuple = supportingTuples[action][prec][i].first;
								
									int myObjIndex = objToIndex[tuple[0]];
									int myParam = actionArgumentPositions[action][precObjec.arguments[0].index];
									int constantVar = parameterVars[time][myParam][myObjIndex - lowerTindex[typeOfArgument[myParam]]];
									
									possibleValues.push_back(constantVar);
								}

								if (task.predicates[predicate].isStaticPredicate())
									impliesOr(solver,actionVar,possibleValues);
								else
									impliesOr(solver,actionVar,precSupporter[time][prec][0],possibleValues);
							} else {
								bool firstWithNonConst = true;
								for (size_t lastPos = 0; lastPos < precObjec.arguments.size() - 1 ; lastPos++){
									// ignore all arguments until we find the first one with a non-constant
									if (precObjec.arguments[lastPos].constant && firstWithNonConst) continue;

									map<vector<int>,set<int>> possibleUpto;
	
									// build assignment tuple up to this point
									for (size_t i = 0; i < supportingTuples[action][prec].size(); i++){
										vector<int> tuple = supportingTuples[action][prec][i].first;
										vector<int> subTuple;
										subTuple.push_back(actionVar);
										if (!task.predicates[predicate].isStaticPredicate())
											subTuple.push_back(precSupporter[time][prec][0]);
									
										for (size_t j = 0; j <= lastPos; j++){
											// push only the non-constants
											if (precObjec.arguments[j].constant) continue;
											int myObjIndex = objToIndex[tuple[j]];
											int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
											int constantVar = parameterVars[time][myParam][myObjIndex - lowerTindex[typeOfArgument[myParam]]];
											
											subTuple.push_back(constantVar);
										}
										
										if (precObjec.arguments[lastPos + 1].constant) {
											possibleUpto[subTuple].insert(0);
											continue;
										}

										int myObjIndex = objToIndex[tuple[lastPos + 1]];
										int myParam = actionArgumentPositions[action][precObjec.arguments[lastPos + 1].index];
										int localObjectNumber = myObjIndex - lowerTindex[typeOfArgument[myParam]];
										//if (localObjectNumber >= parameterVars[time][myParam].size()) cout << "F " << localObjectNumber << " " << parameterVars[time][myParam].size() << endl;
										int constantVar = parameterVars[time][myParam][localObjectNumber];


										possibleUpto[subTuple].insert(constantVar);
									}


									if (!precObjec.arguments[lastPos + 1].constant)
										for (auto & x : possibleUpto){
											andImpliesOr(solver,x.first,x.second);
											//for (int i : x.first) cout << " - " << capsule.variableNames[i];
											//for (int i : x.second) cout << " " << capsule.variableNames[i];
											//cout << endl;
										}


									int posOfValue = 1;
									if (!task.predicates[predicate].isStaticPredicate()) posOfValue = 2;

									if (firstWithNonConst){
										vector<int> initial;
										for (auto & x : possibleUpto)
											initial.push_back(x.first[posOfValue]);
	
										if (task.predicates[predicate].isStaticPredicate())
											impliesOr(solver,actionVar,initial);
										else
											impliesOr(solver,actionVar,precSupporter[time][prec][0],initial);
										//cout << "- " << capsule.variableNames[actionVar];
										//for (int i : initial) cout << " " << capsule.variableNames[i];
										//cout << endl;
										firstWithNonConst = false;
									}
								}
							}
						}
						staticInitSupp += get_number_of_clauses() - bef;
						bef = get_number_of_clauses();
						
						if (!task.predicates[predicate].isStaticPredicate() && time){
							//////// NON static predicate
							DEBUG(cout << "\t\tinit support for precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
							
							for (size_t i = 0; i < supportingTuples[action][prec].size(); i++){
								vector<int> tuple = supportingTuples[action][prec][i].first;
								
								// gather all variables that are true if we use this particular precondition
								set<int> criticalVars;
								criticalVars.insert(actionVar);
								criticalVars.insert(precSupporter[time][prec][0]);
								for (size_t j = 0; j < tuple.size(); j++){
									int myObjIndex = objToIndex[tuple[j]];
									if (!precObjec.arguments[j].constant){
										int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
										if (!(myObjIndex < lowerTindex[typeOfArgument[myParam]] || myObjIndex > upperTindex[typeOfArgument[myParam]]))
											criticalVars.insert(parameterVars[time][myParam][myObjIndex - lowerTindex[typeOfArgument[myParam]]]);
									}
								}
								// now they can't all be true *and* we have deleted the init
								criticalVars.insert(initNotTrueAfter[time-1][supportingTuples[action][prec][i].second]);
								notAll(solver,criticalVars);
							}
						}
						initSupp += get_number_of_clauses() - bef;
						bef = get_number_of_clauses();
					}
				}
				
				
				//////// 3. Step: Supporter of type 2: other actions
			
				// times to use
				int endTime = precSupporter[time][prec].size();
				if (!generateBaseFormula && pastLimit != 1) endTime = min(startTime + 2,endTime); // only generate this single supporter structure

				for (int i = startTime + 1; i < endTime; i++){
					if (myAchievers->achievers.size() == 0){
						DEBUG(cout << "\t\tnon-achievable precondition #" << prec << " with pred " << predicate << " " << task.predicates[predicate].getName() << endl);
						impliesNot(solver,actionVar,precSupporter[time][prec][i]);
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
									int myParam = actionArgumentPositions[action][precObjec.arguments[k].index]; // my index position

									if (theirParam < 0){
										int theirConst  = -theirParam-1;
										if (!allDifferentActions)
											implies(solver,achieverVar,parameterVars[time][myParam][objToIndex[theirConst] - lowerTindex[typeOfArgument[myParam]]]);
										else
											andImplies(solver,actionVar,precSupporter[time][prec][i],achieverVar,parameterVars[time][myParam][objToIndex[theirConst] - lowerTindex[typeOfArgument[myParam]]]);
									} else {
										int myType = task.actions[action].get_parameters()[precObjec.arguments[k].index].type;
										int theirType = task.actions[achiever->action].get_parameters()[theirParam].type; 
										
										//int lower = min(lowerTindex[myType],lowerTindex[theirType]);
						                //int upper = max(upperTindex[myType],upperTindex[theirType]);

										// then only one value is actually possible to we know that equality holds!
										theirParam = actionArgumentPositions[achiever->action][theirParam];
										//if (lower != upper){
										if (!allDifferentActions){
											implies(solver,achieverVar,parameterEquality[time][myParam][i-1][theirParam]);
										}
										else {
											andImplies(solver,actionVar,precSupporter[time][prec][i],achieverVar,parameterEquality[time][myParam][i-1][theirParam]);
										}
										//}
									}
								} else {
									// my param is a const
									int myConst = precObjec.arguments[k].index; // my const ID
									
									if (theirParam >= 0){
										theirParam = actionArgumentPositions[achiever->action][theirParam];

										if (!allDifferentActions)
											implies(solver,achieverVar,parameterVars[i-1][theirParam][objToIndex[myConst] - lowerTindex[typeOfArgument[theirParam]]]);
										else
											andImplies(solver,actionVar,precSupporter[time][prec][i],achieverVar,parameterVars[i-1][theirParam][objToIndex[myConst] - lowerTindex[typeOfArgument[theirParam]]]);
									
									} // else two constants, this has been checked statically
								}
							}
						}
						impliesOr(solver,actionVar,precSupporter[time][prec][i],achieverSelection);
					}
				}
				achieverImplications += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();


				// no deleter in between
				endTime = planLength - 1;
				if (!generateBaseFormula && pastLimit != 1 && endTime) endTime = startTime+1;
				for (int deleterTime = startTime; deleterTime < endTime; deleterTime++){
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
									int myType = task.actions[action].get_parameters()[myParam].type;
									int theirType = task.actions[deleter->action].get_parameters()[deleterParam].type; 

									int lower = min(lowerTindex[myType],lowerTindex[theirType]);
					                int upper = max(upperTindex[myType],upperTindex[theirType]);
									myParam = actionArgumentPositions[action][myParam];
									deleterParam = actionArgumentPositions[deleter->action][deleterParam];

									// then only one value is actually possible to we know that equality holds!
									if (lower != upper){
										criticalVars.push_back(parameterEquality[time][myParam][deleterTime][deleterParam]);
									}
								} else {
									// deleter is a constant
									int deleterConst  = -deleterParam-1;
									myParam = actionArgumentPositions[action][myParam];
									criticalVars.push_back(parameterVars[time][myParam][objToIndex[deleterConst] - lowerTindex[typeOfArgument[myParam]]]);
								}
							} else {
								int myConst = precObjec.arguments[k].index; // my index position
					
								// deleter is a variable
								if (deleterParam >= 0){
									deleterParam = actionArgumentPositions[deleter->action][deleterParam];
									criticalVars.push_back(parameterVars[deleterTime][deleterParam][objToIndex[myConst] - lowerTindex[typeOfArgument[deleterParam]]]);
								} else if (myConst != -deleterParam-1)
									noNeed = true;
								//else equals no nothing to assert
							}
						}

						if (noNeed) continue;
						
						criticalVars.push_back(precSupporterOver[time][prec][deleterTime]);
						criticalVars.push_back(actionVar);
						//cout << "CRIT";
						//for (int x : criticalVars)
						//	cout << " " << x << " " << capsule.variableNames[x];
						//cout << endl;

						set<int> temp(criticalVars.begin(), criticalVars.end());
						notAll(solver,temp);
					}
				}
				noDeleter += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();
			}
		

			// this action might delete facts from init ...
        	auto thisAction = task.actions[action];
            if (generateBaseFormula){
				for (tSize ie = 0; ie < thisAction.get_effects().size(); ie++) {
                	auto eff = thisAction.get_effects()[ie];
					if (!eff.negated) continue; // only negative effects can delete init facts

					for (size_t i = 0; i < deletedTuples[action][ie].size(); i++){
						vector<int> tuple = deletedTuples[action][ie][i].first;

						set<int> neededVariables;
						neededVariables.insert(actionVar);
						for (size_t j = 0; j < tuple.size(); j++){
							int myObjIndex = objToIndex[tuple[j]];
							if (!eff.arguments[j].constant){
								int myParam = actionArgumentPositions[action][eff.arguments[j].index];
								if (!(myObjIndex < lowerTindex[typeOfArgument[myParam]] || myObjIndex > upperTindex[typeOfArgument[myParam]]))
									neededVariables.insert(parameterVars[time][myParam][myObjIndex - lowerTindex[typeOfArgument[myParam]]]);
							}
						}
						andImplies(solver,neededVariables,initNotTrueAfter[time][deletedTuples[action][ie][i].second]);
					}
				}
			}

			noDeleter += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();
		}

		// frame axioms for nullary predicates
		bef = get_number_of_clauses();
		if (generateBaseFormula){
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
		}
		nullary += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();

		if (time && generateBaseFormula){
			for (int thisAction : actionVarsTime)
				impliesOr(solver,thisAction,actionVars.back());
		}

		if (generateBaseFormula){
			actionVars.push_back(actionVarsTime);
			if (forceActionEveryStep) atLeastOne(solver,capsule,actionVarsTime); // correct for incremental solving
			//atLeastOne(solver,capsule,actionVarsTime); // correct for incremental solving
			atMostOne(solver,capsule,actionVarsTime);
		}
		oneAction += get_number_of_clauses() - bef;
	
		lastNullary = currentNullary;
	}



	bef = get_number_of_clauses();
	// nullary goal
	int nullaryGoalBlocker = capsule.new_variable();
	DEBUG(capsule.registerVariable(nullaryGoalBlocker,"nullaryGoalBlocker#" + to_string(planLength)));
	
	if (generateBaseFormula){
		if (!onlyGenerate) {
			if (onlyHardConstraints)
				assertYes(solver,nullaryGoalBlocker);
			else
				ipasir_assume(solver,nullaryGoalBlocker);
		}
		
	    for (int g : task.goal.positive_nullary_goals)
			implies(solver,nullaryGoalBlocker,lastNullary[g]);	
	    for (int g : task.goal.negative_nullary_goals)
			impliesNot(solver,nullaryGoalBlocker,lastNullary[g]);	
	}
	nullary += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();


	// the goal must be achieved!
	if (generateBaseFormula){
		for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
			const AtomicGoal & goalAtom = task.goal.goal[goal];
			if (goalAtom.negated) continue; // TODO don't know what to do ...
			//if (!atom_not_satisfied(task.initial_state,goalAtom)) continue; // goal is satisfied so we don't have to achieve it via actions

			ActionPrecAchiever* thisGoalAchievers = goalAchievers->precAchievers[goal];
		
		
			std::vector<int> goalSupporter;
			for (int pTime = planLength-1; pTime < planLength; pTime++){
				int goalSuppVar = goalSupporterVars[goal][pTime+1];

				vector<int> achieverSelection;
				for (size_t j = 0; j < thisGoalAchievers->achievers.size(); j++){
					Achiever* achiever = thisGoalAchievers->achievers[j];
					int achieverVar = capsule.new_variable();
					achieverSelection.push_back(achieverVar);
					DEBUG(capsule.registerVariable(achieverVar,	"goalAchieve#" + to_string(goal) + "-" + to_string(pTime) + "_" + to_string(j)));

					// if the achiever has been selected then it must be present!
					implies(solver,achieverVar,actionVars[pTime][achiever->action]);
					for (size_t k = 0; k < achiever->params.size(); k++){
						int myConst = goalAtom.args[k]; // my object (main index)
						if (achiever->params[k] < 0){
							if (myConst != -achiever->params[k]-1)
								assertNot(solver,achieverVar);
						
							continue;
						} else {
							int theirParam = actionArgumentPositions[achiever->action][achiever->params[k]];
							//cout << "param K " << achiever->params[k] << endl;
							if (theirParam >= 0){
								int constIdx = objToIndex[myConst];
								int lower = lowerTindex[typeOfArgument[theirParam]];
								int upper = upperTindex[typeOfArgument[theirParam]];

								//cout << "Goal #"  << goal << " achiever " << j << " parameter " << k << " theirParam " << theirParam << " const " << constIdx << " " << lower << " " << upper << endl;

								if (constIdx < lower || constIdx > upper)
									assertNot(solver, achieverVar);
								else
									implies(solver,achieverVar, parameterVars[pTime][theirParam][constIdx - lower]);
							} // else it is a constant and has already been checked
						}
					}
				}
				impliesOr(solver,goalSuppVar,achieverSelection);
			}
		
			// don't use later support ... These assumptions are cleared after each call
			
			if (!onlyGenerate){
				for (size_t time = planLength + 1; time < goalSupporterVars[goal].size(); time++)
					if (onlyHardConstraints)
						assertNot(solver,goalSupporterVars[goal][time]);
					else
						ipasir_assume(solver,-goalSupporterVars[goal][time]);
			}
		}
	}
	goalAchiever += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();


	// this timestep might disable goal achievers ...
	if (generateBaseFormula){
		for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
			const AtomicGoal & goalAtom = task.goal.goal[goal];
			if (goalAtom.negated) continue; // TODO don't know what to do ...
			//if (!atom_not_satisfied(task.initial_state,goalAtom)) {
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
						int theirParam = actionArgumentPositions[destroyer->action][destroyer->params[k]];

						if (theirParam >= 0){
							criticalVars.push_back(parameterVars[planLength-1][theirParam][objToIndex[myConst] - lowerTindex[typeOfArgument[theirParam]]]);
						} // else it is a constant and has already been checked
					}

					criticalVars.push_back(goalSuppVar);
					set<int> temp(criticalVars.begin(), criticalVars.end());
					notAll(solver,temp);
				}
			}
		}
	}
	goalDeleter += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();

	if (onlyGenerate) return false;

	cout << "Generated Variables " << setw(10) << capsule.number_of_variables <<
		" Clauses: " << setw(10) << get_number_of_clauses() << " length " << planLength << endl;
	cout << "\tone action         " << setw(9) << oneAction << endl; 
	cout << "\tmax 1 param value  " << setw(9) << atMostOneParamterValue << endl;
	cout << "\tinit maintain      " << setw(9) << variableInitMaintenance << endl;
	cout << "\tprec support       " << setw(9) << precSupport << endl;
	cout << "\tequals             " << setw(9) << equals << endl;
	cout << "\tinit support       " << setw(9) << initSupp << endl;
	cout << "\tstatic init support" << setw(9) << staticInitSupp << endl;
	cout << "\ttyping             " << setw(9) << actionTyping << endl;
	cout << "\tequals precs       " << setw(9) << equalsPrecs << endl; 
	cout << "\tachiever           " << setw(9) << achieverImplications << endl; 
	cout << "\tno deleter         " << setw(9) << noDeleter << endl; 
	cout << "\tgoal achievers     " << setw(9) << goalAchiever << endl; 
	cout << "\tgoal deleters      " << setw(9) << goalDeleter << endl; 
	cout << "\tnullary            " << setw(9) << nullary << endl;

		
	DEBUG(capsule.printVariables());

	DEBUG(cout << "Starting solver" << endl);
	bool* stopFlag = nullptr;
	std::clock_t solver_start = std::clock();

	if (time_limit_in_ms != -1) {
		// the given timelimit is relative to the startTime clock

		double time_since_start_in_ms = 1000.0 * (solver_start - startTime) / CLOCKS_PER_SEC;
		double timelimit_for_solver = time_limit_in_ms - time_since_start_in_ms;
		cout << endl << "\t\t #### setting solver time limit "  << setw(10) << timelimit_for_solver << endl;
		stopFlag = ensure_termination_after(solver,timelimit_for_solver);
	}


	int state = ipasir_solve(solver);
	if (stopFlag != nullptr) stop_termination_checking(stopFlag); // tell the termination checker to terminate itself
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
					int p = actionArgumentPositions[action][l];
					cout << " " << l << ":";
					for (int o = 0; o <= upperTindex[typeOfArgument[p]] - lowerTindex[typeOfArgument[p]]; o++){
						if (ipasir_val(solver,parameterVars[time][p][o]) > 0){
							cout << " " << task.objects[indexToObj[o + lowerTindex[typeOfArgument[p]]]].getName();
							arguments.push_back(indexToObj[o + lowerTindex[typeOfArgument[p]]]);
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



utils::ExitCode LiftedSAT::solve(const Task &task, int limit, bool optimal, bool incremental) {
	bool satisficing = !optimal;

	if (satisficing){
		DEBUG(cout << "Parameter arity " << maxArity << " Objects " << task.objects.size() << endl);
	
	
		vector<int> planLenghtsToTry;
		if (limit == -1){
			planLenghtsToTry.push_back(10);
			planLenghtsToTry.push_back(25);
			planLenghtsToTry.push_back(50);
			planLenghtsToTry.push_back(100);
			planLenghtsToTry.push_back(200);
		} else
			planLenghtsToTry.push_back(limit);
	

		long long overall_time_limit = 30*60*1000;

		std::clock_t overall_start = std::clock();
		double overall_start_in_ms = 1000.0 * (overall_start) / CLOCKS_PER_SEC;
		cout << endl << "\t\t #### Current time " << setw(10) << overall_start_in_ms  << endl;

		for (int currentLimitIndex = 0; currentLimitIndex < int(planLenghtsToTry.size()); currentLimitIndex++){
			maxLen = planLenghtsToTry[currentLimitIndex];
			std::clock_t start = std::clock();
			double already_used_time_is_ms = 1000.0 * (start - overall_start) / CLOCKS_PER_SEC;
			double remaining_time_is_ms = overall_time_limit - already_used_time_is_ms;
			double my_time_slice = remaining_time_is_ms / (planLenghtsToTry.size() - currentLimitIndex);
			cout << endl << "\t\t #### Starting plan length " << setw(5) << maxLen << " time limit " << setw(10) << my_time_slice << endl;

	
			// start the incremental search for a plan	
			void* solver;
			if (incremental)
				solver = ipasir_init();
			sat_capsule capsule;
			
			for (int pastLimit = 1; pastLimit < maxLen + 1; pastLimit++){
				if (!incremental) {// create a new solver instance for every ACD
					solver = ipasir_init();
					capsule.number_of_variables = 0;
					DEBUG(capsule.variableNames.clear());
					reset_number_of_clauses();


					// reset formula size counters
					actionTyping = 0;
					atMostOneParamterValue = 0;
					variableInitMaintenance = 0;
					precSupport = 0;
					equals = 0;
					initSupp = 0;
					nullary = 0;
					equalsPrecs = 0; 
					achieverImplications = 0; 
					staticInitSupp = 0;
					noDeleter = 0; 
					oneAction = 0; 
					goalAchiever = 0; 
					goalDeleter = 0; 
				}

				
				cout << endl << "Maximum Achiever Consumer Distance (ACD) " << setw(5) << pastLimit << endl;
				cout << "===================================================="  << endl;
			
				int maxPlanLength = maxLen + 2;
				solverTotal = 0;

				if (!incremental){
					goalSupporterVars.clear();
					parameterVars.clear();
					initNotTrueAfter.clear();
					actionVars.clear();
					parameterEquality.clear();
					precSupporter.clear();
					precSupporterOver.clear();
				}

				if (pastLimit == 1 || !incremental){
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
							DEBUG(capsule.registerVariable(goalSuppVar, "goalSupp#" + to_string(goal) + "-" + to_string(pTime-1)));

						}
						if (atom_not_satisfied(task.initial_state,goalAtom)) assertNot(solver,goalSupporter[0]);	
						
						atLeastOne(solver,capsule,goalSupporter);
						goalSupporterVars.push_back(goalSupporter);
					}

					// we only test executable plans and if the goal is a dead end ...
					//if (!gc) return 0;

					
					for (int n : task.nullary_predicates){
						int nullaryInInit = capsule.new_variable();
						lastNullary[n] = nullaryInInit;
						DEBUG(capsule.registerVariable(nullaryInInit,
									"nullary#" + to_string(n) + "_" + to_string(-1)));

						if (task.initial_state.get_nullary_atoms()[n])
							assertYes(solver,nullaryInInit);
						else
							assertNot(solver,nullaryInInit);
					}
				}

			
				planLength = 0;
				while (planLength < maxLen){
					planLength++;
					generate_formula(task,start,solver,capsule,true,false,!incremental,incremental,pastLimit);
				}
				planLength++;
				if (generate_formula(task,start,solver,capsule,false,false,!incremental,incremental,pastLimit, my_time_slice)){
					ipasir_release(solver);
					cout << "\t\tPlan of length: " << planLength << endl;
					DEBUG(cout << "\t\tPlan of length: " << planLength << endl);
					return utils::ExitCode::SUCCESS;
				} else {
					cout << "\t\tNo plan of length: " << planLength << endl;
					DEBUG(cout << "\t\tNo plan of length: " << planLength << endl);
					std::clock_t end = std::clock();
					double time_in_ms = 1000.0 * (end-start) / CLOCKS_PER_SEC;
					if (time_in_ms >= my_time_slice){
						ipasir_release(solver);
						// if we are the last length to try and timed out ...
						if (planLenghtsToTry.size() - 1 == currentLimitIndex)
							return utils::ExitCode::SEARCH_OUT_OF_TIME;
						else
							break; // exit the loop iterating over past limits
					}
				}
				if (!incremental)
					ipasir_release(solver);
			}
		}
	} else {
		if (limit == -1) maxLen = 9999999; else maxLen = limit;
		void* solver;
		sat_capsule capsule;
		if (incremental){
			solver = ipasir_init();
			planLength = 0;
		}
		
		for (int i = 0; i < maxLen; i++){
			if (!incremental) {// create a new solver instance for every ACD
				solver = ipasir_init();
				capsule.number_of_variables = 0;
				DEBUG(capsule.variableNames.clear());
				reset_number_of_clauses();


				// reset formula size counters
				actionTyping = 0;
				atMostOneParamterValue = 0;
				variableInitMaintenance = 0;
				precSupport = 0;
				equals = 0;
				initSupp = 0;
				nullary = 0;
				equalsPrecs = 0; 
				staticInitSupp = 0;
				achieverImplications = 0; 
				noDeleter = 0; 
				oneAction = 0; 
				goalAchiever = 0; 
				goalDeleter = 0; 
			}

			std::clock_t start = std::clock();
			int maxPlanLength = maxLen + 5;
			solverTotal = 0;

			if (!incremental){
				goalSupporterVars.clear();
				parameterVars.clear();
				actionVars.clear();
				parameterEquality.clear();
				precSupporter.clear();
				precSupporterOver.clear();
				lastNullary.clear();
				initNotTrueAfter.clear();
			}
			
			
			// initialise 0-ary predicates either every time we run or once for incremental solving
			if (!incremental || i == 0){

				// the goal must be achieved!
				int gc = 0;
				int clausesBefore = get_number_of_clauses();
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
					if (atom_not_satisfied(task.initial_state,goalAtom)) assertNot(solver,goalSupporter[0]);	
					
					atLeastOne(solver,capsule,goalSupporter);
					goalSupporterVars.push_back(goalSupporter);
				}
				goalAchiever += get_number_of_clauses() - clausesBefore;
				clausesBefore = get_number_of_clauses();

				// we only test executable plans and if the goal is a dead end ...
				if (!gc) return utils::ExitCode::SEARCH_UNSOLVABLE;

			
				for (int n : task.nullary_predicates){
					int nullaryInInit = capsule.new_variable();
					lastNullary[n] = nullaryInInit;
					DEBUG(capsule.registerVariable(nullaryInInit,
								"nullary#" + to_string(n) + "_" + to_string(-1)));

					if (task.initial_state.get_nullary_atoms()[n])
						assertYes(solver,nullaryInInit);
					else
						assertNot(solver,nullaryInInit);
				}
				nullary += get_number_of_clauses() - clausesBefore;
			}


			// start the incremental search for a plan	
			
			
			// if not in incremental mode, we need to generate the formula for all timesteps.
			if (!incremental)
				planLength = 0;
			
			bool linearIncrease = true;
			if (!linearIncrease){
				while (planLength < (1 << i)-1){
					planLength++;
					generate_formula(task,start,solver,capsule,true,false,false,false);
				}
			} else {
				while (planLength < i){
					planLength++;
					generate_formula(task,start,solver,capsule,true,true,false,false);
				}
			}
			
			planLength++;
			if (generate_formula(task,start,solver,capsule,false,linearIncrease,!incremental,false)){
				ipasir_release(solver);
				cout << "\t\tPlan of length: " << planLength << endl;
				DEBUG(cout << "\t\tPlan of length: " << planLength << endl);
				return utils::ExitCode::SUCCESS;
			} else {
				cout << "\t\tNo plan of length: " << planLength << endl;
				DEBUG(cout << "\t\tNo plan of length: " << planLength << endl);
				std::clock_t end = std::clock();
				double time_in_ms = 1000.0 * (end-start) / CLOCKS_PER_SEC;
				//cout << "Total time: " << fixed << time_in_ms << "ms" << endl;
				if (time_in_ms > 300000000){
					ipasir_release(solver);
					return utils::ExitCode::SEARCH_OUT_OF_TIME;
				}
			}
		}
	}
	return utils::ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
}

int LiftedSAT::sortObjs(int index, int type) {
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

int LiftedSAT::actionID(int i) {
    return (maxArity + 1) * i;
}

int LiftedSAT::paramID(int i, int j) {
    return (maxArity + 1) * i + (j + 1);
}
