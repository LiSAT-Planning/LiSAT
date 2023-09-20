//
// Created by Gregor Behnke
//

#include "lifted_linear_sat.h"
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

extern map<int,map<int,int>> actionArgumentPositions;
extern int numberOfArgumentPositions;
extern map<int,int> firstArgumentOfType;
extern map<int,int> typeOfArgument;

extern vector<vector<vector<pair<vector<int>,int>>>> supportingTuples; // action -> precondition
extern vector<vector<vector<pair<vector<int>,int>>>> deletedTuples; // action -> precondition


map<int,map<int,int>> predicateArgumentPositions;
int numberOfPredicateArgumentPositions;
map<int,int> typeOfPredicateArgument;
vector<vector<pair<vector<int>,int>>> supportingPredicateTuples; // predicate


LiftedLinearSAT::LiftedLinearSAT(const Task & task) {
	numActions = task.actions.size();
    numObjs = task.objects.size();


	////////////////// argument positioning of actions
	map<int,int> maxNum;

    for (auto a: task.actions) {
        maxActionArity = max(maxActionArity, (int) a.get_parameters().size());
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
	////////////////// argument positioning of actions
	maxNum.clear();

    for (auto p: task.predicates) {
		if (p.isStaticPredicate()) continue; // static predicates get special treatment
        maxPredicateArity = max(maxPredicateArity, (int) p.getTypes().size());
		
		map<int,int> thisCount;
		for (auto paraType : p.getTypes())
			thisCount[paraType] += 1;

		for (auto p : thisCount)
			if (maxNum[p.first] < p.second)
				maxNum[p.first] = p.second;
    }

	numberOfPredicateArgumentPositions = 0;
	map<int,int> firstPredicateArgumentOfType;
	for (auto p : maxNum){
		firstPredicateArgumentOfType[p.first] = numberOfPredicateArgumentPositions;
		for (int i = numberOfPredicateArgumentPositions; i < numberOfPredicateArgumentPositions + p.second; i++)
			typeOfPredicateArgument[i] = p.first;
		numberOfPredicateArgumentPositions += p.second;
	}


	for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
		auto p = task.predicates[pIndex];
		if (p.isStaticPredicate()) continue; // static predicates get special treatment
		map<int,int> thisCount;
		for (int para = 0; para < int(p.getTypes().size()); para++){
			predicateArgumentPositions[pIndex][para] = firstPredicateArgumentOfType[p.getTypes()[para]] + thisCount[p.getTypes()[para]];
			thisCount[p.getTypes()[para]] += 1;
		}

		
		cout << "Predicate #" << pIndex << " "  << p.getName() << ":";
		for (auto [a,b] : predicateArgumentPositions[pIndex])
			cout << " " << a << "->" << b;
		cout << endl;
	}


	//////////////////////////////////////////////////////////////////////////
	map<int,int> objCount;
    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++)
			objCount[oTypes[i]] += 1;
	}

	for (auto p : maxNum){
		cout << "T " << setw(2) << p.first << " # " << setw(2) << p.second << " size " << setw(5) << objCount[p.first] << endl;
	}
	cout << "Max Arity: " << maxActionArity << " diffSum: " << numberOfArgumentPositions << endl; 
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

    //// create data structure for nullary precs/effects -> from bitmap to iterable set
    //for (tSize a = 0; a < task.actions.size(); a++) {
    //    setPosNullaryPrec.push_back(new unordered_set<int>);
    //    setNegNullaryPrec.push_back(new unordered_set<int>);
    //    setPosNullaryEff.push_back(new unordered_set<int>);
    //    setNegNullaryEff.push_back(new unordered_set<int>);

    //    auto posPrec = task.actions[a].get_positive_nullary_precond();
    //    for (tSize f = 0; f < posPrec.size(); f++) {
    //        if (posPrec[f]) {
    //            setPosNullaryPrec[a]->insert(f);
    //        }
    //    }
    //    auto negPrec = task.actions[a].get_negative_nullary_precond();
    //    for (tSize f = 0; f < negPrec.size(); f++) {
    //        if (negPrec[f]) {
    //            setNegNullaryPrec[a]->insert(f);
    //        }
    //    }
    //    auto posEff = task.actions[a].get_positive_nullary_effects();
    //    for (tSize f = 0; f < posEff.size(); f++) {
    //        if (posEff[f]) {
    //            setPosNullaryEff[a]->insert(f);
	//			nullaryAchiever[f].push_back(a);
    //        }
    //    }
    //    auto negEff = task.actions[a].get_negative_nullary_effects();
    //    for (tSize f = 0; f < negEff.size(); f++) {
    //        if (negEff[f]) {
    //            setNegNullaryEff[a]->insert(f);
	//			nullaryDestroyer[f].push_back(a);
    //        }
    //    }
    //}

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
    cout << "- max arity " << maxActionArity << endl;

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

	/////////////////////////// lookup table for the support from the initial state
	supportingPredicateTuples.resize(task.predicates.size());
	for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
		vector<pair<vector<int>,int>> & mySupportingTuples = supportingPredicateTuples[predicate];
		int currentStartingPos = 0;

		if (!task.predicates[predicate].isStaticPredicate())
			for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
			    auto rel = task.initial_state.get_relations()[i];
			    auto tuple = task.initial_state.get_tuples_of_relation(i);
				
				if (predicate != rel.predicate_symbol) {
					currentStartingPos += tuple.size();
					continue;
				}
			    
				for (vector<int> groundA: tuple) {
			    	mySupportingTuples.push_back({groundA,currentStartingPos++});
			    }
			}
		else
			// the predicate might be static ...
			for (tSize i = 0; i < task.get_static_info().get_relations().size(); i++) {
			    auto rel = task.get_static_info().get_relations()[i];
			    auto tuple = task.get_static_info().get_tuples_of_relation(i);
				
				if (predicate != rel.predicate_symbol) {
					currentStartingPos += tuple.size();
					continue;
				}
			    
				for (vector<int> groundA: tuple) {
			    	mySupportingTuples.push_back({groundA,currentStartingPos++});
			    }
			}
	}


	//supportingTuples.resize(task.actions.size());
	//deletedTuples.resize(task.actions.size());
	//for (size_t action = 0; action < task.actions.size(); action++){
    //    const auto precs = task.actions[action].get_precondition();
	//	
	//	supportingTuples[action].resize(precs.size());
    //    for (size_t prec = 0; prec < precs.size(); prec++) {
    //    	DEBUG(cout << "\t\tprecondition #" << prec << endl);
    //    	
	//		const auto & precObjec = precs[prec];
	//		int predicate = precObjec.predicate_symbol;
	//		if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
	//		if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue;


	//		vector<pair<vector<int>,int>> & mySupportingTuples = supportingTuples[action][prec];

	//		// TODO: sind die nicht nach den predikaten sortiert????
	//		for (size_t i = 0; i < task.get_static_info().get_relations().size(); i++) {
	//		    auto rel = task.get_static_info().get_relations()[i];
	//		    auto tuple = task.get_static_info().get_tuples_of_relation(i);

	//			if (predicate != rel.predicate_symbol) continue;
	//			
	//			// this is the correct predicate
	//		    for (vector<int> groundA: tuple) {
	//				bool notApplicable = false;
	//				for (size_t j = 0; j < groundA.size(); j++){
	//					int myObjIndex = objToIndex[groundA[j]];
	//					if (precObjec.arguments[j].constant){
	//						if (precObjec.arguments[j].index != groundA[j])
	//							notApplicable = true;
	//					} else {
//						int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
	//						if (myObjIndex < lowerTindex[typeOfArgument[myParam]] ||
	//								myObjIndex > upperTindex[typeOfArgument[myParam]])
	//							notApplicable = true;
	//					}
	//				}
	//		    	
	//				if (notApplicable) continue;
	//				mySupportingTuples.push_back({groundA,-1}); // static ..
	//			}
	//		}

	//		int currentStartingPos = 0;
	//		for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
	//		    auto rel = task.initial_state.get_relations()[i];
	//		    auto tuple = task.initial_state.get_tuples_of_relation(i);
	//			
	//			if (predicate != rel.predicate_symbol) {
	//				currentStartingPos += tuple.size();
	//				continue;
	//			}
	//		    
	//			for (vector<int> groundA: tuple) {
	//				bool notApplicable = false;
	//				for (size_t j = 0; j < groundA.size(); j++){
	//					int myObjIndex = objToIndex[groundA[j]];
	//					if (precObjec.arguments[j].constant){
	//						if (precObjec.arguments[j].index != groundA[j])
	//							notApplicable = true;
	//					} else {
	//						int myParam = actionArgumentPositions[action][precObjec.arguments[j].index];
	//						if (myObjIndex < lowerTindex[typeOfArgument[myParam]] ||
	//								myObjIndex > upperTindex[typeOfArgument[myParam]])
	//							notApplicable = true;
	//					}
	//				}
	//		    	
	//				if (notApplicable) {
	//					currentStartingPos++;
	//					continue;
	//				}
	//		    	mySupportingTuples.push_back({groundA,currentStartingPos++});
	//		    }
	//		}
	//	}

	//	deletedTuples[action].resize(task.actions[action].get_effects().size());
    //    for (tSize ie = 0; ie < task.actions[action].get_effects().size(); ie++) {
    //        auto eff = task.actions[action].get_effects()[ie];
	//		if (!eff.negated) continue; // only negative effects can delete init facts
	//		int predicate = eff.predicate_symbol;

	//		//// gather the possibly deleted facts
	//		int currentStartingPos = 0;
	//		for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
	//		    auto rel = task.initial_state.get_relations()[i];
	//		    auto tuple = task.initial_state.get_tuples_of_relation(i);
	//			
	//			if (predicate != rel.predicate_symbol) {
	//				currentStartingPos += tuple.size();
	//				continue;
	//			}
	//		
	//			vector<pair<vector<int>,int>> & possiblyDeletedTuples = deletedTuples[action][ie];
	//			for (vector<int> groundA: tuple) {
	//				bool notApplicable = false;
	//				for (size_t j = 0; j < groundA.size(); j++){
	//					int myObjIndex = objToIndex[groundA[j]];
	//					if (eff.arguments[j].constant){
	//						if (eff.arguments[j].index != groundA[j])
	//							notApplicable = true;
	//					} else {
	//						int myParam = actionArgumentPositions[action][eff.arguments[j].index];
	//						if (myObjIndex < lowerTindex[typeOfArgument[myParam]] ||
	//								myObjIndex > upperTindex[typeOfArgument[myParam]])
	//							notApplicable = true;
	//					}
	//				}
	//		    	
	//				if (notApplicable) {
	//					currentStartingPos++;
	//					continue;
	//				}
	//		    	possiblyDeletedTuples.push_back({groundA,currentStartingPos++});
	//		    }
	//		}
	//	}
	//}
}

void printVariableTruth(void* solver, sat_capsule & capsule);

//{
//
//
//void printVariableTruth(void* solver, sat_capsule & capsule){
//	for (int v = 1; v <= capsule.number_of_variables; v++){
//		int val = ipasir_val(solver,v);
//	
//		std::string s = std::to_string(v);
//		int x = 4 - s.size();
//		cout << "TRUTH ";
//		while (x-- && x > 0) std::cout << " ";
//		std::cout << v << ": ";
//		if (val > 0) std::cout << "    ";
//		else         std::cout << "not ";
//#ifndef NDEBUG
//		std::cout << capsule.variableNames[v] << endl; 
//#else
//		std::cout << v << endl;
//#endif
//	}
//}

bool LiftedLinearSAT::atom_not_satisfied(const DBState &s,
                                   const AtomicGoal &atomicGoal) const {
    const auto &tuples = s.get_relations()[atomicGoal.predicate].tuples;
    const auto it = tuples.find(atomicGoal.args);
    const auto end = tuples.end();
    return (!atomicGoal.negated && it==end) || (atomicGoal.negated && it!=end);
}

///// members that are actually needed
extern std::vector<std::vector<int>> actionVars;




///// members that not needed

extern vector<vector<int>> goalSupporterVars;
extern std::vector<std::vector<std::vector<int>>> parameterVars;
extern std::unordered_map<int,int> lastNullary;
extern std::vector<std::vector<int>> initNotTrueAfter;

extern std::vector<std::vector<std::vector<std::vector<int>>>> parameterEquality;
extern std::vector<std::vector<std::vector<int>>> precSupporter;
extern std::vector<std::vector<std::vector<int>>> precSupporterOver;

extern double solverTotal;


int predicateTyping = 0;
int atMostOnePredicate = 0;

extern int actionTyping;
extern int atMostOneParamterValue;
extern int variableInitMaintenance; 
extern int precSupport;
extern int equals;
extern int initSupp;
extern int staticInitSupp;
extern int nullary;
extern int equalsPrecs; 
extern int achieverImplications; 
extern int noDeleter; 
extern int oneAction; 
extern int goalAchiever; 
extern int goalDeleter; 


vector<vector<vector<int>>> predicateSlotVariables; // time -> slot -> predicate (contains -1 for static one)
vector<vector<vector<vector<int>>>> argumentSlotVariables; // time -> slot -> position -> constant (0 is the first possible one)

vector<vector<vector<int>>> LiftedLinearSAT::generate_action_state_equality(const Task &task, void* solver, sat_capsule & capsule, int width, int actionTime, int stateTime){

	// variables for argument pos X = slot Y parameter pos Z
	vector<vector<vector<int>>> equalsVars;

	int bef = get_number_of_clauses();
    for (int actionParamter = 0; actionParamter < numberOfArgumentPositions; actionParamter++){
		vector<vector<int>> eqVars;
		for (int slot = 0; slot < width; slot++){
			vector<int> eqVarsSlot;
	   		for (int factParameter = 0; factParameter < numberOfPredicateArgumentPositions; factParameter++){
				int equalsVar = capsule.new_variable();
				eqVarsSlot.push_back(equalsVar);
				DEBUG(capsule.registerVariable(equalsVar, to_string(actionTime) + " @ # " +to_string(actionParamter)+" = "	+ to_string(stateTime) + " @ # " + to_string(factParameter)));

				int thisLower = lowerTindex[typeOfArgument[actionParamter]];
				int beforeLower = lowerTindex[typeOfPredicateArgument[factParameter]];
				int thisUpper = upperTindex[typeOfArgument[actionParamter]];
				int beforeUpper = upperTindex[typeOfPredicateArgument[factParameter]];
	
	
				for(int o = 0; o < numObjs; o++){
					if (o < thisLower || o > thisUpper){
						if (o >= beforeLower && o <= beforeUpper)
							impliesNot(solver,equalsVar, argumentSlotVariables[stateTime][slot][factParameter][o-beforeLower]);
					}
					if (o < beforeLower || o > beforeUpper){
						if (o >= thisLower && o <= thisUpper)
							impliesNot(solver,equalsVar, parameterVars[actionTime][actionParamter][o-thisLower]);
					}
				
					// this could actually be the constant that makes them equal	
					if (o >= thisLower && o <= thisUpper && o >= beforeLower && o <= beforeUpper){
						// need to subtract the starting values of the types
						andImplies(solver,equalsVar, parameterVars[actionTime][actionParamter][o-thisLower], argumentSlotVariables[stateTime][slot][factParameter][o-beforeLower]);
						andImplies(solver,equalsVar, argumentSlotVariables[stateTime][slot][factParameter][o-beforeLower], parameterVars[actionTime][actionParamter][o-thisLower]);
						andImplies(solver,argumentSlotVariables[stateTime][slot][factParameter][o-beforeLower], parameterVars[actionTime][actionParamter][o-thisLower], equalsVar);
					}
				}
			}
			eqVars.push_back(eqVarsSlot);
		}
		equalsVars.push_back(eqVars);
	}
	equals += get_number_of_clauses() - bef;
	return equalsVars;
}


void LiftedLinearSAT::generate_predicate_slot_layer(const Task &task, void* solver, sat_capsule & capsule, int width, int time){

	vector<vector<int>> thisTimePredicateSlotVariables; // slot -> predicate (contains -1 for static one)
	vector<vector<vector<int>>> thisTimeArgumentSlotVariables; // slot -> position -> constant (0 is the first possible one)
	
	for (int slot = 0; slot < width; slot++){
		DEBUG(cout << "\tSlot " << slot << endl);

		// predicates
		vector<int> thisSlotPredicates;
		vector<int> thisSlotPredicatesAMO; // second copy without -1s
		for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0 || 
				task.predicates[predicate].getName().rfind("=", 0) == 0||
				task.predicates[predicate].isStaticPredicate()) {
				thisSlotPredicates.push_back(-1);
				continue; 
			}
			int predicateVar = capsule.new_variable();
			thisSlotPredicates.push_back(predicateVar);
			thisSlotPredicatesAMO.push_back(predicateVar);
			DEBUG(capsule.registerVariable(predicateVar, to_string(time) + " @ slot " + to_string(slot) + " predicate " + task.predicates[predicate].getName()));
		}
		int bef = get_number_of_clauses();
		atMostOne(solver,capsule,thisSlotPredicatesAMO);
		atLeastOne(solver,capsule,thisSlotPredicatesAMO);
		bef = get_number_of_clauses();
		
		thisTimePredicateSlotVariables.push_back(thisSlotPredicates);

		// This slot parameters
		std::vector<std::vector<int>> thisSlotParameterVars(numberOfPredicateArgumentPositions);
    	for (int paramter = 0; paramter < numberOfPredicateArgumentPositions; paramter++){
			int type = typeOfPredicateArgument[paramter];
			int lower = lowerTindex[type];
			int upper = upperTindex[type];
			
			thisSlotParameterVars[paramter].resize(upper - lower + 1);

			for (int o = 0; o < upper - lower + 1; o++){
				int objectVar = capsule.new_variable();
				thisSlotParameterVars[paramter][o] = objectVar;
				DEBUG(capsule.registerVariable(objectVar, to_string(time) + " @ slot " + to_string(slot) + " argument#" + to_string(paramter) + " = const " + task.objects[indexToObj[o + lower]].getName()));
			}
			// each parameter can have at most one value
			atMostOne(solver,capsule,thisSlotParameterVars[paramter]);
		}
		thisTimeArgumentSlotVariables.push_back(thisSlotParameterVars);

		atMostOneParamterValue += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();

		// predicate types must be correct
		for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
			if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do
			int predicateVar = thisSlotPredicates[predicate];
    	    DEBUG(cout << "\t" << time << " " << slot << " " << predicate << " " << task.predicates[predicate].getName() << " = " << predicateVar << endl);
			
			// typing implications!
			auto params = task.predicates[predicate].getTypes();
    	    for (size_t l = 0; l < params.size(); l++) {
				int thisParameterIndex = predicateArgumentPositions[predicate][l];
    	        DEBUG(cout << "\t\t" << task.type_names[params[l]] << ": ");
				
				int lower = lowerTindex[params[l]];
    	        int upper = upperTindex[params[l]];
    	        DEBUG(for (int m = lower; m <= upper; m++) {
    	            cout << task.objects[indexToObj[m]].getName() << " ";
    	        }
    	        cout << endl);

				// alternative encoding ...
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
					int parameterConstantVar = thisSlotParameterVars[thisParameterIndex][i];
					allowed.push_back(parameterConstantVar);
				}
				DEBUG(cout << "Typing " << predicateVar << ":"; for(auto x : allowed) cout << " " << x; cout << endl;);
				impliesOr(solver,predicateVar,allowed);
    	    }
		}
		predicateTyping += get_number_of_clauses() - bef;



		// maybe select from init
		bef = get_number_of_clauses();
		if (time == 0){
			for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
				if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do

				// consider how many arguments are there
				int predicateVar = thisSlotPredicates[predicate];
				cout << "PREDICATE VAR " << predicateVar << endl;
				if (task.predicates[predicate].getArity() == 1){
					vector<int> possibleValues;
					
					for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
						vector<int> tuple = supportingPredicateTuples[predicate][i].first;
					
						int myObjIndex = objToIndex[tuple[0]];
						int myParam = predicateArgumentPositions[predicate][i];
						int constantVar = thisSlotParameterVars[myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
						
						possibleValues.push_back(constantVar);
					}
				
					impliesOr(solver,predicateVar,possibleValues);
				} else {
					for (size_t lastPos = 0; lastPos < task.predicates[predicate].getArity() - 1 ; lastPos++){
						map<vector<int>,set<int>> possibleUpto;
				
						// build assignment tuple up to this point
						for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
							vector<int> tuple = supportingPredicateTuples[predicate][i].first;
							vector<int> subTuple;
							subTuple.push_back(predicateVar);
						
							for (size_t j = 0; j <= lastPos; j++){
								// push only the non-constants
								int myObjIndex = objToIndex[tuple[j]];
								int myParam = predicateArgumentPositions[predicate][j];
								int constantVar = thisSlotParameterVars[myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
								
								subTuple.push_back(constantVar);
							}
							
							int myObjIndex = objToIndex[tuple[lastPos + 1]];
							int myParam = predicateArgumentPositions[predicate][lastPos+1];
							int localObjectNumber = myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]];
							//if (localObjectNumber >= parameterVars[time][myParam].size()) cout << "F " << localObjectNumber << " " << parameterVars[time][myParam].size() << endl;
							int constantVar = thisSlotParameterVars[myParam][localObjectNumber];
				
							possibleUpto[subTuple].insert(constantVar);
						}
				
				
						for (auto & x : possibleUpto){
							andImpliesOr(solver,x.first,x.second);
							DEBUG(for (int i : x.first) cout << " - [" << capsule.variableNames[i] << "]";
							for (int i : x.second) cout << " [" << capsule.variableNames[i] << "]";
							cout << endl);
						}
				
						if (lastPos == 0){
							int posOfValue = 1;
							vector<int> initial;
							for (auto & x : possibleUpto)
								initial.push_back(x.first[posOfValue]);
							
							impliesOr(solver,predicateVar,initial);
							DEBUG(cout << "- [" << capsule.variableNames[predicateVar] << "]";
							for (int i : initial) cout << " [" << capsule.variableNames[i] << "]";
							cout << endl);
						}
					}
				}
			}
		}
		//exit(0);
		initSupp += get_number_of_clauses() - bef;
	}
	predicateSlotVariables.push_back(thisTimePredicateSlotVariables);
	argumentSlotVariables.push_back(thisTimeArgumentSlotVariables);
}


void LiftedLinearSAT::generate_goal_assertion(const Task &task, void* solver, sat_capsule & capsule, int width, int time){
	const auto goals = task.goal.goal;
	for (size_t goal = 0; goal < goals.size(); goal++) {
		const auto & goalObjec = goals[goal];
		int predicate = goalObjec.predicate;
	
		if (task.predicates[predicate].isStaticPredicate()){
			// static preconditions must be handled more efficiently
			// i.e. directly via support from init
			// TODO
		} else {
			vector<int> goalSlotVars;
			for (int slot = 0; slot < width; slot++){
				int goalSlotVar = capsule.new_variable();
				goalSlotVars.push_back(goalSlotVar);
				DEBUG(capsule.registerVariable(goalSlotVar,to_string(time) + " @ goal " + to_string(goal) + " slot " + to_string(slot) + " pred " + task.predicates[predicate].getName()));
	
				// if we select this slot, we actually have to have the correct fact there
				implies(solver, goalSlotVar, predicateSlotVariables[time][slot][predicate]);
	
				// iterate over the arguments of the precondition
				for (size_t iArg = 0; iArg < goalObjec.args.size(); iArg++){
					int preconditionVar = goalObjec.args[iArg];
					int myParam = predicateArgumentPositions[predicate][iArg];
	
					int myObjIndex = objToIndex[preconditionVar]; 
					int constantVar = argumentSlotVariables[time][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
					implies(solver, goalSlotVar, constantVar); 
				}
			}
			atLeastOne(solver,capsule,goalSlotVars);
		}
	}
}

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

void LiftedLinearSAT::generate_formula(const Task &task, void* solver, sat_capsule & capsule, int width) {
	bool generateBaseFormula = true; // this is for later. Set to false for incremental?

	int bef = get_number_of_clauses();
	// indices: timestep -> parameter -> object
	int time = planLength-1;
	cout << "Generating time = " << setw(3) << time << endl;


	/// action variables
	std::vector<int> actionVarsTime;
	std::vector<std::vector<int>> parameterVarsTime(numberOfArgumentPositions);
	DEBUG(cout << "\tGenerating Variables for actions." << endl);
	for (size_t action = 0; action < task.actions.size(); action++){

		int actionVar;
		if (generateBaseFormula){  
			actionVar = capsule.new_variable();
			actionVarsTime.push_back(actionVar);
			DEBUG(capsule.registerVariable(actionVar,to_string(time) + " @ action" + "-" + task.actions[action].get_name()));
		} else {
			actionVar = actionVars[time][action];
		}
	}
	// add variables to overall list (needed for later retrieval)
	actionVars.push_back(actionVarsTime);
	if (generateBaseFormula) atMostOne(solver,capsule,actionVarsTime);
	//if (generateBaseFormula) atLeastOne(solver,capsule,actionVarsTime);

	// generate nullary variables
	std::unordered_map<int,int> currentNullary;


	// generate	varialbes for the action parameters
	if (generateBaseFormula){
		for (int n : task.nullary_predicates){
			int nullVar = capsule.new_variable();
			currentNullary[n] = nullVar;
			DEBUG(capsule.registerVariable(nullVar,	to_string(time) + " @ nullary#" + to_string(n)));
		}

		//// code for maintenance of truth of init
		//std::vector<int> initNotTrueAfterThis;
		//for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
		//    auto rel = task.initial_state.get_relations()[i];
		//    auto tuple = task.initial_state.get_tuples_of_relation(i);
		//	
		//	for (size_t j = 0; j < tuple.size(); j++){
		//		int initAtom = capsule.new_variable();
		//		DEBUG(capsule.registerVariable(initAtom, to_string(time) +"@initAtomFalseAfter" + "#" + to_string(i) + "-" + to_string(j)));
		//		// if init atom as false after previous step, it is false now!
		//		if (initNotTrueAfter.size())
		//			implies(solver,initNotTrueAfter.back()[initNotTrueAfterThis.size()],initAtom);
		//		initNotTrueAfterThis.push_back(initAtom);
		//	}
		//}
		//initNotTrueAfter.push_back(initNotTrueAfterThis);
		//bef = get_number_of_clauses();
		//variableInitMaintenance += get_number_of_clauses() - bef;

    	for (int paramter = 0; paramter < numberOfArgumentPositions; paramter++){
			int type = typeOfArgument[paramter];
			int lower = lowerTindex[type];
			int upper = upperTindex[type];
			
			parameterVarsTime[paramter].resize(upper - lower + 1);

			for (int o = 0; o < upper - lower + 1; o++){
				int objectVar = capsule.new_variable();
				parameterVarsTime[paramter][o] = objectVar;
				DEBUG(capsule.registerVariable(objectVar, to_string(time) + " @ param#" + to_string(paramter) + " = const " + task.objects[indexToObj[o + lower]].getName()));
			}
			// each parameter can have at most one value
			atMostOne(solver,capsule,parameterVarsTime[paramter]);
		}
		parameterVars.push_back(parameterVarsTime);

		atMostOneParamterValue += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();
	}

	/// action variables
	bef = get_number_of_clauses();
	for (size_t action = 0; action < task.actions.size(); action++){
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);
		

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
				DEBUG(cout << "Typing " << actionVar << ":"; for(auto x : allowed) cout << " " << x; cout << endl;);
				impliesOr(solver,actionVar,allowed);
          	}
		}
	}
	actionTyping += get_number_of_clauses() - bef;

	generate_predicate_slot_layer(task, solver, capsule, width, time+1); // generate effect slots
	vector<vector<vector<int>>> equalBefore = generate_action_state_equality(task, solver, capsule, width, time, time);
	vector<vector<vector<int>>> equalAfter = generate_action_state_equality(task, solver, capsule, width, time, time+1);


	// preconditions are actually met
	bef = get_number_of_clauses();
	for (size_t action = 0; action < task.actions.size(); action++){
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);

		const auto precs = task.actions[action].get_precondition();
        for (size_t prec = 0; prec < precs.size(); prec++) {
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 

			if (task.predicates[predicate].isStaticPredicate()){
				// static preconditions must be handled more efficiently
				// i.e. directly via support from init

				// consider how many arguments are there
				if (task.predicates[predicate].getArity() == 1){
					vector<int> possibleValues;
					
					DEBUG(cout << "YY " << capsule.variableNames[actionVar]);
					for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
						vector<int> tuple = supportingPredicateTuples[predicate][i].first;
						int myObjIndex = objToIndex[tuple[0]];
						int preconditionVar = precObjec.arguments[0].index;
						
						if (precObjec.arguments[0].constant){
							if (preconditionVar == tuple[0])
								possibleValues.push_back(actionVar); // represents a true clause, i.e. no restriction.
							// otherwise no option, so don't do this
						} else {
							int argPos = actionArgumentPositions[action][preconditionVar];
							int lower = lowerTindex[typeOfArgument[argPos]];
							int constantVar = parameterVarsTime[argPos][myObjIndex - lower];
							possibleValues.push_back(constantVar);

							DEBUG(cout << " " << capsule.variableNames[constantVar]);
						}
					}
					DEBUG(cout << endl);
					
					impliesOr(solver, actionVar, possibleValues); 
				} else {
					for (size_t lastPos = 0; lastPos < task.predicates[predicate].getArity() - 1 ; lastPos++){
						map<vector<int>,set<int>> possibleUpto;
				
						// build assignment tuple up to this point
						for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
							vector<int> tuple = supportingPredicateTuples[predicate][i].first;
							vector<int> subTuple;
							subTuple.push_back(actionVar);

							bool impossible = false;
							int nextConstantVar = -1;
						
							for (size_t j = 0; j <= lastPos+1; j++){
								// push only the non-constants
								int preconditionVar = precObjec.arguments[j].index;
								
								if (precObjec.arguments[j].constant){
									if (preconditionVar != tuple[j])
										impossible = true;
									// otherwise this will always be good
								} else {
									int myObjIndex = objToIndex[tuple[j]];
									int argPos = actionArgumentPositions[action][preconditionVar];
									int lower = lowerTindex[typeOfArgument[argPos]];
									int constantVar = parameterVarsTime[argPos][myObjIndex - lower];
									if (j == lastPos+1)
										nextConstantVar = constantVar;
									else
										subTuple.push_back(constantVar);
								}
							}
							
							if (!impossible) possibleUpto[subTuple].insert(nextConstantVar);
						}
				
				
						for (auto & x : possibleUpto){
							andImpliesOr(solver,x.first,x.second);
							DEBUG(for (int i : x.first) cout << " - [" << capsule.variableNames[i] << "]";
							for (int i : x.second) cout << " [" << capsule.variableNames[i] << "]";
							cout << endl);
						}
				
						if (lastPos == 0){
							int posOfValue = 1;
							vector<int> initial;
							for (auto & x : possibleUpto)
								initial.push_back(x.first[posOfValue]);
							
							impliesOr(solver,actionVar,initial);
						}
					}
				}
	

			} else {
				vector<int> precSlotVars;
				for (int slot = 0; slot < width; slot++){
					int precSlotVar = capsule.new_variable();
					precSlotVars.push_back(precSlotVar);
					DEBUG(capsule.registerVariable(precSlotVar,to_string(time) + " @ action " + task.actions[action].get_name() + " prec " + to_string(prec) + " slot " + to_string(slot)));
					
					implies(solver, -actionVar, -precSlotVar);

					// if we select this slot, we actually have to have the correct fact there
					andImplies(solver, actionVar, precSlotVar, predicateSlotVariables[time][slot][predicate]);

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < precObjec.arguments.size(); iArg++){
						int preconditionVar = precObjec.arguments[iArg].index;
						const bool pIsConst = precObjec.arguments[iArg].constant;
						int myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar = argumentSlotVariables[time][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							andImplies(solver, actionVar, precSlotVar, constantVar); 
						} else {
							// variable equality
							andImplies(solver, actionVar, precSlotVar, equalBefore[actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
				}


				impliesOr(solver,actionVar,precSlotVars);
			}
		}
	}
	precSupport += get_number_of_clauses() - bef;


	vector<vector<int>> slotsSupporter(width);

	// adding effects
	bef = get_number_of_clauses();
	for (size_t action = 0; action < task.actions.size(); action++){
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);

		const auto effs = task.actions[action].get_effects();
        for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 


			if (effObjec.negated){
				// must not be present in any of the slots
				for (int slot = 0; slot < width; slot++){
					set<int> equalFact;
					equalFact.insert(actionVar);
					equalFact.insert(predicateSlotVariables[time+1][slot][predicate]);

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
						int preconditionVar = effObjec.arguments[iArg].index;
						const bool pIsConst = effObjec.arguments[iArg].constant;
						int myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar = argumentSlotVariables[time+1][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							equalFact.insert(constantVar); 
						} else {
							// variable equality
							equalFact.insert(equalAfter[actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
					notAll(solver,equalFact);
				}
			} else {
				vector<int> effSlotVars;
				for (int slot = 0; slot < width; slot++){
					int effSlotVar = capsule.new_variable();
					effSlotVars.push_back(effSlotVar);
					slotsSupporter[slot].push_back(effSlotVar);
					DEBUG(capsule.registerVariable(effSlotVar,to_string(time) + " @ action " + task.actions[action].get_name() + " eff " + to_string(eff) + " slot " + to_string(slot) + " pred " + task.predicates[predicate].getName()));


					implies(solver, -actionVar, -effSlotVar);

					// if we select this slot, we actually have to have the correct fact there
					andImplies(solver, actionVar, effSlotVar, predicateSlotVariables[time+1][slot][predicate]);
					cout << "YY " << actionVar << " " << effSlotVar << " " << predicateSlotVariables[time+1][slot][predicate] << endl; 

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
						int preconditionVar = effObjec.arguments[iArg].index;
						const bool pIsConst = effObjec.arguments[iArg].constant;
						int myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar = argumentSlotVariables[time+1][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							// XXX
							andImplies(solver, actionVar, effSlotVar, constantVar); 
						} else {
							// variable equality
							andImplies(solver, actionVar, effSlotVar, equalAfter[actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
				}

				// we don't need to force that we have that effect ...
				//impliesOr(solver,actionVar,effSlotVars);
			}
		}
	}
	precSupport += get_number_of_clauses() - bef;

	// frame axioms	
	for (int slot = 0; slot < width; slot++){
		//continue; // XXX
		// idea: either the slot got overridden by an effect or is it the same as the slot before
		int slotEqual = capsule.new_variable();
		DEBUG(capsule.registerVariable(slotEqual,to_string(time) + " = " + to_string(time+1) + " @ slot " + to_string(slot)));
		
		// same predicate
		for (size_t pred = 0; pred < task.predicates.size(); pred++){
			int predBefore = predicateSlotVariables[time  ][slot][pred];
			int predAfter  = predicateSlotVariables[time+1][slot][pred];
			if (predBefore == -1) continue;

			andImplies(solver,slotEqual, predBefore, predAfter);
			andImplies(solver,slotEqual, predAfter, predBefore);
			//andImplies(solver,predBefore, predAfter, slotEqual);  maintenance does not have to be exact -- don't use this one. It actually makes things incorrect
		}
		
	   	
		for (int factParameter = 0; factParameter < numberOfPredicateArgumentPositions; factParameter++){
			int lower = lowerTindex[typeOfPredicateArgument[factParameter]];
			int upper = upperTindex[typeOfPredicateArgument[factParameter]];
	
			for(int o = 0; o < numObjs; o++){
				if (o < lower || o > upper)
					continue;

				// need to subtract the starting values of the types
				int constBefore = argumentSlotVariables[time  ][slot][factParameter][o-lower];
				int constAfter  = argumentSlotVariables[time+1][slot][factParameter][o-lower];
				andImplies(solver,slotEqual, constBefore, constAfter);
				andImplies(solver,slotEqual, constAfter, constBefore);
				//andImplies(solver,constBefore, constAfter, slotEqual); maintenance does not have to be exact -- don't use this one. It actually makes things incorrect

			}
		}

		notImpliesOr(solver, slotEqual, slotsSupporter[slot]);
	}
}


bool LiftedLinearSAT::callSolver(sat_capsule & capsule, void* solver, const Task &task, const std::clock_t & startTime, long long time_limit_in_ms){
		
	DEBUG(capsule.printVariables());

	cout << "Generated Variables " << setw(10) << capsule.number_of_variables <<
		" Clauses: " << setw(10) << get_number_of_clauses() << " length " << planLength << endl;
	cout << "\tone action         " << setw(9) << oneAction << endl; 
	cout << "\tmax 1 param value  " << setw(9) << atMostOneParamterValue << endl;
	cout << "\tmax 1 predicate    " << setw(9) << atMostOnePredicate << endl;
	cout << "\tinit maintain      " << setw(9) << variableInitMaintenance << endl;
	cout << "\tprec support       " << setw(9) << precSupport << endl;
	cout << "\tequals             " << setw(9) << equals << endl;
	cout << "\tinit support       " << setw(9) << initSupp << endl;
	cout << "\tstatic init support" << setw(9) << staticInitSupp << endl;
	cout << "\ttyping actions     " << setw(9) << actionTyping << endl;
	cout << "\ttyping predicates  " << setw(9) << predicateTyping << endl;
	cout << "\tequals precs       " << setw(9) << equalsPrecs << endl; 
	cout << "\tachiever           " << setw(9) << achieverImplications << endl; 
	cout << "\tno deleter         " << setw(9) << noDeleter << endl; 
	cout << "\tgoal achievers     " << setw(9) << goalAchiever << endl; 
	cout << "\tgoal deleters      " << setw(9) << goalDeleter << endl; 
	cout << "\tnullary            " << setw(9) << nullary << endl;


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
}



utils::ExitCode LiftedLinearSAT::solve(const Task &task, int limit, bool optimal, bool incremental) {

	cout << "You made a terrible mistake!!" << endl;


	bool satisficing = !optimal;

	//if (satisficing){
	//	DEBUG(cout << "Parameter arity " << maxActionArity << " Objects " << task.objects.size() << endl);
	//
	//
	//	vector<int> planLenghtsToTry;
	//	if (limit == -1){
	//		planLenghtsToTry.push_back(10);
	//		planLenghtsToTry.push_back(25);
	//		planLenghtsToTry.push_back(50);
	//		planLenghtsToTry.push_back(100);
	//		planLenghtsToTry.push_back(200);
	//	} else
	//		planLenghtsToTry.push_back(limit);
	//

	//	long long overall_time_limit = 30*60*1000;

	//	std::clock_t overall_start = std::clock();
	//	double overall_start_in_ms = 1000.0 * (overall_start) / CLOCKS_PER_SEC;
	//	cout << endl << "\t\t #### Current time " << setw(10) << overall_start_in_ms  << endl;

	//	for (int currentLimitIndex = 0; currentLimitIndex < int(planLenghtsToTry.size()); currentLimitIndex++){
	//		maxLen = planLenghtsToTry[currentLimitIndex];
	//		std::clock_t start = std::clock();
	//		double already_used_time_is_ms = 1000.0 * (start - overall_start) / CLOCKS_PER_SEC;
	//		double remaining_time_is_ms = overall_time_limit - already_used_time_is_ms;
	//		double my_time_slice = remaining_time_is_ms / (planLenghtsToTry.size() - currentLimitIndex);
	//		cout << endl << "\t\t #### Starting plan length " << setw(5) << maxLen << " time limit " << setw(10) << my_time_slice << endl;

	//
	//		// start the incremental search for a plan	
	//		void* solver;
	//		if (incremental)
	//			solver = ipasir_init();
	//		sat_capsule capsule;
	//		
	//		for (int pastLimit = 1; pastLimit < maxLen + 1; pastLimit++){
	//			if (!incremental) {// create a new solver instance for every ACD
	//				solver = ipasir_init();
	//				capsule.number_of_variables = 0;
	//				DEBUG(capsule.variableNames.clear());
	//				reset_number_of_clauses();


	//				// reset formula size counters
	//				actionTyping = 0;
	//				atMostOneParamterValue = 0;
	//				variableInitMaintenance = 0;
	//				precSupport = 0;
	//				equals = 0;
	//				initSupp = 0;
	//				nullary = 0;
	//				equalsPrecs = 0; 
	//				achieverImplications = 0; 
	//				staticInitSupp = 0;
	//				noDeleter = 0; 
	//				oneAction = 0; 
	//				goalAchiever = 0; 
	//				goalDeleter = 0; 
	//			}

	//			
	//			cout << endl << "Maximum Achiever Consumer Distance (ACD) " << setw(5) << pastLimit << endl;
	//			cout << "===================================================="  << endl;
	//		
	//			int maxPlanLength = maxLen + 2;
	//			solverTotal = 0;

	//			if (!incremental){
	//				goalSupporterVars.clear();
	//				parameterVars.clear();
	//				initNotTrueAfter.clear();
	//				actionVars.clear();
	//				parameterEquality.clear();
	//				precSupporter.clear();
	//				precSupporterOver.clear();
	//			}

	//			if (pastLimit == 1 || !incremental){
	//				// the goal must be achieved!
	//				int gc = 0;
	//				for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
	//					const AtomicGoal & goalAtom = task.goal.goal[goal];
	//					std::vector<int> goalSupporter;
	//					
	//					if (goalAtom.negated) {
	//						goalSupporterVars.push_back(goalSupporter);
	//						continue; // TODO don't know what to do ...
	//					}
	//					gc++;

	//					//ActionPrecAchiever* thisGoalAchievers = goalAchievers->precAchievers[goal];
	//				
	//					for (int pTime = 0; pTime < maxPlanLength+1; pTime++){
	//						int goalSuppVar = capsule.new_variable();
	//						goalSupporter.push_back(goalSuppVar);
	//						DEBUG(capsule.registerVariable(goalSuppVar, "goalSupp#" + to_string(goal) + "-" + to_string(pTime-1)));

	//					}
	//					if (atom_not_satisfied(task.initial_state,goalAtom)) assertNot(solver,goalSupporter[0]);	
	//					
	//					atLeastOne(solver,capsule,goalSupporter);
	//					goalSupporterVars.push_back(goalSupporter);
	//				}

	//				// we only test executable plans and if the goal is a dead end ...
	//				//if (!gc) return 0;

	//				
	//				for (int n : task.nullary_predicates){
	//					int nullaryInInit = capsule.new_variable();
	//					lastNullary[n] = nullaryInInit;
	//					DEBUG(capsule.registerVariable(nullaryInInit,
	//								"nullary#" + to_string(n) + "_" + to_string(-1)));

	//					if (task.initial_state.get_nullary_atoms()[n])
	//						assertYes(solver,nullaryInInit);
	//					else
	//						assertNot(solver,nullaryInInit);
	//				}
	//			}

	//		
	//			planLength = 0;
	//			while (planLength < maxLen){
	//				planLength++;
	//				generate_formula(task,start,solver,capsule,true,false,!incremental,incremental,pastLimit);
	//			}
	//			planLength++;
	//			if (generate_formula(task,start,solver,capsule,false,false,!incremental,incremental,pastLimit, my_time_slice)){
	//				ipasir_release(solver);
	//				cout << "\t\tPlan of length: " << planLength << endl;
	//				DEBUG(cout << "\t\tPlan of length: " << planLength << endl);
	//				return utils::ExitCode::SUCCESS;
	//			} else {
	//				cout << "\t\tNo plan of length: " << planLength << endl;
	//				DEBUG(cout << "\t\tNo plan of length: " << planLength << endl);
	//				std::clock_t end = std::clock();
	//				double time_in_ms = 1000.0 * (end-start) / CLOCKS_PER_SEC;
	//				if (time_in_ms >= my_time_slice){
	//					ipasir_release(solver);
	//					// if we are the last length to try and timed out ...
	//					if (planLenghtsToTry.size() - 1 == currentLimitIndex)
	//						return utils::ExitCode::SEARCH_OUT_OF_TIME;
	//					else
	//						break; // exit the loop iterating over past limits
	//				}
	//			}
	//			if (!incremental)
	//				ipasir_release(solver);
	//		}
	//	}
	//} else {
	

		int width = 10;
		if (limit == -1) maxLen = 9999999; else maxLen = limit;
		void* solver;
		sat_capsule capsule;
		if (incremental){
			solver = ipasir_init();
			planLength = 0;
		}
		
		for (int i = 10; i < maxLen; i++){
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
			// TODO
			//if (!incremental || i == 0){

			//	// the goal must be achieved!
			//	int gc = 0;
			//	int clausesBefore = get_number_of_clauses();
			//	for (size_t goal = 0; goal < task.goal.goal.size(); goal++){
			//		const AtomicGoal & goalAtom = task.goal.goal[goal];
			//		std::vector<int> goalSupporter;
			//		
			//		if (goalAtom.negated) {
			//			goalSupporterVars.push_back(goalSupporter);
			//			continue; // TODO don't know what to do ...
			//		}
			//		gc++;

			//		//ActionPrecAchiever* thisGoalAchievers = goalAchievers->precAchievers[goal];
			//	
			//		for (int pTime = 0; pTime < maxPlanLength+1; pTime++){
			//			int goalSuppVar = capsule.new_variable();
			//			goalSupporter.push_back(goalSuppVar);
			//			DEBUG(capsule.registerVariable(goalSuppVar,
			//						"goalSupp#" + to_string(goal) + "-" + to_string(pTime-1)));

			//		}
			//		if (atom_not_satisfied(task.initial_state,goalAtom)) assertNot(solver,goalSupporter[0]);	
			//		
			//		atLeastOne(solver,capsule,goalSupporter);
			//		goalSupporterVars.push_back(goalSupporter);
			//	}
			//	goalAchiever += get_number_of_clauses() - clausesBefore;
			//	clausesBefore = get_number_of_clauses();

			//	// we only test executable plans and if the goal is a dead end ...
			//	if (!gc) return utils::ExitCode::SEARCH_UNSOLVABLE;

			//
			//	for (int n : task.nullary_predicates){
			//		int nullaryInInit = capsule.new_variable();
			//		lastNullary[n] = nullaryInInit;
			//		DEBUG(capsule.registerVariable(nullaryInInit,
			//					"nullary#" + to_string(n) + "_" + to_string(-1)));

			//		if (task.initial_state.get_nullary_atoms()[n])
			//			assertYes(solver,nullaryInInit);
			//		else
			//			assertNot(solver,nullaryInInit);
			//	}
			//	nullary += get_number_of_clauses() - clausesBefore;
			//}


			// start the incremental search for a plan	
			
			
			// if not in incremental mode, we need to generate the formula for all timesteps.
			if (!incremental){
				planLength = 0;
				generate_predicate_slot_layer(task, solver, capsule, width, 0); // generate slots directly after init
			}
			
			bool linearIncrease = true;
			if (!linearIncrease){
				while (planLength <= (1 << i)-1){
					planLength++;
					generate_formula(task,solver,capsule,width);
				}
			} else {
				while (planLength <= i){
					planLength++;
					generate_formula(task,solver,capsule,width);
				}
			}

			generate_goal_assertion(task, solver, capsule, width, planLength);


			if (callSolver(capsule,solver,task,start)){
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

			exit(0);
		}
	//}
	return utils::ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
}

int LiftedLinearSAT::sortObjs(int index, int type) {
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

int LiftedLinearSAT::actionID(int i) {
    return (maxActionArity + 1) * i;
}

int LiftedLinearSAT::paramID(int i, int j) {
    return (maxActionArity + 1) * i + (j + 1);
}
