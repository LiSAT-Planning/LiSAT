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

extern int clauseCount;

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


set<pair<int,int>> possibleBeforeEquals;
set<pair<int,int>> possibleAfterEquals;

// predicate maps to 
map<int,set<pair<int,int>>> perPredicatePossibleBeforeEquals;
map<int,set<pair<int,int>>> perPredicatePossibleAfterEquals;


int calculateEffectBalance(const Task & task, const ActionSchema & action, const Atom & effObjec, bool conservativeDeletes = false){
	int predicate = effObjec.predicate_symbol;

	// maybe we have an overriding adding effect
	if (effObjec.negated){
		bool overriding = false;
		const auto & effs = action.get_effects();
    	for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & eff2 = effs[eff];
			if (eff2.negated) continue; // must be a positive effect
			int eff2Predicate = eff2.predicate_symbol;
			if (eff2Predicate != predicate) continue;

			bool bad = false;
			for (size_t i = 0; !bad && i < eff2.arguments.size(); i++){
				if (eff2.arguments[i].index != effObjec.arguments[i].index) bad = true;
				if (eff2.arguments[i].constant != effObjec.arguments[i].constant) bad = true;
			}
			if (!bad) overriding = true;
		}
		if (overriding) return 0;	
	}


	// search for it in the preconditions -- note: the preconditions are always positive only!
	bool balancer = false;
	const auto & precs = action.get_precondition();
    for (size_t prec = 0; prec < precs.size(); prec++) {
		const auto & precObjec = precs[prec];
		int prePredicate = precObjec.predicate_symbol;
		if (prePredicate != predicate) continue;
		bool bad = false;
		for (size_t i = 0; !bad && i < precObjec.arguments.size(); i++){
			if (precObjec.arguments[i].index != effObjec.arguments[i].index) {
				bad = true;
			}
			if (precObjec.arguments[i].constant != effObjec.arguments[i].constant) {
				bad = true;
			}
		}
		if (!bad) balancer = true;
	}

	//cout << "EFF " << eff << " " << balancer << " " << effObjec.negated << endl;
	
	if (effObjec.negated){
		// deleting effect takes only guaranteed effect if we have a precondition on it!
		if (balancer || conservativeDeletes) return -1;
	} else {
		// adding effect may take effect if it is not yet true 
		if (!balancer) return 1;
	}
	return 0;
}


int calculateNullaryEffectBalance(const Task & task, int action, int pIndex){
	if (task.actions[action].get_positive_nullary_effects()[pIndex] && !task.actions[action].get_positive_nullary_precond()[pIndex])
		return 1;
	if (task.actions[action].get_negative_nullary_effects()[pIndex] && !task.actions[action].get_negative_nullary_precond()[pIndex])
		return -1;
	return 0;
}



int calculateOverallBalanceOfPredicate(const Task & task, int pIndex){
	auto p = task.predicates[pIndex];
	if (p.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment

	DEBUG(cout << endl << endl << "Predicate " << p.getName() << endl);
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
		DEBUG(cout << "Action " << action << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	DEBUG(cout  << "maximumNetChange = " << maximumNetChange << endl);
	return maximumNetChange;
}


int calculateOverallBalanceOfPredicatePair(const Task & task, int pIndex, int pIndex2){
	auto p = task.predicates[pIndex];
	auto p2 = task.predicates[pIndex2];
	if (p.getArity() + p2.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment
	if (p2.isStaticPredicate()) return 0; // static predicates get special treatment

	DEBUG(cout << endl << endl << "Predicate " << p.getName() << " Predicate " << p2.getName() << endl);
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex && predicate != pIndex2) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
		if (p.getArity() == 0){
			int thisChange = calculateNullaryEffectBalance(task,action, pIndex);
			DEBUG(cout << "\tEff " << task.predicates[pIndex].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
		if (p2.getArity() == 0){
			int thisChange = calculateNullaryEffectBalance(task,action, pIndex2);
			DEBUG(cout << "\tEff " << task.predicates[pIndex2].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}

		DEBUG(cout << "Action " << action << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	DEBUG(cout  << "maximumNetChange = " << maximumNetChange << endl);
	return maximumNetChange;
}

int calculateOverallBalanceOfPredicateSet(const Task & task, set<int> pIndices){
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (pIndices.count(predicate) == 0) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}

		DEBUG(cout << "Action " << action << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	DEBUG(cout  << "maximumNetChange = " << maximumNetChange << endl);
	return maximumNetChange;
}

int calculateOverallBalanceOfPredicateAndNullary(const Task & task, int pIndex, vector<int> arityZeroPredicates){
	auto p = task.predicates[pIndex];
	if (p.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment

	DEBUG(cout << endl << endl << "Predicate " << p.getName() << endl);
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}

		for (int arityZeroPredicate : arityZeroPredicates){
			int thisChange = calculateNullaryEffectBalance(task,action, arityZeroPredicate);
			DEBUG(cout << "\tEff " << task.predicates[arityZeroPredicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
		
		DEBUG(cout << "Action " << task.actions[action].get_name() << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	DEBUG(cout  << "maximumNetChange = " << maximumNetChange << endl);
	return maximumNetChange;
}


int calculateOverallBalanceOfAction(const Task & task, int action, set<int> consideredPredicates){
	const auto effs = task.actions[action].get_effects();
	int netChange = 0;
	for (size_t eff = 0; eff < effs.size(); eff++) {
		int predicate = effs[eff].predicate_symbol;
		if (consideredPredicates.count(predicate) == 0) continue;

		int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
		DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
		netChange += thisChange;
	}
	DEBUG(cout << "Action " << task.actions[action].get_name() << " balance " << netChange << endl);
	return netChange;
}

int calculateOverallBalanceOfNullary(const Task & task, vector<int> arityZeroPredicates){
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		int netChange = 0;	
		for (int arityZeroPredicate : arityZeroPredicates){
			int thisChange = calculateNullaryEffectBalance(task,action, arityZeroPredicate);
			DEBUG(cout << "\tEff " << task.predicates[arityZeroPredicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
		
		DEBUG(cout << "Action " << task.actions[action].get_name() << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	DEBUG(cout  << "maximumNetChange = " << maximumNetChange << endl);
	return maximumNetChange;
}


int calculateOverallBalanceOfNullaryAndNormal(const Task & task, vector<int> arityZeroPredicates, set<int> normalPredicates){
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		int netChange = 0;	
		for (int arityZeroPredicate : arityZeroPredicates){
			int thisChange = calculateNullaryEffectBalance(task,action, arityZeroPredicate);
			DEBUG(cout << "\tEff " << task.predicates[arityZeroPredicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}

		const auto effs = task.actions[action].get_effects();
		for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (normalPredicates.count(predicate) == 0) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
	
		DEBUG(cout << "Action " << task.actions[action].get_name() << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	DEBUG(cout  << "maximumNetChange = " << maximumNetChange << endl);
	return maximumNetChange;
}


int calculateOverallBalanceOfPredicateInPhasing(const Task & task, int pIndex, vector<int> phasingPredicates){
	auto p = task.predicates[pIndex];
	if (p.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment
	DEBUG(cout << endl << endl << "Predicate " << p.getName() << endl);

	
	// TODO this is not actually correct. I assume that the phasing structure is a cycle .... but it might not be

	map<int,set<int>> changesOnPhaseLeave;

	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			DEBUG(cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl);
			netChange += thisChange;
		}
		
		int leavingPhase = -1;
		// check whether we leaving a phase
		for (int phasingPredicate : phasingPredicates){
			int thisChange;
			if (task.predicates[phasingPredicate].getArity() == 0)
				thisChange = calculateNullaryEffectBalance(task, action, phasingPredicate);
			else{
				set<int> __singleton; __singleton.insert(phasingPredicate);
				thisChange = calculateOverallBalanceOfAction(task,action,__singleton);
			}
			if (thisChange == -1)
				leavingPhase = phasingPredicate;
		}

		if (leavingPhase == -1) {
			if (netChange == 0) {
				DEBUG(cout << "\tAction " << task.actions[action].get_name() << " has net change 0 and does not leave phase. This is ok." << endl);
				continue; // this action does not manipulate predicate p
			}
			DEBUG(cout << "\tAction " << task.actions[action].get_name() << " has net change " << netChange << " and does not leave phase. This is bad." << endl);
			return 1; // might increase ...
		}
		changesOnPhaseLeave[leavingPhase].insert(netChange);
	}
	int increasing = -1;
	for (auto [a,b] : changesOnPhaseLeave){
		DEBUG(cout << "Leave " << a << ":";
		for (auto i : b) cout << " " << i;
		cout << endl);

		if (b.size() > 1) return 1;
		if (*b.begin() > 1) return 1;
		if (*b.begin() == 1) {
			if (increasing != -1) return 1;
			increasing = a;
		}
	}

	return 0;
}


int predicatePairInInit(const Task & task, int pIndex, int pIndex2){
	int numInInit = 0;
    for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
        auto rel = task.initial_state.get_relations()[i];
        auto tuple = task.initial_state.get_tuples_of_relation(i);
        if (task.initial_state.get_relations()[i].predicate_symbol == pIndex){
			numInInit += tuple.size();
		}
        if (task.initial_state.get_relations()[i].predicate_symbol == pIndex2){
			numInInit += tuple.size();
		}
	}
	if (task.predicates[pIndex].getArity() == 0 && task.initial_state.get_nullary_atoms()[pIndex]) numInInit++;
	if (task.predicates[pIndex2].getArity() == 0 && task.initial_state.get_nullary_atoms()[pIndex2]) numInInit++;
	DEBUG(cout << "Size in init " << numInInit << endl);
	return numInInit;
}

int predicateInInit(const Task & task, int pIndex){
	for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
	    auto rel = task.initial_state.get_relations()[i];
	    auto tuple = task.initial_state.get_tuples_of_relation(i);
	    if (task.initial_state.get_relations()[i].predicate_symbol == pIndex){
			DEBUG(cout << "Size in init " << tuple.size() << endl);
			return tuple.size();
		}
	}
	return 0;
}



set<int> predicatesMonotoneNegEncoding;
map<int,int> predicateStable; // maps to size
map<int,int> predicateMaxStable; // maps to size
// maps to all tuples that needs to be tracked
// NOTE: this contains the powerlifted object number and NOT the lisat indices
map<int,set<vector<int>>> predicateNoPreMonotone; 



map<int,set<int>> leavingActions;
vector<int> phaseloop;


LiftedLinearSAT::LiftedLinearSAT(const Task & task, bool inferStructure) {
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
				
				if (predicate != size_t(rel.predicate_symbol)) {
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
				
				if (predicate != size_t(rel.predicate_symbol)) {
					currentStartingPos += tuple.size();
					continue;
				}
			    
				for (vector<int> groundA: tuple) {
			    	mySupportingTuples.push_back({groundA,currentStartingPos++});
			    }
			}
	}


	////////////////////////////////////////////// typing

	map<int,set<int>> typeObjects;
    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++)
			typeObjects[oTypes[i]].insert(obj);
	}
	map<set<int>,int> inverseTypes;
	for (auto [a,b] : typeObjects)
		inverseTypes[b] = a;

	// first step, we need to have a look at the action arguments and whether they are actually any good ...

	for (size_t action = 0; action < task.actions.size(); action++){
		cout << "Action " << task.actions[action].get_name() << " typing" << endl; 
		// initialise the possible argument values
		vector<set<int>> possibleArgumentValues(task.actions[action].get_parameters().size());
		for (size_t p = 0; p < possibleArgumentValues.size(); p++){
			int type = task.actions[action].get_parameters()[p].type;
			possibleArgumentValues[p] = typeObjects[type];
			cout << "\tArgument " << p << " size: " << possibleArgumentValues[p].size() << endl;
		}

		const auto precs = task.actions[action].get_precondition();
        for (size_t pre = 0; pre < precs.size(); pre++) {
			int predicate = precs[pre].predicate_symbol;
			if (!task.predicates[predicate].isStaticPredicate()) continue;
			if (task.predicates[predicate].getArity() == 0) continue;
			//cout << "Action " << task.actions[action].get_name() << " has static precondition on " << task.predicates[predicate].getName() << endl;

			vector<set<int>> possibleValues (task.predicates[predicate].getArity());
			for (auto tuple : supportingPredicateTuples[predicate]){
				for (int i = 0; i < task.predicates[predicate].getArity(); i++)
					possibleValues[i].insert(tuple.first[i]);
			}
			
			for (int i = 0; i < task.predicates[predicate].getArity(); i++){
				if (precs[pre].arguments[i].constant) continue; 
				int argumentIndex = precs[pre].arguments[i].index;

				set<int> intersect;
				set_intersection(possibleArgumentValues[argumentIndex].begin(), possibleArgumentValues[argumentIndex].end(),
								possibleValues[i].begin(), possibleValues[i].end(), std::inserter(intersect, intersect.begin()));

				possibleArgumentValues[argumentIndex] = intersect;
			}
		}
		cout << "===== After applying static preconditions " << endl;
		for (size_t p = 0; p < possibleArgumentValues.size(); p++){
			int originalType = task.actions[action].get_parameters()[p].type;
			cout << "\tArgument " << p << " size: " << possibleArgumentValues[p].size() << endl;
			
			if (possibleArgumentValues[p].size() == 0) continue; 

			int restrictedType;
			if (inverseTypes.count(possibleArgumentValues[p]) != 0){
				restrictedType = inverseTypes[possibleArgumentValues[p]];
				if (restrictedType == originalType) continue;
				cout << "\t\t" << color(COLOR_CYAN,"Found existing better type ") << task.type_names[restrictedType] << endl;
			} else {
				// we have to generate a new type ...
				
				// but we can currently handle only tree-shaped type structure so we can only generate the new type if:
				// - for all other types it is either a subtype or has empty intersection
				
				bool acceptableNewType = true;
				for (auto [elements,_typeID] : inverseTypes){
					set<int> intersect;
					set_intersection(possibleArgumentValues[p].begin(), possibleArgumentValues[p].end(),
								elements.begin(), elements.end(), std::inserter(intersect, intersect.begin()));

					if (intersect.size() == 0) continue;
					if (intersect.size() == elements.size()) continue;
					if (intersect.size() == possibleArgumentValues[p].size()) continue;

					acceptableNewType = false;					
				}

				if (!acceptableNewType){
					cout << "\t\t" << color(COLOR_RED,"Keeping old type as new one would not be acceptable") << endl;
					continue;
				}
				
				restrictedType = task.type_names.size();
				const_cast<Task*>(&task)->type_names.push_back("newType_" + to_string(restrictedType));
				inverseTypes[possibleArgumentValues[p]] = restrictedType;
				cout << "\t\t" << color(COLOR_YELLOW,"Generated better type ") << task.type_names[restrictedType] << endl;

				for (int obj : possibleArgumentValues[p]){
					//DEBUG(cout << "\t\t\tObject " << task.objects[obj].getName() << " add " << restrictedType << endl);
					const_cast<Task*>(&task)->objects[obj].getMutableTypes().push_back(restrictedType);
					//for (int t : task.objects[obj].getTypes())
					//	cout << "\t\t\t\t" << t << endl;
				}
			}
			
			*const_cast<int*>(&task.actions[action].get_parameters()[p].type) = restrictedType;
		}

	}

	/// stability and net change calculations
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
        for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getArity() == 0) continue;

			// search for it in the preconditions
			bool balancer = false;
		    for (size_t prec = 0; prec < precs.size(); prec++) {
				const auto & precObjec = precs[prec];
				int prePredicate = precObjec.predicate_symbol;
				if (prePredicate != predicate) continue;

				bool bad = false;
				for (size_t i = 0; !bad && i < precObjec.arguments.size(); i++){
					if (precObjec.arguments[i].index != effObjec.arguments[i].index) bad = true;
					if (precObjec.arguments[i].constant != effObjec.arguments[i].constant) bad = true;
				}
				if (!bad) balancer = true;
			}

			DEBUG(cout << "EFF " << eff << " " << balancer << " " << effObjec.negated << endl);
			
			if (effObjec.negated){
				if (balancer) netChange--;
			} else {
				if (!balancer) netChange++;
			}
		}
		DEBUG(cout << "Action " << action << " balance " << netChange << endl);
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}

	DEBUG(cout << "maximumNetChange = " << maximumNetChange << endl);


	foundOrdinaryPredicate = false;
	set<int> ordinaryPredicates;
	if (inferStructure){
		map<int,int> stablePredicates;
		map<int,int> maxStablePredicates;

		for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
			if (task.predicates[pIndex].getArity() == 0) continue;
			if (task.predicates[pIndex].isStaticPredicate()) continue; // static predicates get special treatment
			int netChange = calculateOverallBalanceOfPredicate(task, pIndex);
			int inInit = predicateInInit(task, pIndex);

			if (netChange == 0){
				cout << color(COLOR_GREEN, "Found stable predicate ") << task.predicates[pIndex].getName() << endl;
				stablePredicates[pIndex] = inInit;
			}
		}

		vector<int> allArityZeroPredicates;
		vector<int> allArityNonZeroPredicates;
		for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++){
			if (task.predicates[pIndex].isStaticPredicate()) continue; // static predicates get special treatment
			if (task.predicates[pIndex].getArity() == 0) allArityZeroPredicates.push_back(pIndex);
			else allArityNonZeroPredicates.push_back(pIndex);
		}
		cout << "Found Nullaries: " << allArityZeroPredicates.size() << " and Non-Nullaries: " << allArityNonZeroPredicates.size() << endl; 

		vector<int> phasingStructure;
		for (int s = 1; s < (1 << (allArityZeroPredicates.size())); s++){
			vector<int> thisList;
			int initially = 0;
			for (unsigned int i = 0; i < allArityZeroPredicates.size(); i++)
				if (s & (1 << i)) {
					thisList.push_back(allArityZeroPredicates[i]);
					initially += task.initial_state.get_nullary_atoms()[allArityZeroPredicates[i]];
				}

			if (initially != 1) continue;

			int netChange = calculateOverallBalanceOfNullary(task,thisList);

			if (netChange == 0){
				if (thisList.size() > phasingStructure.size()){
					phasingStructure = thisList;
				}
			} else {
				DEBUG(cout << "Testing ...";
				for (int i : thisList)
					cout << " " << task.predicates[i].getName();
				cout << endl);
				for (int ss = 1; ss < (1 << (allArityNonZeroPredicates.size())); ss++){
					if (__builtin_popcount(ss) >= 4) continue;
					set<int> normalList;
					int myinitially = initially;
					for (unsigned int i = 0; i < allArityNonZeroPredicates.size(); i++)
						if (ss & (1 << i)) {
							normalList.insert(allArityNonZeroPredicates[i]);
							myinitially += predicateInInit(task,allArityNonZeroPredicates[i]);
						}
					if (myinitially != 1) continue;
					
					int netChange = calculateOverallBalanceOfNullaryAndNormal(task,thisList, normalList);

					if (netChange == 0){
						if (thisList.size() + normalList.size() > phasingStructure.size()){
							phasingStructure = thisList;
							for (int x : normalList) phasingStructure.push_back(x);
						}
					}
				}
			}
		}

		if (phasingStructure.size() > 0){
			cout << color(COLOR_YELLOW, "Found Plan Phasing Structure:");
			for (int i : phasingStructure)
				cout << " " << task.predicates[i].getName();
			cout << endl;


			// this might be an "absolute" phasing structure, i.e., a case in which every action leaves a phase ..
			map<int,int> enteringActions;
			for (size_t action = 0; action < task.actions.size(); action++){
				const auto effs = task.actions[action].get_effects();
				const auto precs = task.actions[action].get_precondition();
					
				int leavingPhase = -1;
				int enteringPhase = -1;
				// check whether we leaving a phase
				for (int phasingPredicate : phasingStructure){
					int thisChange;
					if (task.predicates[phasingPredicate].getArity() == 0)
						thisChange = calculateNullaryEffectBalance(task, action, phasingPredicate);
					else{
						set<int> __singleton; __singleton.insert(phasingPredicate);
						thisChange = calculateOverallBalanceOfAction(task,action,__singleton);
					}
					if (thisChange == -1)
						leavingPhase = phasingPredicate;
					else if (thisChange == 1)
						enteringPhase = phasingPredicate;
				}
				leavingActions[leavingPhase].insert(action);
				enteringActions[action] = enteringPhase;
			}

			for (auto [phase, actions] : leavingActions){
				if (phase != -1)
					cout << "Phase " << task.predicates[phase].getName() << ":"; 
				else
					cout << "No Phase:";
				for (int action : actions)
					cout << " " << task.actions[action].get_name();
				cout << endl;
			}

			if (leavingActions.count(-1) == 0){
				// determine the initial phase
				int initialPhase = -1;
				for (int phasingPredicate : phasingStructure){
					if (task.predicates[phasingPredicate].getArity() == 0){
						if (task.initial_state.get_nullary_atoms()[phasingPredicate])
							initialPhase = phasingPredicate;
					} else {
						if (predicateInInit(task,phasingPredicate))
							initialPhase = phasingPredicate;
					}
				}

				int curPhase = initialPhase;
				while (curPhase != initialPhase || phaseloop.size() == 0){
					phaseloop.push_back(curPhase);
					int nextPhase = -1;
					bool bad = false;
					for (int leaving : leavingActions[curPhase]){
						if (nextPhase == -1)
							nextPhase = enteringActions[leaving];
						else if (nextPhase != enteringActions[leaving])
							bad = true;
					}
					if (bad){
						phaseloop.clear();
						break;
					}

					curPhase = nextPhase;
				}

				if (phaseloop.size()){
					cout << "Phasing Loop:";
					for (int phase : phaseloop) cout << " " << task.predicates[phase].getName();
					cout << endl;
				}

				//phaseloop.clear();
			}
		}

		// if there is a phasing structure we might use it to get more maxima 	
		if (phasingStructure.size())
			for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
				if (task.predicates[pIndex].getArity() == 0) continue;
				if (task.predicates[pIndex].isStaticPredicate()) continue; // static predicates get special treatment
				
				int netChange = calculateOverallBalanceOfPredicateInPhasing(task,pIndex,phasingStructure);
				if (netChange == 0){
					cout << task.predicates[pIndex].getName() << color(COLOR_RED, " Net Phasing: ") << netChange << endl;
					maxStablePredicates[pIndex] = predicateInInit(task,pIndex) + 1; // +1 for the potential net change
				}
			}

		//exit(0);


		//for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
		//	if (task.predicates[pIndex].getArity() == 0) continue;
		//	if (task.predicates[pIndex].isStaticPredicate()) continue; // static predicates get special treatment
		//	for (unsigned int s = 1; s < (1 << (allArityZeroPredicates.size())); s++){
		//		vector<int> thisList;
		//		for (unsigned int i = 0; i < allArityZeroPredicates.size(); i++)
		//			if (s & (1 << i)) thisList.push_back(allArityZeroPredicates[i]);

		//		int netChange = calculateOverallBalanceOfPredicateAndNullary(task,pIndex,allArityZeroPredicates);
		//		if (netChange == 0)
		//			cout << task.predicates[pIndex].getName() << color(COLOR_RED, " Net Change: ") << netChange;
		//		else
		//			cout << task.predicates[pIndex].getName() << " Net Change: " << netChange;
		//		for (int i : thisList)
		//			cout << " " << task.predicates[i].getName();
		//		cout << endl;
		//	}
		//}




		////////////////////////////////////////////////////////////////////////////////////////
		for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
			if (task.predicates[pIndex].getArity() == 0) continue;
			if (task.predicates[pIndex].isStaticPredicate()) continue; // static predicates get special treatment
			for (int pIndex2 = pIndex+1; pIndex2 < int(task.predicates.size()); pIndex2++) {
				if (task.predicates[pIndex2].getArity() == 0) continue;
				if (task.predicates[pIndex2].isStaticPredicate()) continue; // static predicates get special treatment
				
				int netChange = calculateOverallBalanceOfPredicatePair(task, pIndex, pIndex2);
				int inInit = predicatePairInInit(task, pIndex, pIndex2);

				if (netChange == 0){
					cout << color(COLOR_GREEN, "Found stable predicate pair ") << task.predicates[pIndex].getName() << " & " << task.predicates[pIndex2].getName() << endl;
					if (task.predicates[pIndex].getArity() != 0) {
						if (maxStablePredicates.count(pIndex))
							maxStablePredicates[pIndex] = min(inInit, maxStablePredicates[pIndex]);
						else
							maxStablePredicates[pIndex] = inInit;
					}
					if (task.predicates[pIndex2].getArity() != 0) {
						if (maxStablePredicates.count(pIndex2))
							maxStablePredicates[pIndex2] = min(inInit, maxStablePredicates[pIndex2]);
						else
							maxStablePredicates[pIndex2] = inInit;
					}
				}
			}
		}



		// now try all subsets of the predicates 
		for (int s = 1; s < (1 << (allArityNonZeroPredicates.size())); s++){
			if (__builtin_popcount(s) <= 2) continue;
			if (__builtin_popcount(s) >= 4) continue;

			set<int> thisList;
			int initially = 0;
			for (unsigned int i = 0; i < allArityNonZeroPredicates.size(); i++)
				if (s & (1 << i)) {
					thisList.insert(allArityNonZeroPredicates[i]);
					initially += predicateInInit(task,allArityNonZeroPredicates[i]);
				}
			if (calculateOverallBalanceOfPredicateSet(task,thisList) == 0){
				cout << color(COLOR_GREEN, "Found stable predicate set ") << "of init size " << initially ;
				for (int p : thisList) cout << " " << task.predicates[p].getName();
				cout << endl;
				for (int pIndex : thisList)
					if (maxStablePredicates.count(pIndex))
						maxStablePredicates[pIndex] = min(initially, maxStablePredicates[pIndex]);
					else
						maxStablePredicates[pIndex] = initially;
			}
		}


		/////////////////////////////////////////////////
		// look for predicates that only occur in effects (and thus only in the goal)
		// also look for monotone predicates
		map<int, pair<int,int>> goalAchieverActionsWithoutSideEffects; // pair: action and effect index
		for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
			auto p = task.predicates[pIndex];
			if (p.isStaticPredicate()) continue; // static predicates get special treatment
			if (p.getArity() == 0) continue; // static predicates get special treatment

			bool occursInPre = false;
			bool isMonotonePos = true;
			vector<int> achievers;

			for (size_t action = 0; action < task.actions.size(); action++){
				const auto effs = task.actions[action].get_effects();
				const auto precs = task.actions[action].get_precondition();
		    
				for (size_t prec = 0; prec < precs.size(); prec++) {
					const auto & precObjec = precs[prec];
					int prePredicate = precObjec.predicate_symbol;
					if (prePredicate != pIndex) continue;
					occursInPre = true;
				}

    		    for (size_t eff = 0; eff < effs.size(); eff++) {
					const auto & effObjec = effs[eff];
					int predicate = effObjec.predicate_symbol;
					if (predicate != pIndex) continue;
					if (effObjec.negated)
						isMonotonePos = false;
					else{
						achievers.push_back(action); // if it makes multiple goals true -> can't handle that ...
					}
				}
			}

			// TODO technically the monotonicity is nice to have, but not really necessary as we can just track all facts that are true in the goal individually
			if (!occursInPre && isMonotonePos){
				// we need to track the tuples of this predicate that are in the goal
				for (size_t goal = 0; goal < task.goal.goal.size(); goal++) {
					const auto & goalObjec = task.goal.goal[goal];
					int predicate = goalObjec.predicate;
					if (predicate != pIndex) {
						continue;		
					}
					
					vector<int> tup;
					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < goalObjec.args.size(); iArg++){
						int preconditionVar = goalObjec.args[iArg];
						tup.push_back(preconditionVar);
					}
					predicateNoPreMonotone[pIndex].insert(tup);
				}


				// there might be just one achiever for such predicate	
				if (achievers.size() == 1){
					int action = achievers[0];
					DEBUG(cout << "Only one achiever action: " << task.actions[action].get_name() << endl);
					// check if this an "only achiever" action
					const auto effs = task.actions[action].get_effects();
					const auto precs = task.actions[action].get_precondition();
					bool hasSideEffect = false;
					int effectIndex = -1;
    	    		for (size_t eff = 0; eff < effs.size(); eff++) {
						const auto & effObjec = effs[eff];
						int predicate = effObjec.predicate_symbol;
						if (predicate == pIndex) { effectIndex = eff; continue;} // this one might increase

						int thisChange = calculateEffectBalance(task,task.actions[action],effObjec, true); // be conservative on effects

						if (thisChange != 0) hasSideEffect = true;
					}

					if (!hasSideEffect){
						DEBUG(cout << "Only achiever has no side effects. So its preconditions are only relevant if connected to the goal." << endl);
						goalAchieverActionsWithoutSideEffects[action] = {action, effectIndex};	
					}
				}
			}
		}

		for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
			auto p = task.predicates[pIndex];
			if (p.isStaticPredicate()) continue; // static predicates get special treatment
			if (p.getArity() == 0) continue; // static predicates get special treatment
			cout << "Predicate " << p.getName() << endl;

			bool occursInPre = false;
			bool isMonotonePos = true;
			bool isMonotoneNeg = true;
			vector<int> achievers;

			for (size_t action = 0; action < task.actions.size(); action++){
				const auto effs = task.actions[action].get_effects();
				const auto precs = task.actions[action].get_precondition();
		    
				for (size_t prec = 0; prec < precs.size(); prec++) {
					const auto & precObjec = precs[prec];
					int prePredicate = precObjec.predicate_symbol;
					if (prePredicate != pIndex) continue;
					if (goalAchieverActionsWithoutSideEffects.count(action)){
						DEBUG(cout << "Action " << task.actions[action].get_name() << " is goal achiever as has predicate " << p.getName() << " as a precondition." << endl);
						auto [achieverAction, achieverEffect] = goalAchieverActionsWithoutSideEffects[action];
						// so this is a precondition of an action whose sole effect is to make a goal true.
						set<int> effectVariables;
						map<int,vector<int>> effectVariablesOriginalPositions;
						const auto goalEffect = task.actions[achieverAction].get_effects()[achieverEffect];

						for (size_t i = 0; i < goalEffect.arguments.size(); i++){
							if (goalEffect.arguments[i].constant) continue; // don't care about this one
							effectVariables.insert(goalEffect.arguments[i].index);
							effectVariablesOriginalPositions[goalEffect.arguments[i].index].push_back(i);
						}
					
						vector<int> additionalAruguments;	
						for (size_t i = 0; i < precObjec.arguments.size(); i++){
							if (precObjec.arguments[i].constant) continue; // don't care about this one
							if (effectVariables.count(precObjec.arguments[i].index)) {
								continue;
							}
							additionalAruguments.push_back(precObjec.arguments[i].index);
						}

						map<int,int> argumentSingleValue;
						DEBUG(cout << "precondition has additional arguments:");
						for (int arg: additionalAruguments){
							int type = task.actions[action].get_parameters()[arg].type;
							vector<int> possibleValues;
						    for (tSize obj = 0; obj < task.objects.size(); obj++) {
						        auto oTypes = task.objects[obj].getTypes();
								for (int t : oTypes)
									if (t == type)
										possibleValues.push_back(obj);
							}

							DEBUG(cout << " No " << arg << " of type " << type << " " << task.type_names[type] << "  (domain: ";
						  	for (int obj : possibleValues) cout << " " << obj;
							cout << " )");
							
							if (possibleValues.size() != 1) occursInPre = true;
							else argumentSingleValue[arg] = possibleValues[0];
						}
						DEBUG(cout << endl);
						if (occursInPre) continue;

						DEBUG(cout << "Goal Effect Predicate " << goalEffect.predicate_symbol << " " << task.predicates[goalEffect.predicate_symbol].getName() << 
								" has " << predicateNoPreMonotone[goalEffect.predicate_symbol].size() << " instances."<< endl);
						// we need to generate the tuples that we will actually want to keep track
						for (vector<int> currentTuple : predicateNoPreMonotone[goalEffect.predicate_symbol]){
							vector<int> newTuple;
							bool reject = false;
							for (size_t i = 0; i < precObjec.arguments.size(); i++){
								if (precObjec.arguments[i].constant) {
									newTuple.push_back(precObjec.arguments[i].index);
								} else if (effectVariables.count(precObjec.arguments[i].index)) {
									// these are parameters that need to be copied	
									set<int> valuesFromPositions;
									for(int tuplePosition : effectVariablesOriginalPositions[precObjec.arguments[i].index])
										valuesFromPositions.insert(currentTuple[tuplePosition]);

									if (valuesFromPositions.size() > 1) reject = true;
									else newTuple.push_back(*valuesFromPositions.begin());
								} else {
									newTuple.push_back(argumentSingleValue[precObjec.arguments[i].index]);
								}
							}
							if (!reject){
								predicateNoPreMonotone[pIndex].insert(newTuple);
							}
						}
						DEBUG(cout << endl);
						continue;
					}
					occursInPre = true;
				}

    		    for (size_t eff = 0; eff < effs.size(); eff++) {
					const auto & effObjec = effs[eff];
					int predicate = effObjec.predicate_symbol;
					if (predicate != pIndex) continue;
					if (effObjec.negated)
						isMonotonePos = false;
					else{
						isMonotoneNeg = false;
						achievers.push_back(action); // if it makes multiple goals true -> can't handle that ...
					}
				}
			}



			if (stablePredicates.count(pIndex)) cout << "\t" << color(COLOR_GREEN,"Stable ") << stablePredicates[pIndex] << " are true" << endl;
			if (maxStablePredicates.count(pIndex)) cout << "\t" << color(COLOR_GREEN,"Limit Stable ") << maxStablePredicates[pIndex] << " are true" << endl;
			cout << "\tOnly in Effects " << boolalpha << !occursInPre << endl;
			cout << "\tMonotone rising " << boolalpha << isMonotonePos << endl;
			cout << "\tRising only eff " << ((!occursInPre && isMonotonePos)?color(COLOR_GREEN,"true"):"false") << endl;
			cout << "\tMonotone falling " << ((isMonotoneNeg)?color(COLOR_GREEN,"true"):"false") << endl;

			// we might need to take a judgement on how to handle this predicate
			if (isMonotoneNeg){
				// monotone neg takes precedence as this can be encoded easily
				predicatesMonotoneNegEncoding.insert(pIndex);
				predicateNoPreMonotone.erase(pIndex);
				cout << "\t" << color(COLOR_CYAN, "Decision: ") << "monotone neg" << endl;
			} else if (!occursInPre && isMonotonePos) {
				// Attention: this output is needed! We need to force that even if predicateNoPreMonotone[pIndex] is empty, it is contained
				cout << "\t" << color(COLOR_CYAN, "Decision: ") << "no precondition monotone (size " << predicateNoPreMonotone[pIndex].size() << ")" << endl;
				DEBUG(cout << "insert " << pIndex << " amount: " << predicateNoPreMonotone[pIndex].size() << endl;
				for (vector<int> tuple : predicateNoPreMonotone[pIndex]){
					cout << "\t\t" << task.predicates[pIndex].getName();
					for (int i : tuple) cout << " " << i << " " << task.objects[i].getName();
					cout << endl;
				});
			} else if (stablePredicates.count(pIndex)){
				if (stablePredicates[pIndex] >= 30){
					cout << "\t" << color(COLOR_RED, "Decision: ") << "normal (but known to be stable at " << predicateStable[pIndex] << ")" << endl;
					predicateStable.erase(pIndex);
					predicateNoPreMonotone.erase(pIndex);
					foundOrdinaryPredicate = true;
					ordinaryPredicates.insert(pIndex);
				} else {
					predicateStable[pIndex] = stablePredicates[pIndex];
					predicateNoPreMonotone.erase(pIndex);
					cout << "\t" << color(COLOR_CYAN, "Decision: ") << "stable " << predicateStable[pIndex] << endl;
				}
			} else if (maxStablePredicates.count(pIndex)){
				if (maxStablePredicates[pIndex] >= 30){
					cout << "\t" << color(COLOR_RED, "Decision: ") << "normal (but known to be max stable at " << predicateStable[pIndex] << ")" << endl;
					predicateStable.erase(pIndex);
					predicateNoPreMonotone.erase(pIndex);
					foundOrdinaryPredicate = true;
					ordinaryPredicates.insert(pIndex);
				} else {
					predicateStable[pIndex] = maxStablePredicates[pIndex]; // this causes *most* of the code related to stable stuff
					predicateMaxStable[pIndex] = maxStablePredicates[pIndex];
					predicateNoPreMonotone.erase(pIndex);
					cout << "\t" << color(COLOR_CYAN, "Decision: ") << "max stable " << predicateMaxStable[pIndex] << endl;
				}
			} else {
				cout << "\t" << color(COLOR_RED, "Decision: ") << "normal" << endl;
				foundOrdinaryPredicate = true;
				ordinaryPredicates.insert(pIndex);
			}
			cout << endl << endl;
		}
	} else {
		foundOrdinaryPredicate = true;
		for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
			auto p = task.predicates[pIndex];
			if (p.isStaticPredicate()) continue; // static predicates get special treatment
			if (p.getArity() == 0) continue; // static predicates get special treatment
			ordinaryPredicates.insert(pIndex);
		}	
	}

	if (!foundOrdinaryPredicate){
		cout << "Found no ordinary predicate. Accepting the run only if W=0." << endl;
	} else {
		cout << "Found " << ordinaryPredicates.size() << " ordinary predicate." << endl;
		int maxNetNecessary = 0;
		for (size_t action = 0; action < task.actions.size(); action++){
			int preSize = 0;
			const auto precs = task.actions[action].get_precondition();
			for (size_t prec = 0; prec < precs.size(); prec++) {
				const auto & precObjec = precs[prec];
				int prePredicate = precObjec.predicate_symbol;
				if (ordinaryPredicates.count(prePredicate) == 0) continue;
				preSize ++;
			}
			int change = calculateOverallBalanceOfAction(task,action,ordinaryPredicates);
			if (change < 0) change = 0;
			change += preSize;	
			cout << "Action " << task.actions[action].get_name() << " net change: " << change << endl; 
			if (change > maxNetNecessary) maxNetNecessary = change;
		}

		int goalSize = 0;
		const auto goals = task.goal.goal;
		for (size_t goal = 0; goal < goals.size(); goal++) {
			const auto & goalObjec = goals[goal];
			int predicate = goalObjec.predicate;
			if (ordinaryPredicates.count(predicate) == 0) continue;
			// only count those goals that are already true in init - all others have to be established by effects anyhow
	
			for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
				vector<int> tuple = supportingPredicateTuples[predicate][i].first;
				if (tuple == goalObjec.args)
					goalSize++;
			}
		}

		cout << "Maximum net change: " << maxNetNecessary << " goal size: " << goalSize << endl;
		goalNeededWidth = goalSize;
		maximumTimeStepNetChange = maxNetNecessary;
	}

	//exit(0);


	/////////////////////////////////////////////////////////////////////////////////////////////////////////
	numActions = task.actions.size();
    numObjs = task.objects.size();

	map<int,int> objCount;
    for (size_t obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (size_t i = 0; i < oTypes.size(); i++)
			objCount[oTypes[i]] += 1;
	}

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
		for (int i = numberOfArgumentPositions; i < numberOfArgumentPositions + p.second; i++){
			cout << "Action Argument #" << setw(2) << i << " T " << setw(2) << " size " << setw(5) << objCount[p.first] << " " << task.type_names[p.first] << endl;
			typeOfArgument[i] = p.first;
		}
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

	for (size_t pIndex = 0; pIndex < task.predicates.size(); pIndex++){
    	const auto & p = task.predicates[pIndex];
		if (p.isStaticPredicate()) continue; // static predicates get special treatment
		if (predicateStable.count(pIndex)) continue;
		if (predicateNoPreMonotone.count(pIndex)) continue;
		if (predicatesMonotoneNegEncoding.count(pIndex)) continue;
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
		for (int i = numberOfPredicateArgumentPositions; i < numberOfPredicateArgumentPositions + p.second; i++){
			typeOfPredicateArgument[i] = p.first;
			cout << "Predicate Argument #" << setw(2) << i << " T " << setw(2) << " size " << setw(5) << objCount[p.first] << " " << task.type_names[p.first] << endl;
		}
		numberOfPredicateArgumentPositions += p.second;
	}


	for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
		auto p = task.predicates[pIndex];
		if (p.isStaticPredicate()) continue; // static predicates get special treatment
		if (predicateStable.count(pIndex)) continue;
		if (predicateNoPreMonotone.count(pIndex)) continue;
		if (predicatesMonotoneNegEncoding.count(pIndex)) continue;
		
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
	//exit(0);
    cout << "- num actions " << numActions << endl;
    cout << "- num objects " << numObjs << endl;
    cout << "- max arity " << maxActionArity << endl;

    for (tSize i = 0; i < task.predicates.size(); i++) {
        cout << i << " " << task.predicates[i].getName() << " isStatic " << task.predicates[i].isStaticPredicate() << endl;
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


	// preconditions are actually met
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto precs = task.actions[action].get_precondition();
        for (size_t prec = 0; prec < precs.size(); prec++) {
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getArity() == 0) continue; 
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue;
			if (task.predicates[predicate].isStaticPredicate()) continue;


			// iterate over the arguments of the precondition
			for (size_t iArg = 0; iArg < precObjec.arguments.size(); iArg++){
				int preconditionVar = precObjec.arguments[iArg].index;
				const bool pIsConst = precObjec.arguments[iArg].constant;
				int predSlot = actionArgumentPositions[action][preconditionVar];
				
				// argument in the precondition might be a constant 
				if (pIsConst) continue;
				if (predicateNoPreMonotone.count(predicate)) continue;
				if (predicatesMonotoneNegEncoding.count(predicate)) continue;

				if (predicateStable.count(predicate)) {
					perPredicatePossibleBeforeEquals[predicate].insert({predSlot,iArg});
				} else {
					// variable equality
					int myParam = predicateArgumentPositions[predicate][iArg];
					possibleBeforeEquals.insert({predSlot, myParam});
				}
			}
		}
	}

	// adding and deleting effects
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
        for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 
			if (task.predicates[predicate].getArity() == 0) continue; 
			
			// iterate over the arguments of the precondition
			for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
				int preconditionVar = effObjec.arguments[iArg].index;
				const bool pIsConst = effObjec.arguments[iArg].constant;
				int afterSlot = actionArgumentPositions[action][preconditionVar];

				// argument in the precondition might be a constant 
				if (pIsConst) continue;
				if (predicateNoPreMonotone.count(predicate)) continue;
				if (predicatesMonotoneNegEncoding.count(predicate)) continue;

				if (predicateStable.count(predicate)) {
					perPredicatePossibleAfterEquals[predicate].insert({afterSlot,iArg});
				} else {
					int myParam = predicateArgumentPositions[predicate][iArg];
					possibleAfterEquals.insert({afterSlot,myParam}); 
				}
			}
		}
	}

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
int atMostOnePredicateValueArgument = 0;
int addEffects = 0;
int delEffects = 0;
int delEffectsStable = 0;
int frameEqual = 0;
int frameImplies = 0;
int frameFacts = 0;
int parameterEqualsConstraints = 0;
int precSupportStable = 0;
int precSupportMonotone = 0;
int staticPrecondition = 0;

int addEffectsStable = 0;
int delEffectsMonotone = 0;
int frameMonotoneRising = 0;
int frameEqualStable = 0;
int frameImpliesStable = 0;
int equalsStable = 0;
int initSuppStable = 0;
int initSuppGrounded = 0;

extern int actionTyping;
extern int atMostOneParamterValue;
extern int precSupport;
extern int equals;
extern int initSupp;
extern int nullary;
extern int oneAction; 
extern int goalAchiever; 


vector<vector<vector<int>>> predicateSlotVariables; // time -> slot -> predicate (contains -1 for static one)
vector<vector<vector<vector<int>>>> argumentSlotVariables; // time -> slot -> position -> constant (0 is the first possible one)

// time -> predicate -> slot -> position -> constant (0 is the first possible one)
vector<vector<vector<vector<vector<int>>>>> stablePredicateArgumentSlotVariables; 
// time -> predicate -> tuple -> variable
vector<map<int,map<vector<int>,int>>> monotoneIncreasingPredicates;
vector<map<int,map<vector<int>,int>>> monotoneDecreasingPredicates;

vector<vector<vector<vector<int>>>> LiftedLinearSAT::generate_action_state_equality(const Task &task, void* solver, sat_capsule & capsule, int width, int actionTime, int stateTime){
	DEBUG(cout << "Starting to generate equality between actions@" << actionTime << " and state@" << stateTime << endl);
	// variables for argument pos X = slot Y parameter pos Z
	vector<vector<vector<int>>> planeEqualsVars;
	bool generatedPlaneVars = false;
	
	vector<vector<vector<vector<int>>>> equalsVars;
	
	for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
		DEBUG(cout << "Starting to generate equality for predicate " << task.predicates[predicate].getName() <<  endl);
		vector<vector<vector<int>>> thisPredicateEq;
		if (task.predicates[predicate].getName().rfind("type@", 0) == 0 || 
			task.predicates[predicate].getName().rfind("=", 0) == 0||
			task.predicates[predicate].isStaticPredicate() || 
			task.predicates[predicate].getArity() == 0 ||
			predicateNoPreMonotone.count(predicate) || 
			predicatesMonotoneNegEncoding.count(predicate)
			) {
			equalsVars.push_back(thisPredicateEq);
			DEBUG(cout << " ... is actually not necessary" <<  endl);
			continue; 
		}
	
		bool isStable = predicateStable.count(predicate);
		
		// if this is not a stable one and we have already generated the variables -- just copy them. (this is cheap as there are only few predicates)
		if (!isStable && generatedPlaneVars){
			equalsVars.push_back(planeEqualsVars);
			continue;
		}

		int bef = get_number_of_clauses();
    	for (int actionParamter = 0; actionParamter < numberOfArgumentPositions; actionParamter++){
			DEBUG(cout << "\t Action Parameter " << actionParamter <<  endl);
			vector<vector<int>> eqVars;
		
			// how many slots are there depends on what type of predicate this is	
			int thisWidth = width;
			if (isStable) thisWidth = predicateStable[predicate];

			for (int slot = 0; slot < thisWidth; slot++){
				DEBUG(cout << "\t Slot " << slot <<  endl);
				vector<int> eqVarsSlot;
				
				int numberOfFactParameters = numberOfPredicateArgumentPositions;
				if (isStable){
					numberOfFactParameters = task.predicates[predicate].getArity();
				}

		   		for (int factParameter = 0; factParameter < numberOfFactParameters; factParameter++){
					DEBUG(cout << "\t Fact Parameter " << factParameter << endl);
					// only generate for non-stable equals that will actually be used
					if ( !isStable && (
						(actionTime == stateTime && possibleBeforeEquals.count({actionParamter,factParameter}) == 0) ||
						(actionTime + 1 == stateTime && possibleAfterEquals.count({actionParamter,factParameter}) == 0))){
						eqVarsSlot.push_back(-1);
						continue;
					}

					if ( isStable && (
						(actionTime == stateTime && perPredicatePossibleBeforeEquals[predicate].count({actionParamter,factParameter}) == 0) ||
						(actionTime + 1 == stateTime && perPredicatePossibleAfterEquals[predicate].count({actionParamter,factParameter}) == 0))){
						eqVarsSlot.push_back(-1);
						continue;
					}



					// generate controlling variable
					int equalsVar = capsule.new_variable();
					eqVarsSlot.push_back(equalsVar);
					DEBUG(
					if (isStable)
						capsule.registerVariable(equalsVar, to_string(actionTime) + " @ # " +to_string(actionParamter)+" = "	+ to_string(stateTime) + " @ " + task.predicates[predicate].getName() + " # " + to_string(factParameter));
					else
						capsule.registerVariable(equalsVar, to_string(actionTime) + " @ # " +to_string(actionParamter)+" = "	+ to_string(stateTime) + " @ # " + to_string(factParameter));
						);

					int thisLower = lowerTindex[typeOfArgument[actionParamter]];
					int thisUpper = upperTindex[typeOfArgument[actionParamter]];
					
					int beforeLower;
					int beforeUpper;
				
					if (isStable){	
						beforeLower = lowerTindex[task.predicates[predicate].getTypes()[factParameter]];
						beforeUpper = upperTindex[task.predicates[predicate].getTypes()[factParameter]];
					} else {
						beforeLower = lowerTindex[typeOfPredicateArgument[factParameter]];
						beforeUpper = upperTindex[typeOfPredicateArgument[factParameter]];
					}
		
		
					for(int o = 0; o < numObjs; o++){
						if (o < thisLower || o > thisUpper){
							if (o >= beforeLower && o <= beforeUpper){
								if (isStable)
									impliesNot(solver,equalsVar, stablePredicateArgumentSlotVariables[stateTime][predicate][slot][factParameter][o]); // different indexing ...
								else
									impliesNot(solver,equalsVar, argumentSlotVariables[stateTime][slot][factParameter][o-beforeLower]);
							}
						}
						if (o < beforeLower || o > beforeUpper){
							if (o >= thisLower && o <= thisUpper)
								impliesNot(solver,equalsVar, parameterVars[actionTime][actionParamter][o-thisLower]);
						}
					
						// this could actually be the constant that makes them equal	
						if (o >= thisLower && o <= thisUpper && o >= beforeLower && o <= beforeUpper){
							int a = parameterVars[actionTime][actionParamter][o-thisLower];
							int b;
						   	if (isStable)
								b = stablePredicateArgumentSlotVariables[stateTime][predicate][slot][factParameter][o];
							else
								b = argumentSlotVariables[stateTime][slot][factParameter][o-beforeLower];
							// need to subtract the starting values of the types
							andImplies(solver,equalsVar, a , b);
							if (true || actionTime != stateTime){
								andImplies(solver,equalsVar, b, a);
								andImplies(solver,b, a, equalsVar); // this one is needed for correctness of deleting effects (i.e. it forces that)
							}
						}
					}
				}
				eqVars.push_back(eqVarsSlot);
			}
			thisPredicateEq.push_back(eqVars);
		}
		if (isStable)
			equalsStable += get_number_of_clauses() - bef;
		else
			equals += get_number_of_clauses() - bef;

		equalsVars.push_back(thisPredicateEq);
		if (isStable) continue;

		planeEqualsVars = thisPredicateEq;
		generatedPlaneVars = true;
	}

	DEBUG(cout << "DONE generating equality between actions@" << actionTime << " and state@" << stateTime << endl);
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
				task.predicates[predicate].isStaticPredicate() || 
				task.predicates[predicate].getArity() == 0 || 
				predicateStable.count(predicate) ||
				predicateNoPreMonotone.count(predicate) || 
				predicatesMonotoneNegEncoding.count(predicate)
				) {
				thisSlotPredicates.push_back(-1);
				continue; 
			}
			int predicateVar = capsule.new_variable();
			thisSlotPredicates.push_back(predicateVar);
			thisSlotPredicatesAMO.push_back(predicateVar);
			DEBUG(capsule.registerVariable(predicateVar, to_string(time) + " @ slot " + to_string(slot) + " predicate " + task.predicates[predicate].getName()));
		}
		thisTimePredicateSlotVariables.push_back(thisSlotPredicates);
		
		// at most one predicate per slot
		int bef = get_number_of_clauses();
		if (time == 0 && thisSlotPredicatesAMO.size() > 0){ // this should only be really necessary at time 0 as this property gets inherited to all other time steps
			atMostOne(solver,capsule,thisSlotPredicatesAMO);
			//atLeastOne(solver,capsule,thisSlotPredicatesAMO);
		}
		atMostOnePredicate += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();
		

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

			if (time == 0){ // this should only be really necessary at time 0 as this property gets inherited to all other time steps
				// each parameter can have at most one value
				atMostOne(solver,capsule,thisSlotParameterVars[paramter]);
			}
		}
		thisTimeArgumentSlotVariables.push_back(thisSlotParameterVars);

		atMostOnePredicateValueArgument += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();

		// predicate types must be correct
		for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
			if (task.predicates[predicate].getArity() == 0) continue;
			if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do
			if (predicateStable.count(predicate)) continue;
			if (predicateNoPreMonotone.count(predicate)) continue;
			if (predicatesMonotoneNegEncoding.count(predicate)) continue;
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
		bef = get_number_of_clauses();


		// maybe select from init
		if (time == 0){

			int relevantInitSize = 0;
			vector<pair<int, vector<int> >> initList;
			for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
				if (task.predicates[predicate].getArity() == 0) continue;
				if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do
				if (predicateStable.count(predicate)) continue;
				if (predicateNoPreMonotone.count(predicate)) continue;
				if (predicatesMonotoneNegEncoding.count(predicate)) continue;
				relevantInitSize += supportingPredicateTuples[predicate].size();
				for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
					vector<int> tuple = supportingPredicateTuples[predicate][i].first;
					initList.push_back({predicate, tuple});
				}
			}

			if (width >= relevantInitSize){
				if (slot >= relevantInitSize){
					// there is no predicate at such slots
					for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
						if (task.predicates[predicate].getArity() == 0) continue;
						if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do
						if (predicateStable.count(predicate)) continue;
						if (predicateNoPreMonotone.count(predicate)) continue;
						if (predicatesMonotoneNegEncoding.count(predicate)) continue;

						assertNot(solver,thisSlotPredicates[predicate]);
					}
				} else {
					auto [predicate, tuple] = initList[slot];
					assertYes(solver,thisSlotPredicates[predicate]);

					for (size_t index = 0; index < tuple.size(); index++){
						int myObjIndex = objToIndex[tuple[index]];
						int myParam = predicateArgumentPositions[predicate][index];
						int constantVar = thisSlotParameterVars[myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
						assertYes(solver,constantVar);
					}
				}
			} else {
				for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
					if (task.predicates[predicate].getArity() == 0) continue;
					if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do
					if (predicateStable.count(predicate)) continue;
					if (predicateNoPreMonotone.count(predicate)) continue;
					if (predicatesMonotoneNegEncoding.count(predicate)) continue;

					// consider how many arguments are there
					int predicateVar = thisSlotPredicates[predicate];

					for (int befSlot = 0; befSlot < slot; befSlot++){
						// if we select the predicate here, we cannot use use *later* predicates earlier on in the slots
						for (size_t laterPredicate = predicate + 1; laterPredicate < task.predicates.size(); laterPredicate++){
							if (task.predicates[laterPredicate].getArity() == 0) continue;
							if (task.predicates[laterPredicate].isStaticPredicate()) continue; // nothing to do
							if (predicateStable.count(laterPredicate)) continue;
							if (predicateNoPreMonotone.count(laterPredicate)) continue;
							if (predicatesMonotoneNegEncoding.count(laterPredicate)) continue;
							
							int befSlotLaterPredicateVar = thisTimePredicateSlotVariables[befSlot][laterPredicate];

							impliesNot(solver,predicateVar, befSlotLaterPredicateVar);
						}
						// if before is the same predicate, it must be a lexicographically smaller tuple
						for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
							for (size_t j = i+1; j < supportingPredicateTuples[predicate].size(); j++){
								vector<int> firstTuple = supportingPredicateTuples[predicate][i].first;
								vector<int> secondTuple = supportingPredicateTuples[predicate][i].first;
								set<int> identical;
								identical.insert(predicateVar);
								identical.insert(thisTimePredicateSlotVariables[befSlot][predicate]);
								
								for (size_t pos = 0; pos < size_t(task.predicates[predicate].getArity()) ; pos++){
									int myObjIndexFirst = objToIndex[firstTuple[pos]];
									int myObjIndexSecond = objToIndex[secondTuple[pos]];
									int myParam = predicateArgumentPositions[predicate][pos];
									if (myObjIndexFirst == myObjIndexSecond){ // still same up to here
										identical.insert(thisSlotParameterVars[myParam][myObjIndexFirst - lowerTindex[typeOfPredicateArgument[myParam]]]);
										identical.insert(thisTimeArgumentSlotVariables[befSlot][myParam][myObjIndexFirst - lowerTindex[typeOfPredicateArgument[myParam]]]);
									} else {
										identical.insert(thisSlotParameterVars[myParam][myObjIndexFirst - lowerTindex[typeOfPredicateArgument[myParam]]]);
										int forbiddenVar = thisTimeArgumentSlotVariables[befSlot][myParam][myObjIndexSecond - lowerTindex[typeOfPredicateArgument[myParam]]];

										andImpliesNot(solver,identical,forbiddenVar);
										break; // we have done our job!
									}
								}
							}
						}
					}


					DEBUG(cout << "PREDICATE VAR " << predicateVar << endl);
					if (task.predicates[predicate].getArity() == 1){
						vector<int> possibleValues;
						
						for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
							vector<int> tuple = supportingPredicateTuples[predicate][i].first;
						
							int myObjIndex = objToIndex[tuple[0]];
							int myParam = predicateArgumentPositions[predicate][0];
							int constantVar = thisSlotParameterVars[myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							
							possibleValues.push_back(constantVar);
							//cout << "QQ " << constantVar << " " << myParam << " " << myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]] << " " << myObjIndex << " " << typeOfPredicateArgument[myParam]  << " " << lowerTindex[typeOfPredicateArgument[myParam]] << endl;
						}
						//cout << "A " << predicateVar << endl;
						impliesOr(solver,predicateVar,possibleValues);
					} else {
						//cout << "Predicate supporting tuples " << supportingPredicateTuples[predicate].size() << endl;
						for (size_t lastPos = 0; lastPos < size_t(task.predicates[predicate].getArity() - 1) ; lastPos++){
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
					
							//cout << "B" << endl;
					
							for (auto & x : possibleUpto){
								andImpliesOr(solver,x.first,x.second);
								DEBUG(for (int i : x.first) cout << " - [" << i << " " << capsule.variableNames[i] << "]";
								for (int i : x.second) cout << " [" << capsule.variableNames[i] << "]";
								cout << endl);
							}

							//cout << "C" << endl;
					
							if (lastPos == 0){
								int posOfValue = 1;
								vector<int> initial;
								for (auto & x : possibleUpto)
									initial.push_back(x.first[posOfValue]);
								
								//cout << "C" << endl;
								impliesOr(solver,predicateVar,initial);
								DEBUG(		
								cout << "- [" << predicateVar << " " << capsule.variableNames[predicateVar] << "]";
								for (int i : initial) cout << " [" << capsule.variableNames[i] << "]";
								cout << endl);
							}
							
							//cout << "D " << task.predicates[predicate].getArity() << endl;
						}
					}
				}
			}
		}
		//exit(0);
		initSupp += get_number_of_clauses() - bef;
	}
	
	DEBUG(cout << "DONE generating normal slots." << endl);
	
	vector<vector<vector<vector<int>>>> thisTimeStablePredicateArgumentSlotVariables;
	
	
	int bef = get_number_of_clauses();
	// generate argument variables for stable predicates
	for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
		vector<vector<vector<int>>> thisPredicateAgumentVariables;
		if (!predicateStable.count(predicate)) {
			thisTimeStablePredicateArgumentSlotVariables.push_back(thisPredicateAgumentVariables);
			continue;
		}
		
		DEBUG(cout << "Special slots for " << task.predicates[predicate].getName() << endl);
		
		// we need to do all this generation for each slot
		for (int slot = 0; slot < predicateStable[predicate]; slot++){
			vector<vector<int>> thisSlotAgumentVariables;
			for (int arg = 0; arg < task.predicates[predicate].getArity(); arg++){
				vector<int> thisParameterVariables;
				int thisType = task.predicates[predicate].getTypes()[arg];

				for (int obj = 0; obj < numObjs; obj++){
					if (obj < lowerTindex[thisType]) {thisParameterVariables.push_back(-1); continue;}
					if (obj > upperTindex[thisType]) {thisParameterVariables.push_back(-1); continue;}

					int objectVar = capsule.new_variable();
					thisParameterVariables.push_back(objectVar);
					DEBUG(capsule.registerVariable(objectVar, to_string(time) + " @ predicate " + task.predicates[predicate].getName() + " slot " + to_string(slot) + " argument#" + to_string(arg) + " = const " + task.objects[indexToObj[obj]].getName()));

					if (time == 0){
						if (int(supportingPredicateTuples[predicate].size()) <= slot) // this takes care of the maxStable predicates
							assertNot(solver,objectVar);
						else if (obj == objToIndex[supportingPredicateTuples[predicate][slot].first[arg]])
							assertYes(solver,objectVar);
						else
							assertNot(solver,objectVar);
					}

				}
				// here no other constraints are necessary 
				thisSlotAgumentVariables.push_back(thisParameterVariables);
			}
			thisPredicateAgumentVariables.push_back(thisSlotAgumentVariables);		
		}
		thisTimeStablePredicateArgumentSlotVariables.push_back(thisPredicateAgumentVariables);
	}
	initSuppStable += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();

	DEBUG(cout << "DONE generating limited slots." << endl);
	DEBUG(cout << "Generating grounded slots" << endl);

	map<int,map<vector<int>,int>> thisTimeNoPreMonotone;
	for (auto [predicate, tuples] : predicateNoPreMonotone){
		for (auto tuple : tuples){
			int factVar = capsule.new_variable();
			thisTimeNoPreMonotone[predicate][tuple] = factVar;
			DEBUG(
				string name = task.predicates[predicate].getName(); 
				for (int i : tuple) name += " " + task.objects[i].getName();
				cout << "Generate tuple instance for (" << name + ")" << endl;
				capsule.registerVariable(factVar, to_string(time) + " @ " + name)
				);
			if (time == 0){
				// these are initially false otherwise we would have removed them from the problem already
				// But: Rover ... Fuck!
				bool isTrue = false;
				for (auto trueInInit : supportingPredicateTuples[predicate])
					if (trueInInit.first == tuple){
						assertYes(solver,factVar);
						isTrue = true;
					}
				if (!isTrue)
					assertNot(solver,factVar); 
			}
		}
	}

	map<int,map<vector<int>,int>> thisTimeNegMonotone;
	for (int predicate : predicatesMonotoneNegEncoding){
		for (auto trueInInit : supportingPredicateTuples[predicate]){
			vector<int> tuple = trueInInit.first;
			int factVar = capsule.new_variable();
			thisTimeNegMonotone[predicate][tuple] = factVar;
			DEBUG(
				string name = task.predicates[predicate].getName(); 
				for (int i : tuple) name += " " + task.objects[i].getName();
				cout << "Generate tuple instance for (" << name + ")" << endl;
				capsule.registerVariable(factVar, to_string(time) + " @ " + name)
				);
			if (time == 0) // these are always true at the beginning
				assertYes(solver,factVar);
		}
	}
	initSuppGrounded += get_number_of_clauses() - bef;

	predicateSlotVariables.push_back(thisTimePredicateSlotVariables);
	argumentSlotVariables.push_back(thisTimeArgumentSlotVariables);
	stablePredicateArgumentSlotVariables.push_back(thisTimeStablePredicateArgumentSlotVariables);
	monotoneIncreasingPredicates.push_back(thisTimeNoPreMonotone);
	monotoneDecreasingPredicates.push_back(thisTimeNegMonotone);
	DEBUG(cout << "DONE generating all slots." << endl);
}


void LiftedLinearSAT::generate_goal_assertion(const Task &task, void* solver, sat_capsule & capsule, int width, int time){
	int bef = get_number_of_clauses();
	for (int g : task.goal.positive_nullary_goals)
		assertYes(solver,lastNullary[g]);	
	for (int g : task.goal.negative_nullary_goals)
		assertNot(solver,lastNullary[g]);	

	nullary += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();


	const auto goals = task.goal.goal;
	for (size_t goal = 0; goal < goals.size(); goal++) {
		const auto & goalObjec = goals[goal];
		int predicate = goalObjec.predicate;
	
		if (task.predicates[predicate].isStaticPredicate()){
			// static preconditions must be handled more efficiently
			// i.e. directly via support from init
			// TODO
		} else if (predicateNoPreMonotone.count(predicate)) {
			// this is a predicate where we track individual facts
			assertYes(solver,monotoneIncreasingPredicates[time][predicate][goalObjec.args]);
		} else if (predicatesMonotoneNegEncoding.count(predicate)) {
			// this is a predicate where we track individual facts
			assertYes(solver,monotoneDecreasingPredicates[time][predicate][goalObjec.args]);
		} else {
			vector<int> goalSlotVars;

			int thisWidth = width;
			bool stableMode = false;
			// precondition on a stable predicate. Must be one of the slots we have.
			if (predicateStable.count(predicate)){
				thisWidth = predicateStable[predicate];
				stableMode = true;
			}

			for (int slot = 0; slot < thisWidth; slot++){
				int goalSlotVar = capsule.new_variable();
				goalSlotVars.push_back(goalSlotVar);
				DEBUG(capsule.registerVariable(goalSlotVar,to_string(time) + " @ goal " + to_string(goal) + " slot " + to_string(slot) + " pred " + task.predicates[predicate].getName()));
	
				// if we select this slot, we actually have to have the correct fact there
				if (!stableMode)
					implies(solver, goalSlotVar, predicateSlotVariables[time][slot][predicate]);
	
				// iterate over the arguments of the precondition
				for (size_t iArg = 0; iArg < goalObjec.args.size(); iArg++){
					int preconditionVar = goalObjec.args[iArg];
	
					int myObjIndex = objToIndex[preconditionVar]; 
					
					int constantVar;
					if (stableMode){
						constantVar = stablePredicateArgumentSlotVariables[time][predicate][slot][iArg][myObjIndex];
					} else {
						int myParam = predicateArgumentPositions[predicate][iArg];
						constantVar = argumentSlotVariables[time][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
					}
					implies(solver, goalSlotVar, constantVar); 
				}
			}
			atLeastOne(solver,capsule,goalSlotVars);
		}
	}
	goalAchiever += get_number_of_clauses() - bef;
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

void LiftedLinearSAT::generate_formula(const Task &task, void* solver, sat_capsule & capsule, int width, bool optimal) {
	bool generateBaseFormula = true; // this is for later. Set to false for incremental?

	int bef = get_number_of_clauses();
	// indices: timestep -> parameter -> object
	int time = planLength-1;
	int curPhase = phaseloop.size() ? (time % phaseloop.size()) : 0;
	
	cout << "Generating time = " << setw(3) << time;
	if (phaseloop.size())
		cout << " phase = " << curPhase;
	cout << endl;
	

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
		if (phaseloop.size() && leavingActions[phaseloop[curPhase]].count(action) == 0){
			assertNot(solver,actionVar);
		}
	}
	// add variables to overall list (needed for later retrieval)
	actionVars.push_back(actionVarsTime);
	atMostOne(solver,capsule,actionVarsTime);
	if (optimal) atLeastOne(solver,capsule,actionVarsTime);  // only correct for optimal planning
	oneAction += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();

	// generate nullary variables
	std::unordered_map<int,int> currentNullary;

	// generate	variables for the action parameters
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

    	for (int parameter = 0; parameter < numberOfArgumentPositions; parameter++){
			int type = typeOfArgument[parameter];
			int lower = lowerTindex[type];
			int upper = upperTindex[type];
			
			parameterVarsTime[parameter].resize(upper - lower + 1);

			for (int o = 0; o < upper - lower + 1; o++){
				int objectVar = capsule.new_variable();
				parameterVarsTime[parameter][o] = objectVar;
				DEBUG(capsule.registerVariable(objectVar, to_string(time) + " @ param#" + to_string(parameter) + " = const " + task.objects[indexToObj[o + lower]].getName()));
			}
			// each parameter can have at most one value
			//int x = get_number_of_clauses();
			atMostOne(solver,capsule,parameterVarsTime[parameter]);
			//DEBUG(cout << "Generated for parameter " << parameter << " objects " << upper - lower + 1 << " clauses " << get_number_of_clauses() - x << endl); 
		}
		parameterVars.push_back(parameterVarsTime);

		atMostOneParamterValue += get_number_of_clauses() - bef;
	}

	/// action variables
	bef = get_number_of_clauses();
	for (size_t action = 0; action < task.actions.size(); action++){
		if (phaseloop.size() && leavingActions[phaseloop[curPhase]].count(action) == 0) continue;

		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);
		

		// typing implications!
		auto params = task.actions[action].get_parameters();
		if (generateBaseFormula){
          	for (size_t l = 0; l < params.size(); l++) {
				int thisParameterIndex = actionArgumentPositions[action][l];
          	    //if (!needToType[{action,l}]){
          	    //	DEBUG(cout << "no need to type " << endl);
				//	continue;
				//}
				
				int lower = lowerTindex[params[l].type];
          	    int upper = upperTindex[params[l].type];
          	    DEBUG(cout << "\t\t" << task.type_names[params[l].type] << "(" << lower << "-" << upper << "): ");
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
				//DEBUG(cout << "Typing " << actionVar << ":"; for(auto x : allowed) cout << " " << x; cout << endl;);
				impliesOr(solver,actionVar,allowed);
          	}
		}
	}
	actionTyping += get_number_of_clauses() - bef;

	// that is to generate the variables for the *next* state, i.e., the effect state
	generate_predicate_slot_layer(task, solver, capsule, width, time+1); // generate effect slots
	// create equality from these actions to the previous state
	vector<vector<vector<vector<int>>>> equalBefore = generate_action_state_equality(task, solver, capsule, width, time, time);
	// create equality from these actions to the next state
	vector<vector<vector<vector<int>>>> equalAfter = generate_action_state_equality(task, solver, capsule, width, time, time+1);


	// preconditions are actually met
	for (size_t action = 0; action < task.actions.size(); action++){
		if (phaseloop.size() && leavingActions[phaseloop[curPhase]].count(action) == 0) continue;
		
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);

		const auto precs = task.actions[action].get_precondition();
        for (size_t prec = 0; prec < precs.size(); prec++) {
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getArity() == 0) continue; 

			if (predicateNoPreMonotone.count(predicate) || predicatesMonotoneNegEncoding.count(predicate)){
				//if (predicatesMonotoneNegEncoding.count(predicate)) continue; // for debugging
				// special case: this is a monotone predicate that is only relevant w.r.t. to the goal and this one achiever actions that only makes the goal true ...
				
				bef = get_number_of_clauses();
			
				vector<int> achiever;	
				// we have to select one of the possible tuples and have that one true
				map<vector<int>,int> & tupleSource =
					(predicateNoPreMonotone.count(predicate))?monotoneIncreasingPredicates[time][predicate]:monotoneDecreasingPredicates[time][predicate];
				for (auto [tuple, factVar] : tupleSource){
					bool badAchiever = false;
					set<int> impliedVars;
					impliedVars.insert(actionVar);
					for (size_t iArg = 0; iArg < precObjec.arguments.size(); iArg++){
						int preconditionVar = precObjec.arguments[iArg].index;
						const bool pIsConst = precObjec.arguments[iArg].constant;

						// argument in the precondition might be a constant 
						if (pIsConst){
							if (preconditionVar != tuple[iArg]) badAchiever = true;
						} else {
							int parameter = actionArgumentPositions[action][preconditionVar];
							int lower = lowerTindex[typeOfArgument[parameter]];
							int upper = upperTindex[typeOfArgument[parameter]];
							int objIndex = objToIndex[tuple[iArg]];

							if (objIndex < lower || objIndex > upper)
								badAchiever = true;
							else
								impliedVars.insert(parameterVarsTime[parameter][objIndex - lower]);
						}
					}

					if (badAchiever) {
						//notAll(solver,impliedVars);
						continue;
					} 
				
					andImplies(solver,impliedVars, factVar);

					int chooseThis = capsule.new_variable();
					achiever.push_back(chooseThis);
					DEBUG(
						string name = task.predicates[predicate].getName();
						for (int i : tuple) name += " " + task.objects[i].getName();
						capsule.registerVariable(chooseThis,to_string(time) + " @ action " + task.actions[action].get_name() + " prec " + to_string(prec) + " chooses " + name);
						cout << to_string(time) + " @ action " + task.actions[action].get_name() + " prec " + to_string(prec) + " chooses " + name << endl;
					);

					implies(solver, chooseThis, factVar);
					for (int i : impliedVars)
						implies(solver, chooseThis, i);

				}
				// select one achiever
				impliesOr(solver,actionVar,achiever);
				precSupportMonotone += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();
				continue;
			}
			
			if (task.predicates[predicate].getName().rfind("=", 0) == 0){
				bef = get_number_of_clauses();
				if (!precObjec.negated){
					cout << "ERROR: linear encoding does not support equals constraints in preconditions yet." << endl;
					exit(-1);
				}
				if (precObjec.arguments[0].constant || precObjec.arguments[1].constant){
					cout << "ERROR: linear encoding does not support constants in equals yes." << endl;
					exit(-1);
				}
				int var1 = actionArgumentPositions[action][precObjec.arguments[0].index];
				int var2 = actionArgumentPositions[action][precObjec.arguments[1].index];
				
				int lower1 = lowerTindex[typeOfArgument[var1]];
				int lower2 = lowerTindex[typeOfArgument[var2]];
				int upper1 = upperTindex[typeOfArgument[var1]];
				int upper2 = upperTindex[typeOfArgument[var2]];
				// only constants in the intersection are actually relevant
				int lower = max(lower1,lower2);
				int upper = min(upper1,upper2);


				// generated an not equals constraint between them
				for(int o = 0; o < numObjs; o++){
					if (o < lower || o > upper)
						continue;
					
					int constantVar1 = parameterVarsTime[var1][o - lower1];
					int constantVar2 = parameterVarsTime[var2][o - lower2];

					andImpliesNot(solver, actionVar, constantVar1, constantVar2);

				}
				parameterEqualsConstraints += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();
				continue;
			}


			bef = get_number_of_clauses();
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
							int upper = upperTindex[typeOfArgument[argPos]];
							// tuple constant that does not git
							if (myObjIndex < lower || myObjIndex > upper) continue;
							int constantVar = parameterVarsTime[argPos][myObjIndex - lower];
							possibleValues.push_back(constantVar);

							DEBUG(cout << " " << capsule.variableNames[constantVar]);
						}
					}
					DEBUG(cout << endl);
					
					impliesOr(solver, actionVar, possibleValues); 
				} else {
					DEBUG(cout << "Static Precondition on " << task.predicates[predicate].getName() << endl);
					for (size_t lastPos = 0; lastPos < size_t(task.predicates[predicate].getArity() - 1) ; lastPos++){
						DEBUG(cout << "Generating Static Layer " << lastPos << endl);
						map<vector<int>,set<int>> possibleUpto;
				
						// build assignment tuple up to this point
						for (size_t i = 0; i < supportingPredicateTuples[predicate].size(); i++){
							vector<int> tuple = supportingPredicateTuples[predicate][i].first;
							vector<int> subTuple;
							subTuple.push_back(actionVar);

							bool impossible = false;
							int nextConstantVar = -1;
						
							for (size_t j = 0; !impossible && j <= lastPos+1; j++){
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
									int upper = upperTindex[typeOfArgument[argPos]];
									
									if (myObjIndex < lower || myObjIndex > upper) { impossible = true; continue; } 
								
									int constantVar = parameterVarsTime[argPos][myObjIndex - lower];
									if (j == lastPos+1)
										nextConstantVar = constantVar;
									else
										subTuple.push_back(constantVar);
								}
							}
							
							if (!impossible) possibleUpto[subTuple].insert(nextConstantVar);
							// force generation of this entry, but *only* if there is a actually a subtuple
							// i.e. a beginning of a static instance that we want to continue
							else if (lastPos != 0) possibleUpto[subTuple].size(); 
						}
			
						if (possibleUpto.size() == 0)
							assertNot(solver, actionVar); // this action is statically impossible
						
						for (auto & x : possibleUpto){
							andImpliesOr(solver,x.first,x.second);
							DEBUG(for (int i : x.first) {
									cout << " - [" << i << " " << capsule.variableNames[i] << "]";
							}
							for (int i : x.second) cout << " [" << capsule.variableNames[i] << "]";
							cout << endl);
						}
						
				
						if (lastPos == 0){
							int posOfValue = 1;
							vector<int> initial;
							for (auto & x : possibleUpto)
								initial.push_back(x.first[posOfValue]);
							
							DEBUG(cout << "Initial values:";
							for (int i : initial) cout << " [" << i << " " << capsule.variableNames[i] << "]";
							cout << endl;
									);
							impliesOr(solver,actionVar,initial);
						}
					}
				}
				staticPrecondition += get_number_of_clauses() - bef;
			} else {
				vector<int> precSlotVars;
	
				int thisWidth = width;
				bool stableMode = false;
				// precondition on a stable predicate. Must be one of the slots we have.
				if (predicateStable.count(predicate)){
					thisWidth = predicateStable[predicate];
					stableMode = true;
				}

				for (int slot = 0; slot < thisWidth; slot++){
					int precSlotVar = capsule.new_variable();
					precSlotVars.push_back(precSlotVar);
					DEBUG(capsule.registerVariable(precSlotVar,to_string(time) + " @ action " + task.actions[action].get_name() + " prec " + to_string(prec) + " slot " + to_string(slot)));
					
					implies(solver, -actionVar, -precSlotVar);


					if (!stableMode)
						// if we select this slot, we actually have to have the correct fact there
						andImplies(solver, actionVar, precSlotVar, predicateSlotVariables[time][slot][predicate]);

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < precObjec.arguments.size(); iArg++){
						int preconditionVar = precObjec.arguments[iArg].index;
						const bool pIsConst = precObjec.arguments[iArg].constant;
						int myParam = iArg;
						if (!stableMode) myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar;
							if (stableMode)
								constantVar = stablePredicateArgumentSlotVariables[time][predicate][slot][myParam][myObjIndex];
							else
								constantVar = argumentSlotVariables[time][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];

							andImplies(solver, actionVar, precSlotVar, constantVar); 
						} else {
							// variable equality
							andImplies(solver, actionVar, precSlotVar, equalBefore[predicate][actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
				}


				impliesOr(solver,actionVar,precSlotVars);
				if (stableMode)
					precSupportStable += get_number_of_clauses() - bef;
				else
					precSupport += get_number_of_clauses() - bef;
			}
			bef = get_number_of_clauses();
		}
	}


	vector<vector<int>> slotsSupporter(width);
	vector<vector<vector<int>>> stableSlotsSupporter(task.predicates.size());
	for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
		if (predicateStable.count(predicate) == 0) continue;
		stableSlotsSupporter[predicate].resize(predicateStable[predicate]);
	}
	// predicate -> [(action, [parameter or constants])]   numbers 0 or greater indicate variables, number less than 0 indicate constants
	map<int, vector<pair<int, vector<int> >>  > monotoneIncreasingCausing;


	// adding effects
	for (size_t action = 0; action < task.actions.size(); action++){
		if (phaseloop.size() && leavingActions[phaseloop[curPhase]].count(action) == 0) continue;
		
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);


		// we first need to encode the adding effects to have the slot supporter variables to correctly encode the precendence of adds over deletes

		vector<set<int>> thisActionSlotsSupporter(width);
		vector<vector<set<int>>> thisActionStableSlotsSupporter(task.predicates.size());
		for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
			if (predicateStable.count(predicate) == 0) continue;
			thisActionStableSlotsSupporter[predicate].resize(predicateStable[predicate]);
		}

		const auto effs = task.actions[action].get_effects();
		for (size_t eff = 0; eff < effs.size(); eff++) {
			bef = get_number_of_clauses();
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 
			if (task.predicates[predicate].getArity() == 0) continue; 
			
			if (predicateNoPreMonotone.count(predicate) || predicatesMonotoneNegEncoding.count(predicate)){
				//if (predicatesMonotoneNegEncoding.count(predicate)) continue; // for debugging
				// special predicate that is only relevant w.r.t to the goal.
				// This is necessarily an adding effect
				if (effObjec.negated && predicateNoPreMonotone.count(predicate)){
					cout << "Deleting Effect on monotone increasing predicate ..." << endl;
					exit(-2);
				}
				if (!effObjec.negated && predicatesMonotoneNegEncoding.count(predicate)){
					cout << "Adding Effect on monotone decreasing predicate ..." << endl;
					exit(-2);
				}
				
				vector<int> parameterOrConstants;

				for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
					int preconditionVar = effObjec.arguments[iArg].index;
					const bool pIsConst = effObjec.arguments[iArg].constant;

					// argument in the precondition might be a constant 
					if (pIsConst){
						parameterOrConstants.push_back(-preconditionVar - 1);
					} else {
						parameterOrConstants.push_back(actionArgumentPositions[action][preconditionVar]);
					}
				}


				if (predicateNoPreMonotone.count(predicate)){
					monotoneIncreasingCausing[predicate].push_back({actionVar,parameterOrConstants});
				} else {
					for (auto [tuple, factVar] : monotoneDecreasingPredicates[time+1][predicate]){
						set<int> impliedVars; impliedVars.insert(actionVar);
						bool badDeleter = false;
						for (size_t pos = 0; pos < parameterOrConstants.size(); pos++){
							int parameter  = parameterOrConstants[pos];
							if (parameter < 0){
								parameter = -parameter - 1;

								if (parameter != tuple[pos]) badDeleter = true;
							} else {
								int lower = lowerTindex[typeOfArgument[parameter]];
								int upper = upperTindex[typeOfArgument[parameter]];
								int objIndex = objToIndex[tuple[pos]];

								if (objIndex < lower || objIndex > upper)
									badDeleter = true;
								else
									impliedVars.insert(parameterVarsTime[parameter][objIndex - lower]);
							}
						}
						if (badDeleter) continue;

						// if this action matches the fact then it becomes false
						andImplies(solver, impliedVars, -factVar);
					}
				}
				
				delEffectsMonotone += get_number_of_clauses() - bef;
				continue;
			}

			int thisWidth = width;
			bool stableMode = false;
			// effect on a stable predicate. Must be one of the slots we have.
			if (predicateStable.count(predicate)){
				thisWidth = predicateStable[predicate];
				stableMode = true;
			}


			if (!effObjec.negated){
				vector<int> effSlotVars;
				for (int slot = 0; slot < thisWidth; slot++){
					int effSlotVar = capsule.new_variable();
					effSlotVars.push_back(effSlotVar);
					
					if (stableMode){
						stableSlotsSupporter[predicate][slot].push_back(effSlotVar);
						thisActionStableSlotsSupporter[predicate][slot].insert(effSlotVar);
					} else {
						slotsSupporter[slot].push_back(effSlotVar);
						thisActionSlotsSupporter[slot].insert(effSlotVar);
					}
					
					if (stableMode)
						DEBUG(capsule.registerVariable(effSlotVar,to_string(time) + " @ action " + task.actions[action].get_name() + " eff " + to_string(eff) + " slot " + to_string(slot) + " pred " + task.predicates[predicate].getName()));
					else
						DEBUG(capsule.registerVariable(effSlotVar,to_string(time) + " @ action " + task.actions[action].get_name() + " eff " + to_string(eff) + " slot " + to_string(slot)));


					implies(solver, -actionVar, -effSlotVar);

					// predicate only needs to be enforced for unstable predicates
					if (!stableMode){
						// if we select this slot, we actually have to have the correct fact there
						for (size_t p = 0; p < task.predicates.size(); p++){
							int pVar = predicateSlotVariables[time+1][slot][p];
							if (pVar == -1) continue; // static or = or type@
							if (p == size_t(predicate))
								andImplies(solver, actionVar, effSlotVar, pVar);
							else 
								andImpliesNot(solver, actionVar, effSlotVar, pVar);

							DEBUG(cout << "YYY " << actionVar << " " << effSlotVar << " " << predicateSlotVariables[time+1][slot][predicate] << endl); 
						}
					}

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
						int preconditionVar = effObjec.arguments[iArg].index;
						const bool pIsConst = effObjec.arguments[iArg].constant;
						int myParam = iArg;
					   	if (!stableMode) myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar;
						   	if (stableMode)
								constantVar	= argumentSlotVariables[time+1][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							else
								constantVar	= stablePredicateArgumentSlotVariables[time+1][predicate][slot][myParam][myObjIndex];
							
							andImplies(solver, actionVar, effSlotVar, constantVar); 
						} else {
							// variable equality
							andImplies(solver, actionVar, effSlotVar, equalAfter[predicate][actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
				}
				// we don't need to force that we have that effect ...
				//impliesOr(solver,actionVar,effSlotVars);
			}
			if (stableMode)
				addEffectsStable += get_number_of_clauses() - bef;
			else
				addEffects += get_number_of_clauses() - bef;
		}
		bef = get_number_of_clauses();

		// deleting effects
		for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 
			if (task.predicates[predicate].getArity() == 0) continue; 
			if (predicateNoPreMonotone.count(predicate) || predicatesMonotoneNegEncoding.count(predicate)) continue;

			int thisWidth = width;
			bool stableMode = false;
			// effect on a stable predicate. Must be one of the slots we have.
			if (predicateStable.count(predicate)){
				thisWidth = predicateStable[predicate];
				stableMode = true;
			}

			if (effObjec.negated){
				// must not be present in any of the slots
				for (int slot = 0; slot < thisWidth; slot++){
					vector<int> equalFact;
					equalFact.push_back(actionVar);
					if (!stableMode) equalFact.push_back(predicateSlotVariables[time+1][slot][predicate]);

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
						int preconditionVar = effObjec.arguments[iArg].index;
						const bool pIsConst = effObjec.arguments[iArg].constant;
						int myParam = iArg;
						if (!stableMode) myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar;
						   	if (stableMode)
								constantVar	= stablePredicateArgumentSlotVariables[time+1][predicate][slot][myParam][myObjIndex];
							else
								constantVar	= argumentSlotVariables[time+1][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							equalFact.push_back(constantVar); 
						} else {
							// variable equality
							equalFact.push_back(equalAfter[predicate][actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
					if (stableMode)
						andImpliesOr(solver,equalFact,thisActionStableSlotsSupporter[predicate][slot]);
					else
						andImpliesOr(solver,equalFact,thisActionSlotsSupporter[slot]);
					//notAll(solver,equalFact);
				}
				if (stableMode)
					delEffectsStable += get_number_of_clauses() - bef;
				else
					delEffects += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();
			}
		}
	}

	bef = get_number_of_clauses();
	DEBUG(cout << "NULLARY" << endl);
	for (size_t action = 0; action < task.actions.size(); action++){
		if (phaseloop.size() && leavingActions[phaseloop[curPhase]].count(action) == 0) continue;
		
		int actionVar = actionVars[time][action];
		if (generateBaseFormula){

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
	}	
	// frame axioms for nullary predicates
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
	
	lastNullary = currentNullary;

	// frame axioms	
	if (numberOfPredicateArgumentPositions) for (int slot = 0; slot < width; slot++){
		// idea: either the slot got overridden by an effect or is it the same as the slot before
		int slotEqual = capsule.new_variable();
		DEBUG(capsule.registerVariable(slotEqual,to_string(time) + " = " + to_string(time+1) + " @ slot " + to_string(slot)));
		
		// same predicate
		for (size_t pred = 0; pred < task.predicates.size(); pred++){
			int predBefore = predicateSlotVariables[time  ][slot][pred];
			int predAfter  = predicateSlotVariables[time+1][slot][pred];
			if (predBefore == -1) continue;

			andImplies(solver,slotEqual, predAfter, predBefore);
			//andImplies(solver,slotEqual, predBefore, predAfter);
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
				andImplies(solver,slotEqual, constAfter, constBefore);
				//andImplies(solver,slotEqual, constBefore, constAfter);
				//andImplies(solver,constBefore, constAfter, slotEqual); maintenance does not have to be exact -- don't use this one. It actually makes things incorrect

			}
		}
		
		frameEqual += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();

		// if we don't have a supporter for the current value, it must be the old one
		notImpliesOr(solver, slotEqual, slotsSupporter[slot]);
		frameImplies += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();
	}

	// frame axioms	for stable 
	for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
		vector<vector<vector<int>>> thisPredicateAgumentVariables;
		if (predicateStable.count(predicate) == 0) continue;

		// we need to do all this generation for each slot
		for (int slot = 0; slot < predicateStable[predicate]; slot++){
			// idea: either the slot got overridden by an effect or is it the same as the slot before
			int slotEqual = capsule.new_variable();
			DEBUG(capsule.registerVariable(slotEqual,to_string(time) + " = " + to_string(time+1) + " @ slot " + to_string(slot) + " " + task.predicates[predicate].getName()));
			
			// predicate is always identical so go figure ...
			for (int factParameter = 0; factParameter < task.predicates[predicate].getArity(); factParameter++){
				int lower = lowerTindex[task.predicates[predicate].getTypes()[factParameter]];
				int upper = upperTindex[task.predicates[predicate].getTypes()[factParameter]];
	
				for(int o = 0; o < numObjs; o++){
					if (o < lower || o > upper)
						continue;

					// need to subtract the starting values of the types
					int constBefore = stablePredicateArgumentSlotVariables[time  ][predicate][slot][factParameter][o];
					int constAfter  = stablePredicateArgumentSlotVariables[time+1][predicate][slot][factParameter][o];
					if (predicateMaxStable.count(predicate) == 0)
						andImplies(solver,slotEqual, constBefore, constAfter);
					andImplies(solver,slotEqual, constAfter, constBefore);
					//andImplies(solver,constBefore, constAfter, slotEqual); maintenance does not have to be exact -- don't use this one. It actually makes things incorrect

				}
			}
			
			frameEqualStable += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();

			// if we don't have a supporter for the current value, it must be the old one
			notImpliesOr(solver, slotEqual, stableSlotsSupporter[predicate][slot]);
			frameImpliesStable += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();
		}
	}

	// frame axioms for monotone increasing facts
	bef = get_number_of_clauses();
	for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
		if (predicateNoPreMonotone.count(predicate) == 0) continue;

		for (auto [tuple, factVar] : monotoneIncreasingPredicates[time+1][predicate]){
			vector<int> achiever;
			achiever.push_back(monotoneIncreasingPredicates[time][predicate][tuple]);

			// iterate over possible achievers
			for (auto [actionVar, parameterVars] : monotoneIncreasingCausing[predicate]){
				vector<int> impliedVars; impliedVars.push_back(actionVar);
				bool badAchiever = false;
				for (size_t pos = 0; pos < parameterVars.size(); pos++){
					int parameter  = parameterVars[pos];
					if (parameter < 0){
						parameter = -parameter - 1;

						if (parameter != tuple[pos]) badAchiever = true;
					} else {
						int lower = lowerTindex[typeOfArgument[parameter]];
						int upper = upperTindex[typeOfArgument[parameter]];
						int objIndex = objToIndex[tuple[pos]];

						if (objIndex < lower || objIndex > upper)
							badAchiever = true;
						else
							impliedVars.push_back(parameterVarsTime[parameter][objIndex - lower]);
					}
				}

				if (badAchiever) continue;
				int becomesTrue = capsule.new_variable();
				achiever.push_back(becomesTrue);
				DEBUG(
					string name = task.predicates[predicate].getName();
					for (int i : tuple) name += " " + task.objects[i].getName();
					capsule.registerVariable(becomesTrue, to_string(time) + " @ " + name + " becomes true from " + to_string(actionVar));
				);
				
				for (int i : impliedVars)
					implies(solver,becomesTrue, i);
			
			}
			impliesOr(solver,factVar, achiever);
		}
	}
	frameMonotoneRising += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();

	// monotone decreasing are very simple 
	for (int predicate = 0; predicate < int(task.predicates.size()); predicate++){
		if (predicatesMonotoneNegEncoding.count(predicate) == 0) continue;
		for (auto [tuple, factVar] : monotoneDecreasingPredicates[time+1][predicate]){
			implies(solver,factVar, monotoneDecreasingPredicates[time][predicate][tuple]);
		}
	}
	frameFacts += get_number_of_clauses() - bef;
}


bool LiftedLinearSAT::callSolver(sat_capsule & capsule, void* solver, const Task &task, int width, const std::clock_t & startTime, long long time_limit_in_ms){
		
	DEBUG(capsule.printVariables());
int individuallyCounted = atMostOneParamterValue +
atMostOnePredicate +
atMostOnePredicateValueArgument +
actionTyping +
predicateTyping +
precSupport +
precSupportStable +
precSupportMonotone + 
staticPrecondition + 
addEffectsStable +
delEffectsMonotone +
frameMonotoneRising +
frameEqualStable +
frameImpliesStable +
equalsStable +
equals +
initSupp +
initSuppStable +
initSuppGrounded +
goalAchiever +
nullary +
oneAction +
addEffects + 
delEffects +
delEffectsStable +
frameEqual + 
frameImplies +
frameFacts + 
parameterEqualsConstraints;

	cout << "Generated Variables " << setw(10) << capsule.number_of_variables <<
		" Clauses: " << setw(10) << get_number_of_clauses() << " length " << planLength << " width " << width << endl;
	cout << "Number of clauses submitted to solver: " << clauseCount << " individually counded: " << individuallyCounted <<
			" equalCounted: " << (clauseCount == individuallyCounted) << endl; 

	cout << "\tFS max 1 action                 " << setw(9) << oneAction                       << " " << fixed << setprecision(6) << double(oneAction                      ) / clauseCount << endl; 
	cout << "\tFS max 1 action param value     " << setw(9) << atMostOneParamterValue          << " " << fixed << setprecision(6) << double(atMostOneParamterValue         ) / clauseCount << endl;
	cout << "\tFS max 1 predicate              " << setw(9) << atMostOnePredicate              << " " << fixed << setprecision(6) << double(atMostOnePredicate             ) / clauseCount << endl;
	cout << "\tFS max 1 predicate param value  " << setw(9) << atMostOnePredicateValueArgument << " " << fixed << setprecision(6) << double(atMostOnePredicateValueArgument) / clauseCount << endl;
	cout << "\tFS typing actions               " << setw(9) << actionTyping                    << " " << fixed << setprecision(6) << double(actionTyping                   ) / clauseCount << endl;
	cout << "\tFS typing predicates            " << setw(9) << predicateTyping                 << " " << fixed << setprecision(6) << double(predicateTyping                ) / clauseCount << endl;
	cout << "\tFS parameter (not) equals       " << setw(9) << parameterEqualsConstraints      << " " << fixed << setprecision(6) << double(parameterEqualsConstraints     ) / clauseCount << endl;
	cout << "\tFS prec met general slots       " << setw(9) << precSupport                     << " " << fixed << setprecision(6) << double(precSupport                    ) / clauseCount << endl;
	cout << "\tFS prec met stable slots        " << setw(9) << precSupportStable               << " " << fixed << setprecision(6) << double(precSupportStable              ) / clauseCount << endl;
	cout << "\tFS prec met static              " << setw(9) << staticPrecondition              << " " << fixed << setprecision(6) << double(staticPrecondition             ) / clauseCount << endl;
	cout << "\tFS prec met monotone            " << setw(9) << precSupportMonotone             << " " << fixed << setprecision(6) << double(precSupportMonotone            ) / clauseCount << endl;
	cout << "\tFS add effects general          " << setw(9) << addEffects                      << " " << fixed << setprecision(6) << double(addEffects                     ) / clauseCount << endl; 
	cout << "\tFS add effects stable           " << setw(9) << addEffectsStable                << " " << fixed << setprecision(6) << double(addEffectsStable               ) / clauseCount << endl; 
	cout << "\tFS del effects genera           " << setw(9) << delEffects                      << " " << fixed << setprecision(6) << double(delEffects                     ) / clauseCount << endl; 
	cout << "\tFS del effects stable           " << setw(9) << delEffectsStable                << " " << fixed << setprecision(6) << double(delEffectsStable               ) / clauseCount << endl; 
	cout << "\tFS del effects monotone         " << setw(9) << delEffectsMonotone              << " " << fixed << setprecision(6) << double(delEffectsMonotone             ) / clauseCount << endl; 
	cout << "\tFS frame equals general         " << setw(9) << frameEqual                      << " " << fixed << setprecision(6) << double(frameEqual                     ) / clauseCount << endl;
	cout << "\tFS frame implies general        " << setw(9) << frameImplies                    << " " << fixed << setprecision(6) << double(frameImplies                   ) / clauseCount << endl;
	cout << "\tFS frame equals stable          " << setw(9) << frameEqualStable                << " " << fixed << setprecision(6) << double(frameEqualStable               ) / clauseCount << endl;
	cout << "\tFS frame implies stable         " << setw(9) << frameImpliesStable              << " " << fixed << setprecision(6) << double(frameImpliesStable             ) / clauseCount << endl;
	cout << "\tFS frame facts monotone rising  " << setw(9) << frameMonotoneRising             << " " << fixed << setprecision(6) << double(frameMonotoneRising            ) / clauseCount << endl;
	cout << "\tFS frame facts monotone decr.   " << setw(9) << frameFacts                      << " " << fixed << setprecision(6) << double(frameFacts                     ) / clauseCount << endl;
	cout << "\tFS equals (with state) general  " << setw(9) << equals                          << " " << fixed << setprecision(6) << double(equals                         ) / clauseCount << endl;
	cout << "\tFS equals (with state) stable   " << setw(9) << equalsStable                    << " " << fixed << setprecision(6) << double(equalsStable                   ) / clauseCount << endl;
	cout << "\tFS init support general         " << setw(9) << initSupp                        << " " << fixed << setprecision(6) << double(initSupp                       ) / clauseCount << endl;
	cout << "\tFS init support stable          " << setw(9) << initSuppStable                  << " " << fixed << setprecision(6) << double(initSuppStable                 ) / clauseCount << endl;
	cout << "\tFS init support ground          " << setw(9) << initSuppGrounded                << " " << fixed << setprecision(6) << double(initSuppGrounded               ) / clauseCount << endl;
	cout << "\tFS goal achievers               " << setw(9) << goalAchiever                    << " " << fixed << setprecision(6) << double(goalAchiever                   ) / clauseCount << endl; 

	DEBUG(cout << "Starting solver" << endl);
	bool* stopFlag = nullptr;
	std::clock_t solver_start = std::clock();

	if (time_limit_in_ms != -1) {
		// the given timelimit is relative to the startTime clock

		double time_since_start_in_ms = 1000.0 * (solver_start - startTime) / CLOCKS_PER_SEC;
		double timelimit_for_solver = time_limit_in_ms - time_since_start_in_ms;
		cout << endl << "#### setting solver time limit "  << setw(10) << timelimit_for_solver << endl;
		if (timelimit_for_solver <= 20) return false; // generation of formula took too long
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
		DEBUG(cout << "timestep " << time << endl);
		for (size_t action = 0; action < task.actions.size(); action++){
			int var = actionVars[time][action];
			if (ipasir_val(solver,var) > 0){

				DEBUG(cout << "  " << task.actions[action].get_name());
            	auto params = task.actions[action].get_parameters();
				vector<int> arguments;
            	for (size_t l = 0; l < params.size(); l++) {
					int p = actionArgumentPositions[action][l];
					DEBUG(cout << " " << l << ":");
					for (int o = 0; o <= upperTindex[typeOfArgument[p]] - lowerTindex[typeOfArgument[p]]; o++){
						if (ipasir_val(solver,parameterVars[time][p][o]) > 0){
							DEBUG(cout << " " << task.objects[indexToObj[o + lowerTindex[typeOfArgument[p]]]].getName());
							arguments.push_back(indexToObj[o + lowerTindex[typeOfArgument[p]]]);
						}
					}
				}
				DEBUG(cout << endl);
				
				LiftedOperatorId op (action, move(arguments));
				plan.push_back(op);
			}
		}
	}

	print_plan(plan,task);
	cout << "Solution found." << endl;
	exit(0);
}



utils::ExitCode LiftedLinearSAT::solve(const Task &task, int limit, bool optimal, bool incremental, int width, int timelimitInSeconds) {
		
	double timelimitInMs = timelimitInSeconds * 1000;
	int iterationEnd;
	vector<int> satisficingLengths {3,5,10,25,50,100,200};
	if (optimal){
		iterationEnd = limit + 1; // we actually need to run this bound!
	} else {
		if (limit != 10000){
			satisficingLengths.clear();
			satisficingLengths.push_back(limit);
		}
		iterationEnd = satisficingLengths.size();
	}




	void* solver;
	sat_capsule capsule;
	if (incremental){
		solver = ipasir_init();
		planLength = 0;
	}
	
	std::clock_t overallStartTime = std::clock();
	
	for (int run = 0; run < iterationEnd; run++){

		long long this_time_limit = -1;	
		// this is the actual plan length we are looking for
		int i;
		if (optimal)
			i = run;
		else {
			cout << "Satisficing run " << run << " trying length bound " << satisficingLengths[run] << endl;
			i = satisficingLengths[run] - 1;
			std::clock_t now = std::clock();
			double time_since_start_in_ms = 1000.0 * (now - overallStartTime) / CLOCKS_PER_SEC;
			double remainingTime = timelimitInMs - time_since_start_in_ms;
			double myTimeSlice = remainingTime / (iterationEnd - run);

			if (remainingTime <= 0) return utils::ExitCode::SEARCH_OUT_OF_TIME;
			this_time_limit = (long long) myTimeSlice;
		}


		if (!incremental) {
			solver = ipasir_init();
			clauseCount = 0;
			capsule.number_of_variables = 0;
			DEBUG(capsule.variableNames.clear());
			reset_number_of_clauses();


			// reset formula size counters
			actionTyping = 0;
			atMostOneParamterValue = 0;
			predicateTyping = 0;
			precSupport = 0;
			precSupportStable = 0;
			precSupportMonotone = 0;
			staticPrecondition = 0;
			addEffectsStable = 0;
			delEffectsMonotone = 0;
			frameMonotoneRising = 0;
			frameEqualStable = 0;
			frameImpliesStable = 0;
			equalsStable = 0;
			equals = 0;
			initSupp = 0;
			initSuppStable = 0;
			initSuppGrounded = 0;
			nullary = 0;
			oneAction = 0; 
			goalAchiever = 0; 
			addEffects = 0;
			delEffects = 0;
			delEffectsStable = 0;
			frameEqual = 0;
			frameImplies = 0;
			frameFacts = 0;
			atMostOnePredicateValueArgument = 0;
			atMostOnePredicate = 0;
		   	parameterEqualsConstraints = 0;
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
			predicateSlotVariables.clear();
			argumentSlotVariables.clear();
			stablePredicateArgumentSlotVariables.clear();
			monotoneIncreasingPredicates.clear();
			monotoneDecreasingPredicates.clear();
		}
		
		
		// initialise 0-ary predicates either every time we run or once for incremental solving
		if (!incremental || i == 0){
			int clausesBefore = get_number_of_clauses();
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

		// calculate the width we actually need
		int widthNeeded = (i+1) * maximumTimeStepNetChange + goalNeededWidth;
		if (!foundOrdinaryPredicate) widthNeeded = 0;
		
		// if someone forced us to use lower width ...
		if (width < widthNeeded) widthNeeded = width;

		cout << color(COLOR_GREEN,"Solving for ") << "length " << i+1 << " with width " << widthNeeded << endl; 
	
		// if not in incremental mode, we need to generate the formula for all timesteps.
		if (!incremental){
			planLength = 0;
			generate_predicate_slot_layer(task, solver, capsule, widthNeeded, 0); // generate slots directly after init
		}
		
		bool linearIncrease = true;
		if (!linearIncrease){
			while (planLength <= (1 << i)-1){
				planLength++;
				generate_formula(task,solver,capsule,widthNeeded, optimal);
			}
		} else {
			while (planLength <= i){
				planLength++;
				generate_formula(task,solver,capsule,widthNeeded, optimal);
			}
		}

		generate_goal_assertion(task, solver, capsule, widthNeeded, planLength);

		if (callSolver(capsule,solver,task,widthNeeded,start, this_time_limit)){
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
