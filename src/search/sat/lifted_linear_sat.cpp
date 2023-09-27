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

	cout << endl << endl << "Predicate " << p.getName() << endl;
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}
		cout << "Action " << action << " balance " << netChange << endl;
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	cout  << "maximumNetChange = " << maximumNetChange << endl;
	return maximumNetChange;
}


int calculateOverallBalanceOfPredicatePair(const Task & task, int pIndex, int pIndex2){
	auto p = task.predicates[pIndex];
	auto p2 = task.predicates[pIndex2];
	if (p.getArity() + p2.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment
	if (p2.isStaticPredicate()) return 0; // static predicates get special treatment

	cout << endl << endl << "Predicate " << p.getName() << " Predicate " << p2.getName() << endl;
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex && predicate != pIndex2) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}
		if (p.getArity() == 0){
			int thisChange = calculateNullaryEffectBalance(task,action, pIndex);
			cout << "\tEff " << task.predicates[pIndex].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}
		if (p2.getArity() == 0){
			int thisChange = calculateNullaryEffectBalance(task,action, pIndex2);
			cout << "\tEff " << task.predicates[pIndex2].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}

		cout << "Action " << action << " balance " << netChange << endl;
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	cout  << "maximumNetChange = " << maximumNetChange << endl;
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
			cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}

		cout << "Action " << action << " balance " << netChange << endl;
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	cout  << "maximumNetChange = " << maximumNetChange << endl;
	return maximumNetChange;
}

int calculateOverallBalanceOfPredicateAndNullary(const Task & task, int pIndex, vector<int> arityZeroPredicates){
	auto p = task.predicates[pIndex];
	if (p.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment

	cout << endl << endl << "Predicate " << p.getName() << endl;
	int maximumNetChange = 0;
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto effs = task.actions[action].get_effects();
		const auto precs = task.actions[action].get_precondition();
		int netChange = 0;
	    for (size_t eff = 0; eff < effs.size(); eff++) {
			int predicate = effs[eff].predicate_symbol;
			if (predicate != pIndex) continue;

			int thisChange = calculateEffectBalance(task,task.actions[action], effs[eff]);
			cout << "\tEff " << task.predicates[predicate].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}

		for (int arityZeroPredicate : arityZeroPredicates){
			int thisChange = calculateNullaryEffectBalance(task,action, arityZeroPredicate);
			cout << "\tEff " << task.predicates[arityZeroPredicate].getName() << " " << thisChange << endl;
			netChange += thisChange;
		}
		
		cout << "Action " << task.actions[action].get_name() << " balance " << netChange << endl;
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}
	cout  << "maximumNetChange = " << maximumNetChange << endl;
	return maximumNetChange;
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


int calculateOverallBalanceOfPredicateInPhasing(const Task & task, int pIndex, vector<int> phasingPredicates){
	auto p = task.predicates[pIndex];
	if (p.getArity() == 0) return 0;
	if (p.isStaticPredicate()) return 0; // static predicates get special treatment
	cout << endl << endl << "Predicate " << p.getName() << endl;

	
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
		if (netChange == 0) continue; // this action does not manipulate predicate p
		
		int leavingPhase = -1;
		// check whether we leaving a phase
		for (int arityZeroPredicate : phasingPredicates){
			int thisChange = calculateNullaryEffectBalance(task,action, arityZeroPredicate);
			if (thisChange == -1)
				leavingPhase = arityZeroPredicate;
		}

		if (leavingPhase == -1) return 1; // might increase ...
		changesOnPhaseLeave[leavingPhase].insert(netChange);
	}
	int increasing = -1;
	for (auto [a,b] : changesOnPhaseLeave){
		cout << "Leave " << a << ":";
		for (auto i : b) cout << " " << i;
		cout << endl;

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
	cout << "Size in init " << numInInit << endl;
	return numInInit;
}

int predicateInInit(const Task & task, int pIndex){
	for (tSize i = 0; i < task.initial_state.get_relations().size(); i++) {
	    auto rel = task.initial_state.get_relations()[i];
	    auto tuple = task.initial_state.get_tuples_of_relation(i);
	    if (task.initial_state.get_relations()[i].predicate_symbol == pIndex){
			cout << "Size in init " << tuple.size() << endl;
			return tuple.size();
		}
	}
	return 0;
}



set<int> predicatesMonotoneNegEncoding;
map<int,int> predicateStable; // maps to size
map<int,int> predicateMaxStable; // maps to size
set<int> predicateNoPreMonotone;





LiftedLinearSAT::LiftedLinearSAT(const Task & task) {

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

			cout << "EFF " << eff << " " << balancer << " " << effObjec.negated << endl;
			
			if (effObjec.negated){
				if (balancer) netChange--;
			} else {
				if (!balancer) netChange++;
			}
		}
		cout << "Action " << action << " balance " << netChange << endl;
		if (netChange > maximumNetChange) maximumNetChange = netChange;
	}

	cout << "maximumNetChange = " << maximumNetChange << endl;


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


	vector<int> phasingStructure;

	for (unsigned int s = 1; s < (1 << (allArityZeroPredicates.size())); s++){
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
			cout << color(COLOR_YELLOW, "Found Plan Phasing Structure:");
			for (int i : thisList)
				cout << " " << task.predicates[i].getName();
			cout << endl;

			if (thisList.size() > phasingStructure.size())
				phasingStructure = thisList;
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


	for (int pIndex = 0; pIndex < int(task.predicates.size()); pIndex++) {
		if (task.predicates[pIndex].getArity() == 0) continue;
		if (task.predicates[pIndex].isStaticPredicate()) continue; // static predicates get special treatment
		for (unsigned int s = 1; s < (1 << (allArityZeroPredicates.size())); s++){
			vector<int> thisList;
			for (unsigned int i = 0; i < allArityZeroPredicates.size(); i++)
				if (s & (1 << i)) thisList.push_back(allArityZeroPredicates[i]);

			int netChange = calculateOverallBalanceOfPredicateAndNullary(task,pIndex,allArityZeroPredicates);
			if (netChange == 0)
				cout << task.predicates[pIndex].getName() << color(COLOR_RED, " Net Change: ") << netChange;
			else
				cout << task.predicates[pIndex].getName() << " Net Change: " << netChange;
			for (int i : thisList)
				cout << " " << task.predicates[i].getName();
			cout << endl;
		}
	}




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
	for (unsigned int s = 1; s < (1 << (allArityNonZeroPredicates.size())); s++){
		set<int> thisList;
		int initially = 0;
		for (unsigned int i = 0; i < allArityNonZeroPredicates.size(); i++)
			if (s & (1 << i)) {
				thisList.insert(allArityNonZeroPredicates[i]);
				initially += predicateInInit(task,allArityNonZeroPredicates[i]);
			}
		if (thisList.size() <= 2) continue; // done previously
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
		bool isMonotoneNeg = true;
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
					isMonotoneNeg = false;
					achievers.push_back(action); // if it makes multiple goals true -> can't handle that ...
				}
			}
		}

		// TODO technically the monotonicity is nice to have, but not really necessary as we can just track all facts that are true in the goal individually
		if (!occursInPre && isMonotonePos){
			// there might be just one achiever for such predicate	
			if (achievers.size() == 1){
				int action = achievers[0];
				cout << "Only one achiever action: " << task.actions[action].get_name() << endl;
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
					cout << "Only achiever has no side effects. So its preconditions are only relevant if connected to the goal." << endl;
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
					const auto goalEffect = task.actions[achieverAction].get_effects()[achieverEffect];

					for (size_t i = 0; i < goalEffect.arguments.size(); i++){
						if (goalEffect.arguments[i].constant) continue; // don't care about this one
						effectVariables.insert(goalEffect.arguments[i].index);
					}
				
					vector<int> additionalAruguments;	
					for (size_t i = 0; i < precObjec.arguments.size(); i++){
						if (precObjec.arguments[i].constant) continue; // don't care about this one
						if (effectVariables.count(precObjec.arguments[i].index)) continue;
						additionalAruguments.push_back(precObjec.arguments[i].index);
					}
					if (additionalAruguments.size() == 0){
						// TODO keep track!
						continue; // this is a good precondition - we only need to track its truth as far as it pertains to the goal
					}

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

						DEBUG(cout << " " << arg << " (domain: ";
					  	for (int obj : possibleValues) cout << " " << obj;
						cout << " )");
						
						if (possibleValues.size() != 1) occursInPre = true;
						else {
							// memorise this one value
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
			cout << "\t" << color(COLOR_CYAN, "Decision: ") << "monotone neg" << endl;
		} else if (!occursInPre && isMonotonePos) {
			predicateNoPreMonotone.insert(pIndex);
			cout << "\t" << color(COLOR_CYAN, "Decision: ") << "no precondition monotone" << endl;
		} else if (stablePredicates.count(pIndex)){
			predicateStable[pIndex] = stablePredicates[pIndex];
			cout << "\t" << color(COLOR_CYAN, "Decision: ") << "stable " << predicateStable[pIndex] << endl;
		} else if (maxStablePredicates.count(pIndex)){
			predicateMaxStable[pIndex] = maxStablePredicates[pIndex];
			cout << "\t" << color(COLOR_CYAN, "Decision: ") << "max stable " << predicateMaxStable[pIndex] << endl;
		} else {
			cout << "\t" << color(COLOR_RED, "Decision: ") << "normal" << endl;
		}
		cout << endl << endl;
	}

	/////////////////////////////////////////////////////////////////////////////////////////////////////////
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

	for (size_t pIndex = 0; pIndex < task.predicates.size(); pIndex++){
    	const auto & p = task.predicates[pIndex];
		if (p.isStaticPredicate()) continue; // static predicates get special treatment
		if (predicateStable.count(pIndex)) continue;
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
		if (predicateStable.count(pIndex)) continue;
		
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


	// preconditions are actually met
	for (size_t action = 0; action < task.actions.size(); action++){
		const auto precs = task.actions[action].get_precondition();
        for (size_t prec = 0; prec < precs.size(); prec++) {
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getArity() == 0) continue; 
			
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue;
		
			if (!task.predicates[predicate].isStaticPredicate()){
				// iterate over the arguments of the precondition
				for (size_t iArg = 0; iArg < precObjec.arguments.size(); iArg++){
					int preconditionVar = precObjec.arguments[iArg].index;
					const bool pIsConst = precObjec.arguments[iArg].constant;
					int myParam = predicateArgumentPositions[predicate][iArg];

					// argument in the precondition might be a constant 
					if (!pIsConst){
						// variable equality
						int predSlot = actionArgumentPositions[action][preconditionVar];
						possibleBeforeEquals.insert({predSlot, myParam});
						//cout << predSlot << " " << myParam << endl;
					}
				}
			}
		}
	}


	// adding effects
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
				int myParam = predicateArgumentPositions[predicate][iArg];

				// argument in the precondition might be a constant 
				if (!pIsConst){
					int afterSlot = actionArgumentPositions[action][preconditionVar];
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
int frameEqual = 0;
int frameImplies = 0;
int parameterEqualsConstraints = 0;

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

vector<vector<vector<int>>> LiftedLinearSAT::generate_action_state_equality(const Task &task, void* solver, sat_capsule & capsule, int width, int actionTime, int stateTime){

	// variables for argument pos X = slot Y parameter pos Z
	vector<vector<vector<int>>> equalsVars;

	int bef = get_number_of_clauses();
    for (int actionParamter = 0; actionParamter < numberOfArgumentPositions; actionParamter++){
		vector<vector<int>> eqVars;
		for (int slot = 0; slot < width; slot++){
			vector<int> eqVarsSlot;
	   		for (int factParameter = 0; factParameter < numberOfPredicateArgumentPositions; factParameter++){
				if ((actionTime == stateTime && possibleBeforeEquals.count({actionParamter,factParameter}) == 0) ||
					(actionTime + 1 == stateTime && possibleAfterEquals.count({actionParamter,factParameter}) == 0)){
					eqVarsSlot.push_back(-1);
					continue;
				}

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
				task.predicates[predicate].isStaticPredicate() || 
				task.predicates[predicate].getArity() == 0 || 
				predicateStable.count(predicate)
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
		if (time == 0){ // this should only be really necessary at time 0 as this property gets inherited to all other time steps
			atMostOne(solver,capsule,thisSlotPredicatesAMO);
			atLeastOne(solver,capsule,thisSlotPredicatesAMO);
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
			for (size_t predicate = 0; predicate < task.predicates.size(); predicate++){
				if (task.predicates[predicate].getArity() == 0) continue;
				if (task.predicates[predicate].isStaticPredicate()) continue; // nothing to do

				// consider how many arguments are there
				int predicateVar = thisSlotPredicates[predicate];
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
				
						//cout << "B" << endl;
				
						for (auto & x : possibleUpto){
							andImpliesOr(solver,x.first,x.second);
							DEBUG(for (int i : x.first) cout << " - [" << capsule.variableNames[i] << "]";
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
							DEBUG(cout << "- [" << capsule.variableNames[predicateVar] << "]";
							for (int i : initial) cout << " [" << capsule.variableNames[i] << "]";
							cout << endl);
						}
						
						//cout << "D " << task.predicates[predicate].getArity() << endl;
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
	oneAction += get_number_of_clauses() - bef;
	bef = get_number_of_clauses();


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
	for (size_t action = 0; action < task.actions.size(); action++){
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);

		const auto precs = task.actions[action].get_precondition();
        for (size_t prec = 0; prec < precs.size(); prec++) {
			const auto & precObjec = precs[prec];
			int predicate = precObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getArity() == 0) continue; 
			
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
			precSupport += get_number_of_clauses() - bef;
			bef = get_number_of_clauses();
		}
	}


	vector<vector<int>> slotsSupporter(width);

	// adding effects
	for (size_t action = 0; action < task.actions.size(); action++){
		int actionVar = actionVars[time][action];
        DEBUG(cout << "\t" << time << " " << action << " " << task.actions[action].get_name() << " = " << actionVar << endl);


		// we first need to encode the adding effects to have the slot supporter variables to correctly encode the precendence of adds over deletes

		vector<set<int>> thisActionSlotsSupporter(width);
		const auto effs = task.actions[action].get_effects();
		for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 
			if (task.predicates[predicate].getArity() == 0) continue; 

			if (!effObjec.negated){
				vector<int> effSlotVars;
				for (int slot = 0; slot < width; slot++){
					int effSlotVar = capsule.new_variable();
					effSlotVars.push_back(effSlotVar);
					slotsSupporter[slot].push_back(effSlotVar);
					thisActionSlotsSupporter[slot].insert(effSlotVar);
					DEBUG(capsule.registerVariable(effSlotVar,to_string(time) + " @ action " + task.actions[action].get_name() + " eff " + to_string(eff) + " slot " + to_string(slot) + " pred " + task.predicates[predicate].getName()));


					implies(solver, -actionVar, -effSlotVar);

					// if we select this slot, we actually have to have the correct fact there
					for (size_t p = 0; p < task.predicates.size(); p++){
						int pVar = predicateSlotVariables[time+1][slot][p];
						if (pVar == -1) continue; // static or = or type@
						if (p == predicate)
							andImplies(solver, actionVar, effSlotVar, pVar);
						else 
							andImpliesNot(solver, actionVar, effSlotVar, pVar);

						DEBUG(cout << "YY " << actionVar << " " << effSlotVar << " " << predicateSlotVariables[time+1][slot][predicate] << endl); 
					}

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
				addEffects += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();
			}
		}


		for (size_t eff = 0; eff < effs.size(); eff++) {
			const auto & effObjec = effs[eff];
			int predicate = effObjec.predicate_symbol;
			if (task.predicates[predicate].getName().rfind("type@", 0) == 0) continue;
			if (task.predicates[predicate].getName().rfind("=", 0) == 0) continue; 
			if (task.predicates[predicate].getArity() == 0) continue; 


			if (effObjec.negated){
				// must not be present in any of the slots
				for (int slot = 0; slot < width; slot++){
					vector<int> equalFact;
					equalFact.push_back(actionVar);
					equalFact.push_back(predicateSlotVariables[time+1][slot][predicate]);

					// iterate over the arguments of the precondition
					for (size_t iArg = 0; iArg < effObjec.arguments.size(); iArg++){
						int preconditionVar = effObjec.arguments[iArg].index;
						const bool pIsConst = effObjec.arguments[iArg].constant;
						int myParam = predicateArgumentPositions[predicate][iArg];

						// argument in the precondition might be a constant 
						if (pIsConst){
							int myObjIndex = objToIndex[preconditionVar]; // is not actually a var, but the number of the constant ...
							int constantVar = argumentSlotVariables[time+1][slot][myParam][myObjIndex - lowerTindex[typeOfPredicateArgument[myParam]]];
							equalFact.push_back(constantVar); 
						} else {
							// variable equality
							equalFact.push_back(equalAfter[actionArgumentPositions[action][preconditionVar]][slot][myParam]); 
						}
					}
					andImpliesOr(solver,equalFact,thisActionSlotsSupporter[slot]);
					//notAll(solver,equalFact);
				}
				delEffects += get_number_of_clauses() - bef;
				bef = get_number_of_clauses();
			}
		}

	}


	bef = get_number_of_clauses();
	for (size_t action = 0; action < task.actions.size(); action++){
		int actionVar = actionVars[time][action];
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
		
		frameEqual += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();

		// if we don't have a supporter for the current value, it must be the old one
		notImpliesOr(solver, slotEqual, slotsSupporter[slot]);
		frameImplies += get_number_of_clauses() - bef;
		bef = get_number_of_clauses();
	}
}


bool LiftedLinearSAT::callSolver(sat_capsule & capsule, void* solver, const Task &task, const std::clock_t & startTime, long long time_limit_in_ms){
		
	DEBUG(capsule.printVariables());
int individuallyCounted = atMostOneParamterValue +
atMostOnePredicate +
atMostOnePredicateValueArgument +
actionTyping +
predicateTyping +
precSupport +
equals +
initSupp +
goalAchiever +
nullary +
oneAction +
addEffects + 
delEffects +
frameEqual + 
frameImplies +
parameterEqualsConstraints;

	cout << "Generated Variables " << setw(10) << capsule.number_of_variables <<
		" Clauses: " << setw(10) << get_number_of_clauses() << " length " << planLength << endl;
	cout << "Number of clauses submitted to solver: " << clauseCount << " individually counded: " << individuallyCounted <<
			" equalCounted: " << (clauseCount == individuallyCounted) << endl; 

	cout << "\tFS max 1 action                 " << setw(9) << oneAction                       << " " << fixed << setprecision(6) << double(oneAction                      ) / clauseCount << endl; 
	cout << "\tFS max 1 action param value     " << setw(9) << atMostOneParamterValue          << " " << fixed << setprecision(6) << double(atMostOneParamterValue         ) / clauseCount << endl;
	cout << "\tFS max 1 predicate              " << setw(9) << atMostOnePredicate              << " " << fixed << setprecision(6) << double(atMostOnePredicate             ) / clauseCount << endl;
	cout << "\tFS max 1 predicate param value  " << setw(9) << atMostOnePredicateValueArgument << " " << fixed << setprecision(6) << double(atMostOnePredicateValueArgument) / clauseCount << endl;
	cout << "\tFS typing actions               " << setw(9) << actionTyping                    << " " << fixed << setprecision(6) << double(actionTyping                   ) / clauseCount << endl;
	cout << "\tFS typing predicates            " << setw(9) << predicateTyping                 << " " << fixed << setprecision(6) << double(predicateTyping                ) / clauseCount << endl;
	cout << "\tFS parameter (not) equals       " << setw(9) << parameterEqualsConstraints      << " " << fixed << setprecision(6) << double(parameterEqualsConstraints     ) / clauseCount << endl;
	cout << "\tFS prec met                     " << setw(9) << precSupport                     << " " << fixed << setprecision(6) << double(precSupport                    ) / clauseCount << endl;
	cout << "\tFS add effects                  " << setw(9) << addEffects                      << " " << fixed << setprecision(6) << double(addEffects                     ) / clauseCount << endl; 
	cout << "\tFS del effects                  " << setw(9) << delEffects                      << " " << fixed << setprecision(6) << double(delEffects                     ) / clauseCount << endl; 
	cout << "\tFS frame equals                 " << setw(9) << frameEqual                      << " " << fixed << setprecision(6) << double(frameEqual                     ) / clauseCount << endl;
	cout << "\tFS frame implies                " << setw(9) << frameImplies                    << " " << fixed << setprecision(6) << double(frameImplies                   ) / clauseCount << endl;
	cout << "\tFS equals (with state)          " << setw(9) << equals                          << " " << fixed << setprecision(6) << double(equals                         ) / clauseCount << endl;
	cout << "\tFS init support                 " << setw(9) << initSupp                        << " " << fixed << setprecision(6) << double(initSupp                       ) / clauseCount << endl;
	cout << "\tFS goal achievers               " << setw(9) << goalAchiever                    << " " << fixed << setprecision(6) << double(goalAchiever                   ) / clauseCount << endl; 

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



utils::ExitCode LiftedLinearSAT::solve(const Task &task, int limit, bool optimal, bool incremental, int width) {
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
	
		if (limit == -1) maxLen = 9999999; else maxLen = limit;
		void* solver;
		sat_capsule capsule;
		if (incremental){
			solver = ipasir_init();
			planLength = 0;
		}
		
		for (int i = 15; i < maxLen; i++){
			if (!incremental) {// create a new solver instance for every ACD
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
				equals = 0;
				initSupp = 0;
				nullary = 0;
				oneAction = 0; 
				goalAchiever = 0; 
				addEffects = 0;
				delEffects = 0;
				frameEqual = 0;
				frameImplies = 0;
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
