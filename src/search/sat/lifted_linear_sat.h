//
// Created by dh on 27.08.21.
//

#ifndef SEARCH_LIFTED_LINEAR_SAT_H
#define SEARCH_LIFTED_LINEAR_SAT_H

#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <ctime>
#include "sat_encoder.h"
#include "../utils/system.h"
#include "../task.h"

struct LAchiever {
    // the precondition "pred p0 p1 p3"
    // can be achieved using the following action
    int action = -1;
    int effect = -1; // so far only used for debugging
    // let the following be "v1 v3 v0", these are (a subset of) parameters of the action
	std::vector<int> params;
    // then, to achieve the predicate given above, the following must hold
    // v1 == p0, v3 == p1, v0 == p3
} ;

struct LActionPrecAchiever {
    // it stores for a **single action precondition** which other action can achieve it
	std::vector<LAchiever*> achievers;
	std::vector<LAchiever*> destroyers;
    // todo: add which s0 literals can fulfill this precondition
};

struct LActionPrecAchievers {
    // for a single action, it stores for **each precondition** which other action can achieve it
	std::vector<LActionPrecAchiever*> precAchievers;
    std::map<int, LActionPrecAchiever*> posNullaryPrecAchievers;
    std::map<int, LActionPrecAchiever*> negNullaryPrecAchievers;
};

class LiftedLinearSAT{
private:
	std::map<std::pair<int, int>, bool> needToType;
    const int largeC = 100000;
    int planLength = 8;
    int maxActionArity = -1;
    int maxPredicateArity = -1;
    int maxPrec = -1;

	int maximumTimeStepNetChange;
	int goalNeededWidth;

	int numObjs = -1;
    int numActions = -1;
	bool foundOrdinaryPredicate;

    int* lowerTindex;
    int* upperTindex;
    int* objToIndex;
    int* indexToObj;

	std::unordered_set<int>*	toptypes;

	std::unordered_set<int>* types;

    std::unordered_set<int>* children;
    std::unordered_set<int>* ps;
    std::unordered_set<int>* toptasks;
    std::unordered_set<int> done;

    std::vector<LActionPrecAchievers*> achievers;
    LActionPrecAchievers* goalAchievers;

	std::vector<std::unordered_set<int>*> setPosNullaryPrec;
    std::vector<std::unordered_set<int>*> setNegNullaryPrec;
    std::vector<std::unordered_set<int>*> setPosNullaryEff;
    std::vector<std::unordered_set<int>*> setNegNullaryEff;

	std::unordered_map<int,std::vector<int>> nullaryAchiever;
	std::unordered_map<int,std::vector<int>> nullaryDestroyer;

    int sortObjs(int index, int type);
public:

    LiftedLinearSAT(const Task& task);
	utils::ExitCode solve(const Task& task, int limit, bool optimal, bool incremental, int width, int timelimitInSeconds);
	void generate_predicate_slot_layer(const Task &task, void* solver, sat_capsule & capsule, int width, int time);
	std::vector<std::vector<std::vector<std::vector<int>>>> generate_action_state_equality(const Task &task, void* solver, sat_capsule & capsule, int width, int actionTime, int stateTime);
	void generate_goal_assertion(const Task &task, void* solver, sat_capsule & capsule, int width, int time);
	void generate_formula(const Task &task, void* solver, sat_capsule & capsule, int width, bool optimal);
	bool callSolver(sat_capsule & capsule, void* solver, const Task &task, int width, const std::clock_t & startTime,long long time_limit_in_ms = -1);
	bool atom_not_satisfied(const DBState &s, const AtomicGoal &atomicGoal) const;

    int actionID(int i);

    int paramID(int i, int j);
};


typedef size_t tSize;

#endif //SEARCH_LIFTEDRP_H
