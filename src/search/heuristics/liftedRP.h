//
// Created by dh on 27.08.21.
//

#ifndef SEARCH_LIFTEDRP_H
#define SEARCH_LIFTEDRP_H

#include <ilcplex/ilocplex.h>
#include <vector>
#include <unordered_set>
#include "heuristic.h"

struct Achiever {
    // the precondition "pred p0 p1 p3"
    // can be achieved using the following action
    int action = -1;
    int effect = -1; // so far only used for debugging
    // let the following be "v1 v3 v0", these are (a subset of) parameters of the action
	std::vector<int> params;
    // then, to achieve the predicate given above, the following must hold
    // v1 == p0, v3 == p1, v0 == p3
} ;

struct ActionPrecAchiever {
    // it stores for a **single action precondition** which other action can achieve it
	std::vector<Achiever*> achievers;
    // todo: add which s0 literals can fulfill this precondition
};

struct ActionPrecAchievers {
    // for a single action, it stores for **each precondition** which other action can achieve it
	std::vector<ActionPrecAchiever*> precAchievers;
};

class liftedRP : public Heuristic {
private:
    const int largeC = 100000;
    int planLength = 10;
    int maxArity = -1;

    int numObjs = -1;
    int numActions = -1;

    int* lowerTindex;
    int* upperTindex;
    int* objToIndex;
    int* indexToObj;

	std::unordered_set<int>* types;

    std::unordered_set<int>* children;
    std::unordered_set<int>* ps;
    std::unordered_set<int>* toptasks;
    std::unordered_set<int> done;

    std::vector<ActionPrecAchievers*> achievers;
    ActionPrecAchievers* goalAchievers;
    int sortObjs(int index, int type);
public:

    liftedRP(const Task task);

    int compute_heuristic(const DBState & s, const Task& task) final;
	int compute_heuristic_sat(const DBState &s, const Task &task);

    int actionID(int i);

    int paramID(int i, int j);
};


#endif //SEARCH_LIFTEDRP_H
