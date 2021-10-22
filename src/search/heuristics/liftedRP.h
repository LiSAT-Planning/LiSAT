//
// Created by dh on 27.08.21.
//

#ifndef SEARCH_LIFTEDRP_H
#define SEARCH_LIFTEDRP_H

#include <ilcplex/ilocplex.h>
#include "heuristic.h"

struct Achiever {
    // the precondition "pred p0 p1 p3"
    // can be achieved using the following action
    int action = -1;
    int effect = -1; // so far only used for debugging
    // let the following be "v1 v3 v0", these are (a subset of) parameters of the action
    vector<int> params;
    // then, to achieve the predicate given above, the following must hold
    // v1 == p0, v3 == p1, v0 == p3
} ;

struct ActionPrecAchiever {
    // it stores for a **single action precondition** which other action can achieve it
    vector<Achiever*> achievers;
    // todo: add which s0 literals can fulfill this precondition
};

struct ActionPrecAchievers {
    // for a single action, it stores for **each precondition** which other action can achieve it
    vector<ActionPrecAchiever*> precAchievers;
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

    unordered_set<int>* types;

    unordered_set<int>* children;
    unordered_set<int>* ps;
    unordered_set<int>* toptasks;
    unordered_set<int> done;

    vector<ActionPrecAchievers*> achievers;
    ActionPrecAchievers* goalAchievers;
    int sortObjs(int index, int type);
public:

    liftedRP(const Task task);

    int compute_heuristic(const DBState & s, const Task& task) final;

    int actionID(int i);

    int paramID(int i, int j);
};


#endif //SEARCH_LIFTEDRP_H
