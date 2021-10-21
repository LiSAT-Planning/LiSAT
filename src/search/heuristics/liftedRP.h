//
// Created by dh on 27.08.21.
//

#ifndef SEARCH_LIFTEDRP_H
#define SEARCH_LIFTEDRP_H

#include <ilcplex/ilocplex.h>
#include "heuristic.h"

struct achiever {
    // the predicate "pred p0 p1 p3"
    // can be achieved using the following action
    int action = 0;
    // let the following be "v1 v3 v0", these are (a subset of) parameters of the action
    int* params;
    // then, to achieve the predicate given above, the following must hold
    // v1 == p0, v3 == p1, v0 == p3
} ;

class liftedRP : public Heuristic{
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

    vector<achiever*>* achievers;
    int sortObjs(int index, int type);
public:

    liftedRP(const Task task);

    int compute_heuristic(const DBState & s, const Task& task) final;

    int actionID(int i);

    int paramID(int i, int j);
};


#endif //SEARCH_LIFTEDRP_H
