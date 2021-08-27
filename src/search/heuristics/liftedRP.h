//
// Created by dh on 27.08.21.
//

#ifndef SEARCH_LIFTEDRP_H
#define SEARCH_LIFTEDRP_H

#include <ilcplex/ilocplex.h>
#include "heuristic.h"

class liftedRP : public Heuristic{
public:
    liftedRP(const Task task);

    int compute_heuristic(const DBState & s, const Task& task) final;
};


#endif //SEARCH_LIFTEDRP_H
