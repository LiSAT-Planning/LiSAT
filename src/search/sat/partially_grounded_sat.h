#ifndef SEARCH_PARTIALLY_GROUNDED_SAT_H
#define SEARCH_PARTIALLY_GROUNDED_SAT_H

#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <ctime>
#include "sat_encoder.h"
#include "../utils/system.h"
#include "../task.h"

class PartiallyGroundedSAT{
private:
public:
    PartiallyGroundedSAT(const Task& task);
	utils::ExitCode solve(const Task& task, int limit, bool optimal, bool incremental);
};


typedef size_t tSize;

#endif //SEARCH_LIFTEDRP_H
