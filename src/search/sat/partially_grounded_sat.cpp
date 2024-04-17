#include "partially_grounded_sat.h"
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

PartiallyGroundedSAT::PartiallyGroundedSAT(const Task & task) {
	int numActions = task.actions.size();
    int numObjs = task.objects.size();
	cout << "Extracting FAM groups using [Fiser, AAAI 2020] ...";


	cout << " done" << endl;
}

utils::ExitCode PartiallyGroundedSAT::solve(const Task &task, int limit, bool optimal, bool incremental) {
	cout << "Not yet implemented!" << endl;
	return utils::ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
}


