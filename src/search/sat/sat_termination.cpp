#include "sat_termination.h"
#include <thread>
#include <chrono>
#include <cstdlib>
#include <iostream>
#ifndef CMAKE_NO_TERMINATE
#include "kissat.h"
#endif

void kissat_termination_fuction(void* solver, double terminationTime, bool* stopFlag){
#ifndef CMAKE_NO_TERMINATE
	while (true){
		using namespace std::chrono_literals;
		// sleep for 0.1 second
		std::this_thread::sleep_for(100ms);
	
		// check whether we need to terminate
		if (*stopFlag) return;

		// determine current time
		std::clock_t current_time = std::clock();
		double current_time_in_ms = 1000.0 * (current_time) / CLOCKS_PER_SEC;

		// check whether we need to stop the SAT solver
		if (current_time_in_ms > terminationTime){
			std::cout << "SAT solver has exceeded its time limit ... I'm stopping it" << std::endl;
			kissat_terminate((kissat*)solver);
		}
	}
#endif
}


bool* ensure_termination_after(void* solver, long long limit_in_miliseconds){
	bool* stopFlag = (bool*) malloc(sizeof(bool));
	*stopFlag = false;

#ifndef CMAKE_NO_TERMINATE
	std::clock_t solver_start = std::clock();
	double solver_end_time = 1000.0 * (solver_start) / CLOCKS_PER_SEC + limit_in_miliseconds;
	
	std::thread time_limit_thread(&kissat_termination_fuction, solver, solver_end_time, stopFlag);
	time_limit_thread.detach();
#endif

	return stopFlag;
}


void stop_termination_checking(bool* stopFlag){
	*stopFlag = true; // tell the termination checker to terminate itself
	free(stopFlag);
}
