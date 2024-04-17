#include "options.h"
#include "parser.h"
#include "task.h"

#ifndef CMAKE_NO_SAT
#include "sat/lifted_sat.h"
#include "sat/lifted_linear_sat.h"
#include "sat/partially_grounded_sat.h"
#endif


#include "heuristics/heuristic.h"
#include "heuristics/heuristic_factory.h"
#include "search_engines/search.h"
#include "search_engines/search_factory.h"
#include "successor_generators/successor_generator.h"
#include "successor_generators/successor_generator_factory.h"

#include <iostream>
#include <memory>

using namespace std;
using namespace utils;

int main(int argc, char *argv[]) {
    cout << "Initializing planner" << endl;

    Options opt(argc, argv);

    ifstream task_file(opt.get_filename());
    if (!task_file) {
        cerr << "Error opening the task file: " << opt.get_filename() << endl;
        exit(-1);
    }

    cout << "Reading task description file." << endl;
    cin.rdbuf(task_file.rdbuf());

    // Parse file
    string domain_name, task_name;
    cin >> domain_name >> task_name;
    Task task(domain_name, task_name);
    cout << task.get_domain_name() << " " << task.get_task_name() << endl;

    bool parsed = parse(task, task_file);
    if (!parsed) {
        cerr << "Parser failed." << endl;
        exit(-1);
    }

    cout << "IMPORTANT: Assuming that negative effects are always listed first. "
            "(This is guaranteed by the default translator.)" << endl;


	if (opt.get_search_engine() == "sat"){
#ifndef CMAKE_NO_SAT
        std::unique_ptr<LiftedSAT> liftedSAT(new LiftedSAT(task));
    	try {
    	    auto exitcode = liftedSAT->solve(task,opt.get_planLength(), opt.get_optimal(), opt.get_incremental());
    	    utils::report_exit_code_reentrant(exitcode);
    	    return static_cast<int>(exitcode);
    	}
    	catch (const bad_alloc& ex) {
    	    //search->print_statistics();
    	    exit_with(utils::ExitCode::SEARCH_OUT_OF_MEMORY);
    	}
#else
		cout << "Planner was compiled without SAT solver support. Exiting." << endl;
#endif
	} else if (opt.get_search_engine() == "linear"){
#ifndef CMAKE_NO_SAT
        std::unique_ptr<LiftedLinearSAT> liftedSAT(new LiftedLinearSAT(task,opt.get_structure()));
    	try {
    	    auto exitcode = liftedSAT->solve(task,opt.get_planLength(), opt.get_optimal(), opt.get_incremental(), opt.get_width(), opt.get_timelimit());
    	    utils::report_exit_code_reentrant(exitcode);
    	    return static_cast<int>(exitcode);
    	}
    	catch (const bad_alloc& ex) {
    	    //search->print_statistics();
    	    exit_with(utils::ExitCode::SEARCH_OUT_OF_MEMORY);
    	}
#else
		cout << "Planner was compiled without SAT solver support. Exiting." << endl;
#endif
	} else if (opt.get_search_engine() == "pgsat"){
#ifndef CMAKE_NO_SAT
        std::unique_ptr<PartiallyGroundedSAT> liftedSAT(new PartiallyGroundedSAT(task));
    	try {
    	    auto exitcode = liftedSAT->solve(task,opt.get_planLength(), opt.get_optimal(), opt.get_incremental());
    	    utils::report_exit_code_reentrant(exitcode);
    	    return static_cast<int>(exitcode);
    	}
    	catch (const bad_alloc& ex) {
    	    //search->print_statistics();
    	    exit_with(utils::ExitCode::SEARCH_OUT_OF_MEMORY);
    	}
#else
		cout << "Planner was compiled without SAT solver support. Exiting." << endl;
#endif
	} else {
    	// Let's create a couple unique_ptr's that deal with mem allocation themselves
    	std::unique_ptr<SearchBase> search(SearchFactory::create(opt.get_search_engine(), opt.get_state_representation()));
    	std::unique_ptr<Heuristic> heuristic(HeuristicFactory::create(opt, task));
    	std::unique_ptr<SuccessorGenerator> sgen(SuccessorGeneratorFactory::create(opt.get_successor_generator(),
    	                                                                           opt.get_seed(),
    	                                                                           task));

    	// Start search
    	if (task.is_trivially_unsolvable()) {
    	    cout << "Problem goal was statically determined to be unsatisfiable." << endl;
    	    exit_with(utils::ExitCode::SEARCH_UNSOLVABLE);
    	}

    	try {
    	    auto exitcode = search->search(task, *sgen, *heuristic);
    	    search->print_statistics();
    	    utils::report_exit_code_reentrant(exitcode);
    	    return static_cast<int>(exitcode);
    	}
    	catch (const bad_alloc& ex) {
    	    //search->print_statistics();
    	    exit_with(utils::ExitCode::SEARCH_OUT_OF_MEMORY);
    	}
	}

}
