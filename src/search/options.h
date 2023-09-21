#ifndef SEARCH_OPTIONS_H
#define SEARCH_OPTIONS_H

#include <iostream>

#include <boost/program_options.hpp>

namespace po = boost::program_options;

class Options {
    std::string filename;
    std::string generator;
    std::string search_engine;
    std::string evaluator;
    std::string state_representation;
    std::string datalog_file;
    unsigned seed;
	int planLength;
	int width;
	bool optimal;
	bool incremental;

public:
    Options(int argc, char** argv) {
        po::options_description description("Allowed options");
        description.add_options()
            ("filename,f", po::value<std::string>()->default_value("output.lifted"), "Lifted task file name.")
            ("help,h", "Display this help message.")
            ("seed", po::value<unsigned>()->default_value(1), "Random seed.")
            ("evaluator,e", po::value<std::string>()->default_value("goalcount"), "Heuristic evaluator.")
            ("generator,g", po::value<std::string>()->default_value("yannakakis"), "Successor generator method.")
            ("search,s", po::value<std::string>()->required(), "Search engine.")
            ("state-representation,r", po::value<std::string>()->default_value("sparse"), "State representation.")
            ("datalog-file", po::value<std::string>()->default_value("FilePathUndefined"), "Datalog model file.")
            ("planLength,l", po::value<int>()->default_value(-1), "Plan length for the SAT encoding. If it is -1, then the satisficing solver will run in portfolio mode.")
            ("width,w", po::value<int>()->default_value(10), "Number of predicate slots in linear encoding")
            ("optimal,o", "Run the SAT planner in optimal mode")
            ("incremental,i", "Run the SAT planner in incremenal mode. ATTENTION: this is not supported by all SAT solvers")
            ;

        po::variables_map vm;

        try {
            po::store(po::command_line_parser(argc, argv).options(description).run(), vm);

            if (vm.count("help")) {
                std::cout << description << "\n";
                exit(0);
            }
            po::notify(vm);
        } catch(const std::exception& ex) {
            std::cout << "Error with command-line options:" << ex.what() << std::endl;
            std::cout << std::endl << description << std::endl;
            exit(1);
        }

        filename = vm["filename"].as<std::string>();
        generator = vm["generator"].as<std::string>();
        evaluator = vm["evaluator"].as<std::string>();
        search_engine = vm["search"].as<std::string>();
        state_representation = vm["state-representation"].as<std::string>();
        datalog_file = vm["datalog-file"].as<std::string>();
        seed = vm["seed"].as<unsigned>();
        planLength = vm["planLength"].as<int>();
        width = vm["width"].as<int>();
        optimal = vm.count("optimal");
        incremental = vm.count("incremental");
    }

    const std::string &get_filename() const {
        return filename;
    }

    const std::string &get_successor_generator() const {
        return generator;
    }

    const std::string &get_search_engine() const {
        return search_engine;
    }

    const std::string &get_evaluator() const {
        return evaluator;
    }

    const std::string &get_state_representation() const {
        return state_representation;
    }

    const std::string &get_datalog_file() const {
        return datalog_file;
    }

    unsigned get_seed() const {
        return seed;
    }

    int get_planLength() const {
        return planLength;
    }

	int get_width() const {
        return width;
    }

    unsigned int get_optimal() const {
        return optimal;
    }

    unsigned int get_incremental() const {
        return incremental;
    }


};

#endif //SEARCH_OPTIONS_H
