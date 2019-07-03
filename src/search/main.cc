#include <iostream>
#include <vector>
#include <fstream>

#include "parser.h"
#include "task.h"
#include "search.h"
#include "successor_generators/successor_generator.h"

using namespace std;

int main(int argc, char *argv[]) {
    cout << "Initializing planner" << endl;

    if (argc != 3) {
        cerr << "Usage: ./planner [TASK INPUT] [SUCCESSOR GENERATOR METHOD]" << endl;
        exit(-1);
    }

    // Remember to change it when it is not debugging anymore
    cout << argv[1] << endl;
    ifstream in(argv[1]);
    if (!in) {
        cerr << "Error opening the task file." << endl;
        exit(-1);
    }

    cout << "Reading task description file." << endl;
    cin.rdbuf(in.rdbuf());

    // Parse file
    string domain_name, task_name;
    cin >> domain_name >> task_name;
    Task task(domain_name, task_name);
    cout << task.getDomainName() << " " << task.getTaskName() << endl;

    bool parsed = parse(task, in);
    if (!parsed) {
        cerr << "Parser failed." << endl;
        return -1;
    }

    Search search;
    SuccessorGenerator successorGenerator;
    search.search(task, successorGenerator);

    /*
     * TODO
     * We probably want to create some more refined data structures. For example, it would be nice to have an easy way
     * to get all objects of a given type. An unordered map/set might suffice for this example.  For other attributes,
     * this might also be interesting.  Maybe in the future we can do it while parsing.
     *
     */

    return 0;
}