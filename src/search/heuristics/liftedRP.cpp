//
// Created by dh on 27.08.21.
//

#include "liftedRP.h"

int liftedRP::compute_heuristic(const DBState &s, const Task &task) {

    cout << "I am here!" << endl;

    IloEnv lenv;
    IloNumVarArray v(lenv);
    IloModel model(lenv);

    v.add(IloNumVar(lenv, 0, 1, IloNumVar::Bool));
    IloNumExpr mainExp(lenv);
    mainExp = mainExp + (v[0]);
    model.add(IloMinimize(lenv, mainExp));
    IloCplex cplex(model);
    cplex.setParam(IloCplex::Param::Threads, 1);

    // no output
    // cplex.setOut(lenv.getNullStream());
    // cplex.setWarning(lenv.getNullStream());

    int res = -1;
    if (cplex.solve()) {
        res = round(cplex.getObjValue()); // todo: use ceil for LP
        double d = cplex.getValue(v[0]);
    }
    exit(0);
    return 0;
}

liftedRP::liftedRP(const Task task) {

}
