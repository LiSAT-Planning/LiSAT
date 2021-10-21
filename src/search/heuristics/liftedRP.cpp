//
// Created by Daniel Höller on 27.08.21.
//

#include "liftedRP.h"
#include <unordered_set>
#include <cassert>

using namespace std;

liftedRP::liftedRP(const Task task) {
    numActions = task.actions.size();
    numObjs = task.objects.size();
    for (auto a: task.actions) {
        maxArity = max(maxArity, (int) a.get_parameters().size());
    }

    cout << "- re-inferring type hierarchy..." << endl;
    int numTypes = task.type_names.size();
    types = new unordered_set<int>[numTypes];
    for (int obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (int i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            types[j].insert(obj);
        }
    }
    unordered_set<int> parents[numTypes];
    for (int child = 0; child < numTypes; child++) {
        for (int parent = 0; parent < numTypes; parent++) {
            if (child == parent) continue;
            if (types[child].size() < types[parent].size()) {
                bool isSubset = true;
                for (int elem: types[child]) {
                    if (types[parent].find(elem) == types[parent].end()) {
                        isSubset = false;
                        break;
                    }
                }
                if (isSubset) {
                    parents[child].insert(parent);
                }
            }
        }
    }

    // make sparse
    for (int i = 0; i < numTypes; i++) {
        for (int j = 0; j < numTypes; j++) {
            if (i == j) continue;
            for (int k = 0; k < numTypes; k++) {
                if ((i == k) || (j == k)) continue;
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(k) != parents[j].end())
                    && (parents[i].find(k) != parents[i].end())) {
                    parents[i].erase(parents[i].find(k));
                }
            }
        }
    }

    for (int i = 0; i < numTypes; i++) {
        cout << task.type_names[i] << " -> {";
        bool first = true;
        for (auto p : parents[i]) {
            if (first) {
                first = false;
            } else {
                cout << ", ";
            }
            cout << task.type_names[p];
        }
        cout << "}" << endl;
    }

    children = new unordered_set<int>[numTypes];
    ps = new unordered_set<int>[numTypes];
    toptasks = new unordered_set<int>;
    for (int i = 0; i < numTypes; i++) {
        if (parents[i].size() == 0) {
           toptasks->insert(i);
        } else {
            for (int p : parents[i]) {
                children[p].insert(i);
                ps[i].insert(p);
            }
        }
    }

    // sort obj such that objects of same parent type are adjacent
    upperTindex = new int[numTypes];
    lowerTindex = new int[numTypes];
    objToIndex = new int[numObjs];
    indexToObj = new int[numObjs];

    int r = 0;
    for (int t : *toptasks) {
        r = sortObjs(r, t);
    }

    for (int i = 0; i < task.objects.size(); i++) {
        cout << task.objects[i].getName() << " ";
    }
    cout << endl;

    for (int i = 0; i < numTypes; i++) {
        cout << task.type_names[i] << ":\t" << lowerTindex[i] << "-" << upperTindex[i] << " = {";
        for(int j = lowerTindex[i]; j <= upperTindex[i]; j++) {
            if (j > lowerTindex[i]) {
                cout << ", ";
            }
            int k = indexToObj[j];
            cout << task.objects[k].getName();
        }
        cout << "}" << endl;
    }

    cout << "- num actions " << numActions << endl;
    cout << "- num objects " << numObjs << endl;
    cout << "- max arity " << maxArity << endl;


    cout << "- building achiever lookup table" << endl;
    int numPreds = task.predicates.size();
    achievers = new vector<achiever*>[numPreds];
    for (int ia = 0; ia < task.actions.size(); ia++) {
        auto a = task.actions[ia];
        for (int ie = 0; ie < a.get_effects().size(); ie++) {
            auto eff = a.get_effects()[ie];
            assert(eff.predicate_symbol < numPreds);
            achiever* ach = new achiever;
            ach->action = ia;
            int pred = eff.predicate_symbol;
            int arity = task.predicates[pred].getArity();
            ach->params = new int[arity];
            for (int ip = 0; ip < eff.arguments.size(); ip++) {
                auto args = eff.arguments[ip];
                assert(!args.constant);
                ach->params[ip] = args.index;
            }

            achievers[pred].push_back(ach);
        }
    }

}

int liftedRP::compute_heuristic(const DBState &s, const Task &task) {
    IloEnv env;
    IloNumVarArray v(env);
    IloModel model(env);

    // create variables representing lifted relaxed plan
    // a1 p1_1 p1_2 ... p1_k a2 p2_1 p2_2 ... p2_k ... an pn_1 pn_2 ... pn_k
    for (int i = 0; i < planLength; i++) {
        v.add(IloNumVar(env, 0, numActions, IloNumVar::Int));
        string vName = "a" + to_string(i);
        v[v.getSize() - 1].setName(vName.c_str());
        for (int j = 0; j < maxArity; j++) {
            v.add(IloNumVar(env, 0, numObjs, IloNumVar::Int));
            string vName2 = "p" + to_string(i);
            vName2 += "_" + to_string(j);
            v[v.getSize() - 1].setName(vName2.c_str());
            model.add(v[actionID(i)] * largeC >= v[paramID(i, j)]); // if action schema is 0, the parameter also need to be 0
        }
    }

    // create main optimization function
    IloNumExpr mainExp(env);
    for (int i = 0; i < planLength; i++) {
        v.add(IloNumVar(env, 0, 1, IloNumVar::Bool));
        string vName = "a_opt" + to_string(i);
        v[v.getSize() - 1].setName(vName.c_str());
        model.add(v[v.getSize() - 1] * largeC >= v[actionID(i)]);
        mainExp = mainExp + (v[v.getSize() - 1]);
    }

    // enforce typing of action parameters
    for (int i = 0; i < planLength; i++) {
        int iSchema = actionID(i);
        for (int j = 1; j <= numActions; j++) { // actions with initial index 1 (!)
            cout << task.actions[j - 1].get_name() << endl;
            IloConstraint schemaEq = (v[iSchema] == j);
            auto params = task.actions[j - 1].get_parameters();
            for (int l = 0; l < params.size(); l++) {
                cout << "- " << task.type_names[params[l].type] << ": ";
                int lower = lowerTindex[params[l].type];
                int upper = upperTindex[params[l].type];
                for (int m = lower; m <= upper; m++) {
                    cout << task.objects[indexToObj[m]].getName() << " ";
                }
                cout << endl;
                int iP = paramID(i, l);
                IloIfThen lowerVarRange(env, schemaEq, (v[iP] - 1) > (lower - 1));
                IloIfThen upperVarRange(env, schemaEq, (v[iP] - 1) < (upper + 1));
                model.add(lowerVarRange);
                model.add(upperVarRange);
            }
        }
    }

    // add goal condition
    for (int i = 0; i < planLength; i++) {
        for (int j = 0; j < task.goal.goal.size(); j++) {

        }
    }
    //model.add(v[0] == 3);

    model.add(IloMinimize(env, mainExp));
    IloCplex cplex(model);
    cplex.exportModel("/home/dh/Schreibtisch/LiftedDelRel/test.lp");
    cplex.setParam(IloCplex::Param::Threads, 1);

    // no output
    // cplex.setOut(env.getNullStream());
    // cplex.setWarning(env.getNullStream());

    int res = -1;
    if (cplex.solve()) {
        res = round(cplex.getObjValue()); // todo: use ceil for LP
        //cout << "a" << "=" << round(cplex.getValue(v[0])) << endl;
        //cout << "b" << "=" << round(cplex.getValue(v[1])) << endl;

        for (int i = 0; i < planLength; i++) {
            int x = round(cplex.getValue(v[actionID(i)])) - 1;
            if (x >= 0) {
                cout << "a" << i << "=" << task.actions[x].get_name();
                for (int j = 0; j < maxArity; j++) {
                    int x = round(cplex.getValue(v[paramID(i, j)])) - 1;
                    if (x >= 0) {
                        cout << " p" << j << "=" << task.objects[indexToObj[x]].getName();
                    }
                }
                cout << endl;
            }
        }
    }
    cout << "res: " << res << endl;
    exit(0);
    return 0;
}

int liftedRP::sortObjs(int index, int type) {
    lowerTindex[type] = index;
    for (int st : children[type]) {
        index = sortObjs(index, st);
    }
    for(int o : types[type]) {
        if (done.find(o) == done.end()) {
            objToIndex[o] = index;
            indexToObj[index] = o;
            index++;
            done.insert(o);
        }
    }
    upperTindex[type] = index - 1;
    return index;
}

int liftedRP::actionID(int i) {
    return (maxArity + 1) * i;
}

int liftedRP::paramID(int i, int j) {
    return (maxArity + 1) * i + (j + 1);
}
