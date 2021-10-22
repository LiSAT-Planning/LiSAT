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

    // create data structure for nullary precs/effects
    for (int a = 0; a < task.actions.size(); a++) {
        setPosNullaryPrec.push_back(new unordered_set<int>);
        setNegNullaryPrec.push_back(new unordered_set<int>);
        setPosNullaryEff.push_back(new unordered_set<int>);
        setNegNullaryEff.push_back(new unordered_set<int>);

        auto posPrec = task.actions[a].get_positive_nullary_precond();
        for (int f = 0; f < posPrec.size(); f++){
            if (posPrec[f]){
                setPosNullaryPrec[a]->insert(f);
            }
        }
        auto negPrec = task.actions[a].get_negative_nullary_precond();
        for (int f = 0; f < negPrec.size(); f++){
            if (negPrec[f]){
                setNegNullaryPrec[a]->insert(f);
            }
        }
        auto posEff = task.actions[a].get_positive_nullary_effects();
        for (int f = 0; f < posEff.size(); f++){
            if (posEff[f]){
                setPosNullaryEff[a]->insert(f);
            }
        }
        auto negEff = task.actions[a].get_negative_nullary_effects();
        for (int f = 0; f < negEff.size(); f++){
            if (negEff[f]){
                setNegNullaryEff[a]->insert(f);
            }
        }
    }

    cout << "- building achiever lookup table" << endl;
    // !!! this code assumes the non-sparse (i.e. transitively closed) typing !!!
    for (int iAction = 0; iAction < task.actions.size(); iAction++) {
        auto a = task.actions[iAction];
        achievers.push_back(new ActionPrecAchievers);
        const auto precs = task.actions[iAction].get_precondition();
        for (int iPrec = 0; iPrec < precs.size(); iPrec++) {
            achievers[iAction]->precAchievers.push_back(new ActionPrecAchiever);
            const auto prec = precs[iPrec];
            // check for this single prec which other actions can achieve it. need to check
            // - predicate
            // - typing of the specific parameters
            for (int iPosAch = 0; iPosAch < task.actions.size(); iPosAch++) {
                auto posAchAction = task.actions[iPosAch];
                for (int ie = 0; ie < posAchAction.get_effects().size(); ie++) {
                    auto eff = posAchAction.get_effects()[ie];
                    if ((eff.predicate_symbol == prec.predicate_symbol) && (eff.negated == prec.negated)){
                        /* ** check typing **
                         * what shall be excluded is that the predicate is defined on a
                         * parent type, but the effect and the precondition are siblings
                         *
                         * example: In a transport domain, a locatable object may be a
                         * transporter or a package. The "at" predicate may be defined
                         * on "locatable"s. However, the "at" predicate of a package
                         * cannot be fulfilled with a drive action.
                         */
                        bool typesCompatible = true;
                        for (int iArg = 0; iArg < prec.arguments.size(); iArg++) {
                            int varP = prec.arguments[iArg].index;
                            int typeP = a.get_parameters()[varP].type;
                            int varE = eff.arguments[iArg].index;
                            int typeE = posAchAction.get_parameters()[varE].type;
                            if (typeP == typeE) continue;
                            if (parents[typeP].find(typeE) != parents[typeP].end()) continue;
                            if (parents[typeE].find(typeP) != parents[typeE].end()) continue;
                            typesCompatible = false;
                            break;
                        }
                        if (typesCompatible) {
                            Achiever *ach = new Achiever;
                            ach->action = iPosAch;
                            ach->effect = ie;
                            for (int ip = 0; ip < eff.arguments.size(); ip++) {
                                auto args = eff.arguments[ip];
                                assert(!args.constant);
                                ach->params.push_back(args.index);
                            }
                            achievers[iAction]->precAchievers[iPrec]->achievers.push_back(ach);
                        }
                    }
                }
            }
        }
        for (int posPrec : *setPosNullaryPrec[iAction]) {
            achievers[iAction]->posNullaryPrecAchievers[posPrec] = new ActionPrecAchiever;
            for (int iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
                auto possAchAction = task.actions[iPossibleAch];
                if (possAchAction.get_positive_nullary_effects()[posPrec]) {
                    Achiever *ach = new Achiever;
                    ach->action = iPossibleAch;
                    achievers[iAction]->posNullaryPrecAchievers[posPrec]->achievers.push_back(ach);
                }
            }
        }
        for (int negPrec : *setNegNullaryPrec[iAction]) {
            achievers[iAction]->negNullaryPrecAchievers[negPrec] = new ActionPrecAchiever;
            for (int iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
                auto possAchAction = task.actions[iPossibleAch];
                if (possAchAction.get_negative_nullary_effects()[negPrec]) {
                    Achiever *ach = new Achiever;
                    ach->action = iPossibleAch;
                    achievers[iAction]->negNullaryPrecAchievers[negPrec]->achievers.push_back(ach);
                }
            }
        }
    }

    // same for goals
    goalAchievers = new ActionPrecAchievers;
    for (int iGoal = 0; iGoal < task.goal.goal.size(); iGoal++) {
        AtomicGoal goal = task.goal.goal[iGoal];
        goalAchievers->precAchievers.push_back(new ActionPrecAchiever);
        for (int iPosAch = 0; iPosAch < task.actions.size(); iPosAch++) {
            auto posAchAction = task.actions[iPosAch];
            for (int ie = 0; ie < posAchAction.get_effects().size(); ie++) {
                auto eff = posAchAction.get_effects()[ie];
                if ((eff.predicate_symbol == goal.predicate) && (eff.negated == goal.negated)) {
                    bool typesCompatible = true;
                    for (int iArg = 0; iArg < goal.args.size(); iArg++) {
                        int goalObj = goal.args[iArg];
                        int varE = eff.arguments[iArg].index;
                        int typeE = posAchAction.get_parameters()[varE].type;
                        if (types[typeE].find(goalObj) == types[typeE].end()) {
                            typesCompatible = false;
                            break;
                        }
                    }
                    if (typesCompatible) {
                        Achiever *ach = new Achiever;
                        ach->action = iPosAch;
                        ach->effect = ie;
                        for (int ip = 0; ip < eff.arguments.size(); ip++) {
                            auto args = eff.arguments[ip];
                            ach->params.push_back(args.index);
                        }
                        goalAchievers->precAchievers[iGoal]->achievers.push_back(ach);
                    }
                }
            }
        }
    }
    for (int posGoal : task.goal.positive_nullary_goals) {
        goalAchievers->posNullaryPrecAchievers[posGoal] = new ActionPrecAchiever;
        for (int iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
            auto possAchAction = task.actions[iPossibleAch];
            if (possAchAction.get_positive_nullary_effects()[posGoal]) {
                Achiever *ach = new Achiever;
                ach->action = iPossibleAch;
                goalAchievers->posNullaryPrecAchievers[posGoal]->achievers.push_back(ach);
            }
        }
    }
    for (int negGoal : task.goal.negative_nullary_goals) {
        goalAchievers->negNullaryPrecAchievers[negGoal] = new ActionPrecAchiever;
        for (int iPossibleAch = 0; iPossibleAch < task.actions.size(); iPossibleAch++) {
            auto possAchAction = task.actions[iPossibleAch];
            if (possAchAction.get_negative_nullary_effects()[negGoal]) {
                Achiever *ach = new Achiever;
                ach->action = iPossibleAch;
                goalAchievers->negNullaryPrecAchievers[negGoal]->achievers.push_back(ach);
            }
        }
    }

    cout << "found achievers:" << endl;
    for (int iAction = 0; iAction < task.actions.size(); iAction++) {
        cout << "- action '" << task.actions[iAction].get_name() << "'";
        auto precs = task.actions[iAction].get_precondition();
        int numPrecs = precs.size() + setPosNullaryPrec[iAction]->size() + setNegNullaryPrec[iAction]->size();
        cout << ", which has " << numPrecs << " preconditions" << endl;
        for (int iPrec = 0; iPrec < precs.size(); iPrec++) {
            cout << "  - prec: ";
            if (precs[iPrec].negated) {
                cout << "not ";
            }
            cout << "'" << task.predicates[precs[iPrec].predicate_symbol].getName() << "' achieved by";
            auto achs = achievers[iAction]->precAchievers[iPrec]->achievers;
            for (int iAchiever = 0; iAchiever < achs.size(); iAchiever++) {
                auto achieverAction = task.actions[achs[iAchiever]->action];
                cout << endl << "    - '" << achieverAction.get_name() << "'";
                cout << " eff: " << achs[iAchiever]->effect;
                cout << " pred: '" << task.predicates[achieverAction.get_effects()[achs[iAchiever]->effect].predicate_symbol].getName() << "'";
            }
            if (achs.empty()) {cout << " s0 only.";}
            cout << endl;
        }
        for (int iPrec : *setPosNullaryPrec[iAction]) {
            cout << "  - prec: nullary" << iPrec;
            auto achs = achievers[iAction]->posNullaryPrecAchievers[iAction][iPrec].achievers;
            for (auto ach : achs) {
                auto achieverAction = task.actions[ach->action];
                cout << endl << "    - '" << achieverAction.get_name() << "'";
            }
        }
        for (int iPrec : *setNegNullaryPrec[iAction]) {
            cout << "  - prec: not nullary" << iPrec;
            auto achs = achievers[iAction]->negNullaryPrecAchievers[iAction][iPrec].achievers;
            for (auto ach : achs) {
                auto achieverAction = task.actions[ach->action];
                cout << endl << "    - '" << achieverAction.get_name() << "'";
            }
        }
    }

    cout << "goal achievers:" << endl;
    for (int iGoal = 0; iGoal < task.goal.goal.size(); iGoal++) {
        cout << "- goal ";
        if (task.goal.goal[iGoal].negated) {
            cout << "not ";
        }
        cout << "'" << task.predicates[task.goal.goal[iGoal].predicate].getName() << "'";
        for (int iAchiever = 0; iAchiever < goalAchievers->precAchievers[iGoal]->achievers.size(); iAchiever++) {
            auto ach = goalAchievers->precAchievers[iGoal]->achievers[iAchiever];
            auto achieverAction = task.actions[ach->action];
            cout << endl << "    - '" << achieverAction.get_name() << "'";
            cout << " eff: " << ach->effect;
            cout << " pred: '" << task.predicates[achieverAction.get_effects()[ach->effect].predicate_symbol].getName()
                 << "'";
        }
        if (goalAchievers->precAchievers[iGoal]->achievers.empty()) { cout << " s0 only."; }
        cout << endl;
    }
    for (int g : task.goal.positive_nullary_goals) {
        cout << "  - prec: nullary" << g;
        auto achs = goalAchievers->posNullaryPrecAchievers[g]->achievers;
        for (auto ach : achs) {
            auto achieverAction = task.actions[ach->action];
            cout << endl << "    - '" << achieverAction.get_name() << "'";
        }
    }
    for (int g : task.goal.negative_nullary_goals) {
        cout << "  - prec: not nullary" << g;
        auto achs = goalAchievers->negNullaryPrecAchievers[g]->achievers;
        for (auto ach : achs) {
            auto achieverAction = task.actions[ach->action];
            cout << endl << "    - '" << achieverAction.get_name() << "'";
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

    for (int i = 0; i < task.predicates.size(); i++) {
        cout << i << " " << task.predicates[i].getName() << endl;
    }

    cout << endl << "Initial state (static):" << endl;
    for (int i = 0; i < task.get_static_info().get_relations().size(); i++) {
        auto rel = task.get_static_info().get_relations()[i];
        auto tuple = task.get_static_info().get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            cout << "(" << task.predicates[task.get_static_info().get_relations()[i].predicate_symbol].getName();
            for (int obj: groundA) {
                cout << " " << task.objects[obj].getName();
            }
            cout <<")" << endl;
        }
    }

    cout << endl << "Initial state (non-static):" << endl;
    for (int i = 0; i < task.initial_state.get_relations().size(); i++) {
        auto rel = task.initial_state.get_relations()[i];
        auto tuple = task.initial_state.get_tuples_of_relation(i);
        for (vector<int> groundA: tuple) {
            cout << "(" << task.predicates[task.initial_state.get_relations()[i].predicate_symbol].getName();
            for (int obj: groundA) {
                cout << " " << task.objects[obj].getName();
            }
            cout <<")" << endl;
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
    model.add(IloMinimize(env, mainExp));

    // enforce typing of action parameters
    for (int i = 0; i < planLength; i++) {
        int iSchema = actionID(i);
        for (int j = 1; j <= numActions; j++) { // actions with initial index 1 (!)
            //cout << task.actions[j - 1].get_name() << endl;
            IloConstraint schemaEq = (v[iSchema] == j);
            auto params = task.actions[j - 1].get_parameters();
            for (int l = 0; l < params.size(); l++) {
                //cout << "- " << task.type_names[params[l].type] << ": ";
                int lower = lowerTindex[params[l].type];
                int upper = upperTindex[params[l].type];
//                for (int m = lower; m <= upper; m++) {
//                    cout << task.objects[indexToObj[m]].getName() << " ";
//                }
//                cout << endl;
                int iP = paramID(i, l);
                IloIfThen lowerVarRange(env, schemaEq, (v[iP] - 1) > (lower - 1));
                IloIfThen upperVarRange(env, schemaEq, (v[iP] - 1) < (upper + 1));
                model.add(lowerVarRange);
                model.add(upperVarRange);
            }
        }
    }

    // add goal condition
    // todo: check for containment in current state

//    for (int pred : task.goal.positive_nullary_goals) {
//        if (!s.get_nullary_atoms()[pred]) {
//
//        }
//    }
//    for (int pred : task.goal.negative_nullary_goals) {
//        if (!s.get_nullary_atoms()[pred]) {
//
//        }
//    }
//    for (const AtomicGoal &atomicGoal : task.goal.goal) {
//        int goal_predicate = atomicGoal.predicate;
//        const Relation &relation_at_goal_predicate = s.get_relations()[goal_predicate];
//
//        const auto it = relation_at_goal_predicate.tuples.find(atomicGoal.args);
//        const auto end = relation_at_goal_predicate.tuples.end();
//        if ((!atomicGoal.negated && it == end) || (atomicGoal.negated && it != end)) {
//            return false;
//        }
//    }
//    return true;











//    for (int j = 0; j < task.goal.goal.size(); j++) {
//        auto g = task.goal.goal[j];
//        auto sPart = s.get_tuples_of_relation(g.predicate);
//        if(sPart.find(g) == sPart.end()) {
//
//        }
//        int pred = task.goal.goal[j].predicate;
//        cout << "goal: " << task.predicates[pred].getName();
//        for (int k = 0; k < task.goal.goal[j].args.size(); k++) {
//            int obj = task.goal.goal[j].args[k];
//            cout << " " << task.objects[obj].getName();
//        }
//        cout << endl;
//    }
    //model.add(v[0] == 3);

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
