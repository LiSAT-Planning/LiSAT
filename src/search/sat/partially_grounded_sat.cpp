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

#include "pddl/pddl.h"

static const char* root_type_cppdl = "__object_cpddl";

using namespace std;

struct obj_key {
    int obj_id;
    const char *name;
    uint32_t hash;
    pddl_list_t htable;
};
typedef struct obj_key obj_key_t;

static pddl_htable_key_t objHash(const pddl_list_t *key, void *_)
{
    const obj_key_t *obj = pddl_container_of(key, obj_key_t, htable);
    return obj->hash;
}

static int objEq(const pddl_list_t *key1, const pddl_list_t *key2, void *_)
{
    const obj_key_t *obj1 = pddl_container_of(key1, obj_key_t, htable);
    const obj_key_t *obj2 = pddl_container_of(key2, obj_key_t, htable);
    return strcmp(obj1->name, obj2->name) == 0;
}




vector<unordered_set<int>> reinferTypeHierarchy(const Task & task){
    cout << "- re-inferring type hierarchy..." << endl;
    int numTypes = task.type_names.size();
	std::unordered_set<int>* types = new unordered_set<int>[numTypes];
    for (tSize obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (tSize i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            types[j].insert(obj);
        }
    }
    vector<unordered_set<int>> parents(numTypes); // todo: equal sets
    for (int child = 0; child < numTypes; child++) {
		if (types[child].size() == 0) continue;

        for (int parent = 0; parent < numTypes; parent++) {
            if (child == parent) continue;
            if (types[child].size() <= types[parent].size()) {
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
	delete[] types;
	return parents;
}


vector<int> computedirectParents(vector<unordered_set<int>> parents, const Task & task){
    // make directional if there are multiple identical types
    int numTypes = parents.size();
	for (int i = 0; i < numTypes; i++) {
        for (int j = 0; j < numTypes; j++) {
            if (i == j) continue;
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(i) != parents[j].end())) {
                    parents[i].erase(parents[i].find(j));
                }
		}
	}
    
    // make sparse
	for (int j = 0; j < numTypes; j++) {
        for (int i = 0; i < numTypes; i++) {
            if (i == j) continue;
            for (int k = 0; k < numTypes; k++) {
                if ((i == k) || (j == k)) continue;
				//j is parent of i
				//k is parent of j
				//k is parent of i
				//then erase: k is parent of i
                if ((parents[i].find(j) != parents[i].end())
                    && (parents[j].find(k) != parents[j].end())
                    && (parents[i].find(k) != parents[i].end())) {
                    parents[i].erase(parents[i].find(k));
                }
            }
        }
    }

	vector<int> directparents(parents.size());

	for(unsigned int type = 0; type < parents.size(); type++)
		if (parents[type].size() == 0){
			directparents[type] = -1;
		} else if (parents[type].size() == 1){
			directparents[type] = *(parents[type].begin());
		} else {
			cout << "Type " << type << " has multiple direct parents ... this is impossbile." << endl;
   			exit_with(utils::ExitCode::SEARCH_UNSUPPORTED);
		}

	return directparents;
}



PartiallyGroundedSAT::PartiallyGroundedSAT(const Task & task) {
	int numActions = task.actions.size();
    int numObjs = task.objects.size();
#ifdef CMAKE_NO_CPDDL 
	cout << "Compiled without CPDDL support" << endl;
   	exit_with(utils::ExitCode::SEARCH_UNSUPPORTED);
#endif
	cout << "Extracting FAM groups using [Fiser, AAAI 2020] ...";

	pddl_t * pddl = new pddl_t;
    bzero(pddl,sizeof(pddl_t));
    std::string name = "dom";
    pddl->domain_name = const_cast<char*>(name.c_str());
    std::string name2 = "prob";
    pddl->problem_name = const_cast<char*>(name2.c_str());
    pddl->require.strips = 1;
    pddl->require.typing = 1;
    pddl->require.equality = 1;

	vector<unordered_set<int>> parents = reinferTypeHierarchy(task);
	vector<int> directparents = computedirectParents(parents,task);

    int numTypes = task.type_names.size();
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
        cout << "}" << " direct parent: " << (directparents[i] == -1?"none":task.type_names[directparents[i]]) << endl;
    }

	// adding all the types to CPDDL
	pddlTypesAdd(&pddl->type,root_type_cppdl,-1);
    for (int i = 0; i < numTypes; i++) {
		pddlTypesAdd(&pddl->type,task.type_names[i].c_str(),directparents[i]+1);

	}


	bzero(&pddl->obj, sizeof(pddl->obj));
	pddl->obj.htable = pddlHTableNew(objHash, objEq, NULL);

	// looping over all objects
	std::unordered_set<int>* types = new unordered_set<int>[numTypes];
    for (tSize obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
        for (tSize i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            types[j].insert(obj);
        }
    }


	for (tSize obj = 0; obj < task.objects.size(); obj++) {
        auto oTypes = task.objects[obj].getTypes();
		int actType = -1;
		int typesize = 0x3f3f3f3f;
        for (tSize i = 0; i < oTypes.size(); i++) {
            int j = oTypes[i];
            if (types[j].size() < typesize){
				typesize = types[j].size();
				actType = j;
			}
        }

		pddl_obj_t *objP = pddlObjsAdd(&pddl->obj, task.objects[obj].getName().c_str());
		objP->type = actType + 1;
		objP->is_constant = false;
	}





	//for (size_t o = 0; o < domain.constants.size(); o++)
	//	cpddl_add_object_of_sort(pddl,domain.constants[o], ourTypeIDToCPDDL[objectType[o]]);


	cout << endl;
    pddlPrintPDDLDomain(pddl,stdout);
    pddlPrintPDDLProblem(pddl,stdout);


	cout << " done" << endl;
}

utils::ExitCode PartiallyGroundedSAT::solve(const Task &task, int limit, bool optimal, bool incremental) {
	cout << "Not yet implemented!" << endl;
	return utils::ExitCode::SEARCH_UNSOLVED_INCOMPLETE;
}


