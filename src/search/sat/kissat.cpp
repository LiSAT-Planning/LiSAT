#include "ipasir.h"
#include "kissat.h"
#include <stdio.h>
#include <cstdlib>
#include <vector>

int clauseCount = 0;


#include <iostream>
#include <fstream>

std::string dmacsfilepath = "formula.cnf";
std::ofstream dmacsfile;
std::vector<std::vector<int>> formula;
std::vector<int> curclause;
int maxVar = -1;

#undef NDEBUG

extern "C" {

/**
 * Return the name and the version of the incremental SAT
 * solving library.
 */
IPASIR_API const char * ipasir_signature (){
	return kissat_signature();
}

/**
 * Construct a new solver and return a pointer to it.
 * Use the returned pointer as the first parameter in each
 * of the following functions.
 *
 * Required state: N/A
 * State after: INPUT
 */
IPASIR_API void * ipasir_init (){
	formula.clear();
	maxVar = -1;
	return kissat_init();
}

/**
 * Release the solver, i.e., all its resoruces and
 * allocated memory (destructor). The solver pointer
 * cannot be used for any purposes after this call.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: undefined
 */
IPASIR_API void ipasir_release (void * solver){
	return kissat_release((kissat*)solver);
}

/**
 * Add the given literal into the currently added clause
 * or finalize the clause with a 0.  Clauses added this way
 * cannot be removed. The addition of removable clauses
 * can be simulated using activation literals and assumptions.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 *
 * Literals are encoded as (non-zero) integers as in the
 * DIMACS formats.  They have to be smaller or equal to
 * INT_MAX and strictly larger than INT_MIN (to avoid
 * negation overflow).  This applies to all the literal
 * arguments in API functions.
 */
IPASIR_API void ipasir_add (void * solver, int lit_or_zero){
#ifndef NDEBUG
	curclause.push_back(lit_or_zero);
	if (lit_or_zero > maxVar) maxVar = lit_or_zero;
#endif
	if (lit_or_zero == 0){
		clauseCount++;
#ifndef NDEBUG
		formula.push_back(curclause);
		//std::cout << "CLAUSE";
		//for (int i : curclause) std::cout << " " << i;
		//std::cout << std::endl;
		curclause.clear();
#endif
	}
	kissat_add((kissat*)solver,lit_or_zero);
}

/**
 * Add an assumption for the next SAT search (the next call
 * of ipasir_solve). After calling ipasir_solve all the
 * previously added assumptions are cleared.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 */
IPASIR_API void ipasir_assume (void * solver, int lit){
	printf("Not supported by kissat\n");
	exit(0);
}

/**
 * Solve the formula with specified clauses under the specified assumptions.
 * If the formula is satisfiable the function returns 10 and the state of the solver is changed to SAT.
 * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to UNSAT.
 * If the search is interrupted (see ipasir_set_terminate) the function returns 0 and the state of the solver remains INPUT.
 * This function can be called in any defined state of the solver.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
IPASIR_API int ipasir_solve (void * solver){
#ifndef NDEBUG
	dmacsfile.open(dmacsfilepath);
	dmacsfile << "p cnf " << maxVar + 1 << " " << formula.size() << std::endl;
	for (auto clause: formula){
		for (size_t i = 0; i < clause.size(); i++)
			dmacsfile << (i?" ":"") << clause[i];
		dmacsfile << std::endl;
	}
  	dmacsfile.close();
#endif
	return kissat_solve((kissat*)solver);
}

/**
 * Get the truth value of the given literal in the found satisfying
 * assignment. Return 'lit' if True, '-lit' if False, and 0 if not important.
 * This function can only be used if ipasir_solve has returned 10
 * and no 'ipasir_add' nor 'ipasir_assume' has been called
 * since then, i.e., the state of the solver is SAT.
 *
 * Required state: SAT
 * State after: SAT
 */
IPASIR_API int ipasir_val (void * solver, int lit){
	return kissat_value((kissat*)solver,lit);
}
}
