#include "sat_encoder.h"
#include "ipasir.h"
#include <iostream>
#include <cassert>
#include <math.h> 

bool no_colors_in_output = false;

std::string color(Color color, std::string text, Mode m, Color background){
	if (no_colors_in_output) return text;
	return std::string ()
		+ "\033[" +std::to_string (m)+ ";" + std::to_string (30 + color) + "m"
		+ ((background != COLOR_NONE)?("\033[" + std::to_string (40 + background) + "m"):"")
		+ text
		+ "\033[0;m"
  ;
}

std::string path_string(std::vector<int> & path){
	std::string s = "";
	for (int & i : path){
		if (s.size()) s+= ",";
		s+= std::to_string(i);
	}

	return s;
}

std::string path_string_no_sep(std::vector<int> & path){
	std::string s = "";
	for (int & i : path)
		s+= std::to_string(i);

	return s;
}

std::string pad_string(std::string s, int chars){
	while (int(s.size()) < chars)
		s += " ";
	return s;
}

std::string pad_int(int i, int chars){
	return pad_string(std::to_string(i),chars);
}

std::string pad_path(std::vector<int> & path, int chars){
	return pad_string(path_string(path),chars);
}


sat_capsule::sat_capsule(){
	number_of_variables = 0;
}

int sat_capsule::new_variable(){
	return ++number_of_variables;
}

#ifndef NDEBUG
void sat_capsule::registerVariable(int v, std::string name){
	assert(v > 0);
	if (v <= 0) exit(42);
	assert(variableNames.count(v) == 0);
	variableNames[v] = name;	
}

void sat_capsule::printVariables(){
	std::cout << "===========================" << std::endl;
	for (auto & p : variableNames){
		std::string s = std::to_string(p.first);
		int x = 4 - s.size();
		while (x-- && x > 0) std::cout << " ";
		std::cout << s << " -> " << p.second << std::endl;
	}
	std::cout << "===========================" << std::endl;
}
#endif

int number_of_clauses = 0;

void reset_number_of_clauses(){
	number_of_clauses = 0;
}

int get_number_of_clauses(){
	return number_of_clauses;
}

void assertYes(void* solver, int i){
	ipasir_add(solver,i);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void assertNot(void* solver, int i){
	ipasir_add(solver,-i);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void implies(void* solver, int i, int j){
	//DEBUG(std::cout << "Adding " << -i << " " << j << " " << 0 << std::endl);
	ipasir_add(solver,-i);
	ipasir_add(solver,j);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void impliesAnd(void* solver, int i, int j, int k){
	//DEBUG(std::cout << "Adding " << -i << " " << j << " " << 0 << std::endl);
	ipasir_add(solver,-i);
	ipasir_add(solver,-j);
	ipasir_add(solver,k);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void impliesNot(void* solver, int i, int j){
	//DEBUG(std::cout << "Adding " << -i << " " << j << " " << 0 << std::endl);
	ipasir_add(solver,-i);
	ipasir_add(solver,-j);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void impliesOr(void* solver, int i, std::vector<int> & j){
	ipasir_add(solver,-i);
	for (int & x : j)
		ipasir_add(solver,x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void notImpliesOr(void* solver, int i, std::vector<int> & j){
	ipasir_add(solver,i);
	for (int & x : j)
		ipasir_add(solver,x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void impliesOr(void* solver, int i, int k, std::vector<int> & j){
	ipasir_add(solver,-i);
	ipasir_add(solver,-k);
	for (int & x : j)
		ipasir_add(solver,x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void andImpliesOr(void* solver, int i, int ii, const std::set<int> & j){
	ipasir_add(solver,-i);
	ipasir_add(solver,-ii);
	for (const int & x : j)
		ipasir_add(solver,x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void andImpliesOr(void* solver, const std::vector<int> & i, const std::set<int> & j){
	for (const int & x : i)
		ipasir_add(solver,-x);
	for (const int & x : j)
		ipasir_add(solver,x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void impliesPosAndNegImpliesOr(void* solver, int i, int j, std::vector<int> & k){
	ipasir_add(solver,-i);
	ipasir_add(solver,j);
	for (int & x : k)
		ipasir_add(solver,x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void impliesAllNot(void* solver, int i, std::vector<int> & j){
	for (int & x : j){
		ipasir_add(solver,-i);
		ipasir_add(solver,-x);
		ipasir_add(solver,0);
		number_of_clauses++;
	}
}

void notImpliesAllNot(void* solver, int i, std::vector<int> & j){
	for (int & x : j){
		ipasir_add(solver,i);
		ipasir_add(solver,-x);
		ipasir_add(solver,0);
		number_of_clauses++;
	}
}

void andImplies(void* solver, int i, int j, int k){
	ipasir_add(solver,-i);
	ipasir_add(solver,-j);
	ipasir_add(solver,k);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void andImpliesNot(void* solver, int i, int j, int k){
	ipasir_add(solver,-i);
	ipasir_add(solver,-j);
	ipasir_add(solver,-k);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void andImplies(void* solver, int i, int j, int k, int l){
	ipasir_add(solver,-i);
	ipasir_add(solver,-j);
	ipasir_add(solver,-k);
	ipasir_add(solver,l);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void andImplies(void* solver, std::set<int> i, int j){
	for (const int & x : i)
		ipasir_add(solver,-x);
	ipasir_add(solver,j);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void notAll(void* solver, std::set<int> i){
	for (const int & x : i)
		ipasir_add(solver,-x);
	ipasir_add(solver,0);
	number_of_clauses++;
}

void atMostOneBinomial(void* solver, sat_capsule & capsule, std::vector<int> & is){
	for (size_t i = 0; i < is.size(); i++){
		int ii = is[i];
		for (size_t j = i+1; j < is.size(); j++){
			impliesNot(solver,ii,is[j]);
		}
	}
}


void atMostOne(void* solver, sat_capsule & capsule, std::vector<int> & is){
	if (is.size() <= 1) return; // nothing to do

	if (is.size() < 32){
		atMostOneBinomial(solver,capsule,is);
		return;
	}

	int bits = (int) ceil(log(is.size()) / log(2));

	int baseVar = capsule.new_variable();
	DEBUG(capsule.registerVariable(baseVar,"at-most-one " + pad_int(0)));

	for (int b = 1; b < bits; b++){
#ifndef NDEBUG
		int r =
#endif
			capsule.new_variable(); // ignore return, they will be incremental
		assert(r == baseVar + b);
		DEBUG(capsule.registerVariable(baseVar + b,"at-most-one " + pad_int(b)));
	}


	for (size_t i = 0; i < is.size(); i++){
		int & var = is[i];

		for (int b = 0; b < bits; b++){
			ipasir_add(solver,-var);
			if (i & (1 << b))
				ipasir_add(solver,-(baseVar + b));
			else	
				ipasir_add(solver,  baseVar + b );
			ipasir_add(solver,0);
			number_of_clauses++;
		}
	}
}


void atMostK(void* solver, sat_capsule & capsule, int K, std::vector<int> & is){
	std::vector<int> vars;
	for (int x = 0; x < int(is.size()); x++){
		vars.push_back(capsule.new_variable());
		for (int i = 1; i <= K+1; i++)
			capsule.new_variable(); // id will not be needed
	}

	vars.push_back(capsule.new_variable());
	for (int i = 1; i <= K+1; i++)
		capsule.new_variable(); // id will not be needed


	for (int i = 0; i < int(is.size()); i++){
		for (int j = 0; j <= K; j++){
			ipasir_add(solver,-is[i]);
			ipasir_add(solver,-(vars[i] + j));
			ipasir_add(solver,(vars[i+1] + j + 1));
			ipasir_add(solver,0);
			
			ipasir_add(solver,-(vars[i] + j));
			ipasir_add(solver,(vars[i+1] + j));
			ipasir_add(solver,0);
		}
		ipasir_add(solver,-(vars[i+1]+K+1));
		ipasir_add(solver,0);
	}
	
	ipasir_add(solver,vars[0]);
	ipasir_add(solver,0);
}

void atLeastOne(void* solver, sat_capsule & capsule, std::vector<int> & is){
	for (int & i : is)
		ipasir_add(solver, i);
	ipasir_add(solver,0);
	number_of_clauses++;
}

