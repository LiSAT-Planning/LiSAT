# Powerlifted Planner

Powerlifted is a domain-independent classical planner that uses only lifted
representations.

(See [References](#references) for more details.)

## Building
Powerlifted is build using the `build.py` script.


This version of powerlifted can either be build with or without support for SAT-based planning.
To build with SAT support, you need to call the script with the argument `-s` followed by the path to the directory that contains your sat solver's library.
You need to build the SAT solver before building powerlifted and you need to build the SAT solver s.t. a library is produced.
Some SAT solvers don't do this by default!


Currently, powerlifted uses the SAT solver [kissat](https://github.com/arminbiere/kissat) by default.
It can be configured to use [cryptominisat](https://github.com/msoos/cryptominisat) by providing the argument `-i` to `build.py`.
Instead of cryptominisat, any SAT solving offering the [IPASIR](https://github.com/biotomas/ipasir) interface can be used.
If so desired, in src/search/CMakeLists.txt, the reference to `ipasircryptominisat5` must be changed appropriately.


## Usage

The `powerlifted.py` script solves a PDDL task provided as input. It also builds
the planner if the `--build` parameter is passed. The script has the following
parameters:

```$ ./powerlifted.py [-d DOMAIN] -i INSTANCE -s SEARCH -e HEURISTIC -g GENERATOR [--state STATE REPR.] [ADDITIONAL OPTIONS] [--seed RANDOM SEED] [-l PLANLENGH] [-o] [-I] [--build]```

Use the `build.py` script to build the planner first.

### Available Options for `SEARCH`:
- `bfs`: Breadth-First Search (This option was previously called `naive`. You
  can still use `naive` with the `powerlifted.py` script but the planner will internally
  use the new keyword `bfs`.)
- `gbfs`: Greedy Best-First Search
- `lazy`: Lazy Best-First Search
- `lazy-po`: Lazy Best-First Search with Boosted Dual-Queue
- `lazy-prune`: Lazy Best-First Search with pruning of states generated by
non-preferred operators
- `sat`: Search via reduction to SAT. If chosed the options `-l`, `-o`, and `-I` become available.

### Available Options for `HEURISTIC`:
- `add`: The additive heuristic
- `blind`: No Heuristic
- `goalcount`: The goal-count/STRIPS heuristic
- `hmax`: The hmax heuristic (Note that A* search is not implemented)

### Available Options for `GENERATOR`:
- `join`: Join program using the predicate order given in the PDDL file
- `random_join`: Randomly ordered join program
- `ordered_join`: Join program ordered by the arity of the predicates
- `full_reducer`: Generate successor for acyclic schemas using the full
  reducer method; for cyclic schemas it uses a partial reducer and a join
  program.
- `yannakakis`: Same as above but replaces the final join of the full
      reducer method by the Yannakakis' project-join program.

### Available Options for `STATE REPR.`:

- `sparse`: Use the sparse state representation where a state is only
  represented by the facts that are true in this state.
- `extensional`: Use the extensional representation where a state is a bitset
  where the ith-bit is true if the fact associated to it is true in this
  state. This representation requires the grounding of facts (but not of
  actions) which, right now, is performed in the search component.

### Avaialble Options for `PLANLENGH`:
A plan lenght may only be provided if SAT-based planning is chosen.

If the planner is run in satisficing mode, it will attempt to solve the given problem **only** for this plan length.
If `PLANLENGH` is not set, it is defaulted to 100.

If the planner is run in optimal mode, it will stop searching for a solution if `PLANLENGH` is reached. I.e. it will only find a solution if there is one with length at most `PLANLENGH`

### Flag `-o`
By default, powerlifted runs in **satisficing** mode.
In this mode, it will try to find a plan up to `PLANLENGH`.
To obtain a complete satisficing planner, you need to run powerlifted for **multiple** values of `PLANLENGH`s as if there was a portfolio. We recommend to use `10,25,50,100,200` with assigning all runs equal time.
Note that powerlifted can as of now, not run such a portfolio.
This is due to difficulties is setting timelimits to SAT-solver calls correctly.


If the flag `-o` is provided, the powerlifted runs in optimal mode.
It will iterate over the length of the plan and return the shortest (in terms of number of actions) solution.


### Flag `-I`
This flag sets the SAT planner to incremental mode. This does not affect the output of the planner, but may inpact its performance.

Incremental mode is only supported if the SAT solver that powerlifted was build with supports incremental solving.
Note that `kissat` does not support incremental solving.


### Available `ADDITIONAL OPTIONS`:
- `[--translator-output-file TRANSLATOR_FILE]`: Output of the intermediate representation to be parsed by the search component will be saved into `TRANSLATOR_FILE`. (Default: `output.lifted`)
- `[--datalog-file DATALOG_FILE]`: Datalog program used by the h-add heuristic will be saved into `DATALOG_FILE`. (Default: `model.lp`)
- `[--keep-action-predicates]`: Keeps action predicates in the Datalog program
- `[--keep-duplicated-rules]`: Keep duplicated Datalog rules in the Datalog program.
- `[--add-inequalities]`: Compile inequalities into an EDB predicate in the Datalog program and replace `(not (= ?x ?y))` atoms with this new EDB predicate in actions.
- `[--validate]`: Runs VAL after a plan is found to validate it. This requires
  [VAL](https://github.com/KCL-Planning/VAL) to be added as `validate` to the `PATH`.


## Running Powerlifted as a Singularity container

You can also build a Singularity image to run the planner. This might be useful
in the case where you are not able to compile the planner locally, for
example. To do so, first remove the `builds/` directory, in case you have any
builds already in your system. Then, you can run the following command to create
the planner image:


``` sudo singularity build powerlifted.sif Singularity```

Be aware that this might take a while. Once the image `powerlifted.sif` is
created, you can run it with the same parameters as the `powerlifted.py`
script. The only exception is that, by default, VAL is not installed in the
container, so it is not possible to use the `--validate` flag with the
Singularity image. However, you can run VAL with the `sas_plan` file created by
the planner after the execution. The following command is a usage example on
how to run the planner with the Singularity image:

```./powerlifted.sif -i /path/to/instance.pddl -s lazy-po -e add -g yannakakis --datalog-file model.lp --translator-output-file output.lifted```



## Components
 - Translator
 - Search component

## Requirements
 - A C++17-compliant compiler
 - CMake 3.9+
 - Python 3.5+
 - Boost

## Limitations
 - **Axioms**: not supported
 - **Conditional effects**: not supported
 - **Costs**: ignored
 - **Negated preconditions**: only inequality
 - **Quantifiers**: not supported

 ## References

 1. Corrêa, A. B.; Pommerening, F.; Helmert, M.; and Francès, G. 2020. Lifted Successor Generation using Query Optimization Techniques. In Proc. ICAPS 2020, pp. 80-89. [[pdf]](https://ai.dmi.unibas.ch/papers/correa-et-al-icaps2020.pdf)
 2. Corrêa, A. B.; Pommerening, F.; Helmert, M.; and Francès, G. 2020. Code from the paper "Lifted Successor Generationusing Query Optimization Techniques".  https://doi.org/10.5281/zenodo.3687008
 3. Corrêa, A. B.; Francès, G.; Pommerening, F.; and Helmert, M. 2021. Delete-Relaxation Heuristics for Lifted Classical Planning. In Proc. ICAPS 2021. (To appear)
