cmake_minimum_required(VERSION 3.9)
project(search)

set(CMAKE_CXX_STANDARD 17)

set(CPLEX_SOURCE_DIR /home/gregor/Workspace/cplex)
#set(CPLEX_SOURCE_DIR /home/dh/programme/CPLEX_Studio1210)
link_directories("/home/gregor/Workspace/kissat/build")


## required for IBM's CPLEX in order to force it to use newer names for the std headers
add_definitions(-DIL_STD)

list(APPEND linker_flags "$<$<CONFIG:DEBUG>:-lpthread;-g>" "$<$<CONFIG:RELEASE>:-flto;-lpthread>")

if (CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_CONFIGURATION_TYPES Debug Release)
endif ()

find_package(Boost COMPONENTS program_options REQUIRED)
if (Boost_FOUND)
    include_directories(${Boost_INCLUDE_DIRS})
    add_definitions( "-DHAS_BOOST" )
endif()


set(CMAKE_CXX_FLAGS "-Wall -Wnon-virtual-dtor")

# Release
set(CMAKE_CXX_FLAGS_RELEASE
        "-O3 -g -DNDEBUG -fomit-frame-pointer")

# Debug and Profile
set(CMAKE_CXX_FLAGS_DEBUG
        "${CMAKE_CXX_FLAGS_DEBUG} -Og -pg \
        -fsanitize=undefined -fno-omit-frame-pointer")


add_executable(search
        main.cc
        task.cc task.h
        predicate.cc predicate.h
        object.h
        states/state.cc states/state.h
        parser.cc parser.h
        goal_condition.h
        action_schema.cc action_schema.h
        structures.h
        search_engines/search_factory
        search_engines/search
        search_engines/breadth_first_search
        search_engines/greedy_best_first_search
        search_engines/nodes
        search_engines/utils
        search_engines/search_space
        action
        successor_generators/successor_generator.h
        database/table
        database/join
        database/utils
        heuristics/goalcount
        heuristics/heuristic.h
        heuristics/heuristic_factory
        heuristics/blind_heuristic.h
        successor_generators/successor_generator_factory
        successor_generators/naive_successor.h
        successor_generators/ordered_join_successor.cc successor_generators/ordered_join_successor.h
        successor_generators/generic_join_successor.cc successor_generators/generic_join_successor.h
        successor_generators/full_reducer_successor_generator.cc successor_generators/full_reducer_successor_generator.h
        database/semi_join.h database/semi_join.cc
        database/hash_join.cc database/hash_join.h
        hash_structures
        database/hash_semi_join.cc database/hash_semi_join.h
        utils.cc utils.h
        successor_generators/random_successor.h successor_generators/random_successor.cc
        successor_generators/yannakakis.cc successor_generators/yannakakis.h
        database/project.cc database/project.h
        utils/segmented_vector.h
        states/extensional_states
        states/sparse_states
        utils/hash.h
        algorithms/cartesian_iterator.h
        utils/collections.h
        utils/language.h
        utils/system
        utils/system_unix
        utils/system_windows
        utils/logging
        utils/timer
        algorithms/int_hash_set.h
        algorithms/dynamic_bitset.h
        search_statistics
        options.h open_lists/greedy_open_list.h
        lifted_heuristic/lifted_heuristic.cc lifted_heuristic/lifted_heuristic.h
        lifted_heuristic/arguments.h
        lifted_heuristic/atom.cc lifted_heuristic/atom.h
        lifted_heuristic/fact.cc lifted_heuristic/fact.h
        lifted_heuristic/term.h
        lifted_heuristic/logic_program.cc lifted_heuristic/logic_program.h
        lifted_heuristic/object.cc lifted_heuristic/object.h
        lifted_heuristic/rules/rule_base.cc lifted_heuristic/rules/rule_base.h
        lifted_heuristic/parser.cc lifted_heuristic/parser.h
        lifted_heuristic/rules/join.h lifted_heuristic/rules/product.h lifted_heuristic/rules/project.h
        lifted_heuristic/rule_matcher.cc lifted_heuristic/rule_matcher.h
        lifted_heuristic/grounders/grounder.h
        lifted_heuristic/grounders/weighted_grounder.cc lifted_heuristic/grounders/weighted_grounder.h search_engines/lazy_search.cc search_engines/lazy_search.h
		sat/lifted_sat.cpp sat/lifted_sat.h
		sat/sat_encoder.cpp sat/sat_encoder.h
		sat/ipasir.h
		sat/kissat.h sat/kissat.cpp
		)

add_library(cplex SHARED IMPORTED)
set_target_properties(cplex  PROPERTIES
        IMPORTED_LOCATION "${CPLEX_SOURCE_DIR}/cplex/lib/x86-64_linux/static_pic/libcplex.a"
        INTERFACE_INCLUDE_DIRECTORIES "${CPLEX_SOURCE_DIR}/cplex/include"
        )

add_library(ilocplex SHARED IMPORTED)
set_target_properties(ilocplex  PROPERTIES
        IMPORTED_LOCATION "${CPLEX_SOURCE_DIR}/cplex/lib/x86-64_linux/static_pic/libilocplex.a"
        INTERFACE_INCLUDE_DIRECTORIES "${CPLEX_SOURCE_DIR}/cplex/include"
        )

add_library(concert SHARED IMPORTED)
set_target_properties(concert  PROPERTIES
        IMPORTED_LOCATION "${CPLEX_SOURCE_DIR}/concert/lib/x86-64_linux/static_pic/libconcert.a"
        INTERFACE_INCLUDE_DIRECTORIES "${CPLEX_SOURCE_DIR}/concert/include"
        )

target_link_options(search PUBLIC ${linker_flags})

#target_link_libraries(search PRIVATE ipasircryptominisat5)
target_link_libraries(search PRIVATE kissat)

target_link_libraries(search PRIVATE ilocplex)
target_link_libraries(search PRIVATE concert)
target_link_libraries(search PRIVATE cplex)
target_link_libraries(search PRIVATE m)
target_link_libraries(search PRIVATE pthread)
target_link_libraries(search PRIVATE dl)
#target_link_libraries(search PRIVATE hlm)
target_link_libraries(search LINK_PUBLIC ${Boost_LIBRARIES})
