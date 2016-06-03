#pragma once

#include <vector>

struct isl_set;
struct isl_map;
struct isl_union_map;
struct isl_union_set;
struct isl_space;

isl_set* rename_set( isl_set* set, std::vector<int>& rename_table );
isl_union_set* linearize_union_set( isl_space* space, isl_union_set* domains, std::vector<int>& rename_table );
isl_stat rename_map( isl_map* map, void* user );
isl_union_map* linearize_union_map( isl_space* space, isl_union_map* map, std::vector<int>& rename_table);

