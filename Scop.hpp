#pragma once

#include <string>
#include <vector>
#include <functional>
#include <memory>

#include "ScopStmt.hpp"

//class ScopStmt;
class MemoryAccess;

struct pet_scop;
struct isl_space;
struct isl_schedule;
struct isl_union_map;
struct isl_set;
struct isl_union_set;

class Scop {
public:



    Scop( pet_scop* );

    virtual ~Scop () {}

    auto begin(){
      return scop_stmts.begin();
    }

    auto end(){
      return scop_stmts.end();
    }

    isl_space* getParamSpace();
    isl_set* getContext();
    isl_union_set* getDomains();
    isl_schedule* getSchedule();
    isl_schedule* getScheduleTree();
    ScopStmt* getStmtByTupleName( std::string name );
    isl_union_map* getKillStatements();

    isl_union_map* getAccessesOfType(std::function<bool(MemoryAccess &)> Predicate);
    isl_union_map* getMustWrites();
    isl_union_map* getMayWrites();
    isl_union_map* getWrites();
    isl_union_map* getReads();
    isl_union_map* getAccesses();
private:


    pet_scop* scop;
    std::vector<std::unique_ptr<ScopStmt>> scop_stmts;
};



