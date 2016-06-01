
#pragma once

#include "MemoryAccess.hpp"

#include <string>
#include <vector>

struct pet_stmt;
struct isl_union_map;
struct isl_set;
struct isl_map;
struct isl_space;

class ScopStmt {
public:
    ScopStmt (pet_stmt* _s, isl_union_map* _schedule);
    virtual ~ScopStmt () {}

    isl_set* getDomain();

    auto begin(){
      return memory_accesses.begin();
    }

    auto end(){
      return memory_accesses.end();
    }

    isl_space* getDomainSpace() const;
    isl_map* getSchedule();

    std::string getTupleName();

private:

  pet_stmt* stmt = nullptr;  
  isl_union_map* schedule = nullptr;
  std::vector<MemoryAccess> memory_accesses;
    
};

