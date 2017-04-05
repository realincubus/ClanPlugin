
#pragma once

#include "MemoryAccess.hpp"

#include <string>
#include <vector>
#include <functional>

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

    unsigned int getSourceLocation();
    unsigned int getSourceLocationEnd();

    std::vector<ScopStmt*> sub_statements;

    enum AllowedAccessTypes{
      RespectBranches,
      IgnoreBranches
    };

    isl_union_map* getAccessesOfType(std::function<bool(MemoryAccess &)> Predicate, 
	isl_union_map* Accesses,
        isl_set* DomainParent = nullptr,	
	AllowedAccessTypes allowed_access_type = RespectBranches );

private:

  isl_set* ignoreTrueOrFalseBranch( isl_set*, isl_set* );

  pet_stmt* stmt = nullptr;  
  isl_union_map* schedule = nullptr;
  std::vector<MemoryAccess> memory_accesses;
    
};

