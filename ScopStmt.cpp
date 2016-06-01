

#include "ScopStmt.hpp"
#include <iostream>
#include "pet.h"
#include "pet_cxx.h"

#include <isl/union_set.h>

static int helper( pet_expr* expr, void* user ){
  std::vector<MemoryAccess>* memory_accesses = (std::vector<MemoryAccess>*) user;
  memory_accesses->emplace_back( expr );
  return 0;
}

ScopStmt::ScopStmt (pet_stmt* _s, isl_union_map* _schedule) :
  stmt(_s),
  schedule( _schedule )
{
  std::cerr << "dep analysis: new stmt with " << " x accesses " << std::endl;
  pet_tree_foreach_access_expr( 
      stmt->body, &helper ,
      &memory_accesses
  );
  
}


isl_set* ScopStmt::getDomain(){
  return isl_set_copy(stmt->domain);    
}


isl_space* ScopStmt::getDomainSpace() const {
  return isl_set_get_space(stmt->domain);
}

isl_map* ScopStmt::getSchedule(){
  isl_set *Domain = getDomain();
  if (isl_set_is_empty(Domain)) {
    isl_set_free(Domain);
    return isl_map_from_aff(
	isl_aff_zero_on_domain(isl_local_space_from_space(getDomainSpace())));
  }
  auto *Schedule = isl_union_map_copy(schedule);
  Schedule = isl_union_map_intersect_domain(
      Schedule, isl_union_set_from_set(isl_set_copy(Domain)));
  if (isl_union_map_is_empty(Schedule)) {
    isl_set_free(Domain);
    isl_union_map_free(Schedule);
    return isl_map_from_aff(
	isl_aff_zero_on_domain(isl_local_space_from_space(getDomainSpace())));
  }
  auto *M = isl_map_from_union_map(Schedule);
  M = isl_map_coalesce(M);
  M = isl_map_gist_domain(M, Domain);
  M = isl_map_coalesce(M);
  return M;

}

std::string ScopStmt::getTupleName(){
      auto domain = getDomain();
      const char* name = isl_set_get_tuple_name( domain );
      isl_set_free( domain );
      return name;
    }
