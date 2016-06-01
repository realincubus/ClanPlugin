
#include <MemoryAccess.hpp>
#include <iostream>

#include "pet.h"
#include "pet_cxx.h"
#include <isl/map.h>

using namespace std;

isl_map* MemoryAccess::getAccessRelation(){
  if ( pet_expr_access_is_read( expr ) ) {
    return isl_map_from_union_map(pet_expr_access_get_may_read( expr ));
  }
  if ( pet_expr_access_is_write( expr ) ) {
    return isl_map_from_union_map(pet_expr_access_get_may_write( expr ));
  }
  return (isl_map*)nullptr;
}

MemoryAccess::MemoryAccess (pet_expr* _expr) :
  expr(_expr)
{
    std::cerr << "dep analysis: new access " << std::endl;
}


bool MemoryAccess::isReductionLike() {
  return pet_expr_access_is_reduction( expr );
}


isl_id* MemoryAccess::getBaseAddr() {
  return pet_expr_access_get_id( expr );
}


bool MemoryAccess::isRead(){
  return pet_expr_access_is_read( expr );
}

bool MemoryAccess::isWrite(){
  return pet_expr_access_is_write( expr );
}

bool MemoryAccess::isMayWrite(){
  assert(0);
}


bool MemoryAccess::isMustWrite(){
  assert(0);
}


int MemoryAccess::getReductionType(){
  return (int)pet_expr_access_get_reduction_type( expr );
}

isl_id* MemoryAccess::getId(){
  return pet_expr_access_get_id( expr );
}


isl_id* MemoryAccess::getArrayId(){
  return pet_expr_access_get_ref_id( expr );
}
