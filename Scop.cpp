

#include "Scop.hpp"
#include "ScopStmt.hpp"

#include "pet.h"
#include "pet_cxx.h"

#include <isl/map.h>
#include <isl/union_map.h>
#include <isl/union_set.h>
#include <isl/set.h>

#include <iostream>

using namespace std;

isl_union_set* Scop::getDomains() {
  isl_union_set *Domain = isl_union_set_empty(getParamSpace());

  for (auto& Stmt : *this) {
    Domain = isl_union_set_add_set(Domain, Stmt->getDomain());
  }

  return Domain;
}

isl_union_set* Scop::getNonKillDomains(){
    int i;
    isl_set *domain_i;
    isl_union_set *domain;

    if (!scop)
	    return NULL;

    domain = isl_union_set_empty(isl_set_get_space(scop->context));

    for (i = 0; i < scop->n_stmt; ++i) {
	struct pet_stmt *stmt = scop->stmts[i];

	if (pet_stmt_is_kill( stmt ) )
		continue;

#if 0
	if ( stmt->n_arg > 0 ) {
	  error_reporter(pet_loc_get_start(stmt->loc), "data dependent conditions not supported");
	  return isl_union_set_free(domain);
	}
#endif

#if 1
	if ( stmt->n_arg > 0 ) {
	  warning_reporter(pet_loc_get_start(stmt->loc), "data dependent condition ignoring:");
	  isl_set_dump( scop->stmts[i]->domain );
	  continue;
	}
#endif

	domain_i = isl_set_copy(scop->stmts[i]->domain);
	domain = isl_union_set_add_set(domain, domain_i);
    }

    return domain;
}



Scop::Scop (
    pet_scop* _s, 
    reporter_function _warning_reporter, 
    reporter_function _error_reporter) :
  scop(_s),
  warning_reporter(_warning_reporter),
  error_reporter(_error_reporter)
{
  std::cerr << "dep analysis: new scop with " << scop->n_stmt << " statements " << std::endl;
  for (int i = 0; i < scop->n_stmt; ++i){
    scop_stmts.emplace_back( new ScopStmt(scop->stmts[i], isl_schedule_get_map(getSchedule())) );
  }
}


ScopStmt* Scop::getStmtByTupleName( std::string name ) {
  for( auto& element : scop_stmts ){
    if ( element->getTupleName() == name ) {
      return element.get();
    }
  }
  return nullptr;
}


isl_space* Scop::getParamSpace() {
  return isl_set_get_space(scop->context);
}


isl_schedule* Scop::getScheduleTree( ) {
  return isl_schedule_intersect_domain(isl_schedule_copy(getSchedule()), getDomains());
}


isl_set* Scop::getContext(){
  return scop->context;
}


isl_schedule* Scop::getSchedule(){
  return scop->schedule;
}

isl_union_map* 
Scop::getKillStatements( ){
  return pet_scop_collect_must_kills( scop );
}


void
Scop::get_sub_statements( ScopStmt* super_stmt ) {
  auto begin = super_stmt->getSourceLocation();
  auto end = super_stmt->getSourceLocationEnd();
  super_stmt->sub_statements.clear();

  for (auto& Stmt : *this) {
    auto sloc_start = Stmt->getSourceLocation();
    auto sloc_end = Stmt->getSourceLocationEnd();
    if ( sloc_start > begin ) {
      if ( sloc_end < end ) {
	super_stmt->sub_statements.push_back( Stmt.get() );
      }
    }
  }
}




// since pet stores the read and write information for the memory accesses but changes the
// iteration space to indicate that the statement can not be executed this function needs to 
// skip these statements somehow
__isl_give isl_union_map *
Scop::getAccessesOfType(std::function<bool(MemoryAccess &)> Predicate) {
  isl_union_map *Accesses = isl_union_map_empty(getParamSpace());

  cerr << "depana test: " << __PRETTY_FUNCTION__ << endl ;

  int ctr = 0;
  for (auto& Stmt : *this) {
    get_sub_statements( Stmt.get() );

    Accesses = Stmt->getAccessesOfType( Predicate, Accesses );
    cerr << "iteration " << ctr++ << " accesses in " << __PRETTY_FUNCTION__ << endl;
    isl_union_map_dump( Accesses );
  }
  return isl_union_map_coalesce(Accesses);
}

__isl_give isl_union_map *Scop::getMustWrites() {
  return getAccessesOfType([](MemoryAccess &MA) { return MA.isMustWrite(); });
}

__isl_give isl_union_map *Scop::getMayWrites() {
  return getAccessesOfType([](MemoryAccess &MA) { return MA.isMayWrite(); });
}

__isl_give isl_union_map *Scop::getWrites() {
  return getAccessesOfType([](MemoryAccess &MA) { return MA.isWrite(); });
}

__isl_give isl_union_map *Scop::getReads() {
  return getAccessesOfType([](MemoryAccess &MA) { return MA.isRead(); });
}

__isl_give isl_union_map *Scop::getAccesses() {
  return getAccessesOfType([](MemoryAccess &MA) { return true; });
}
