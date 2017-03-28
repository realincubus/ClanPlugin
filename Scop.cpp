

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

	if (stmt->n_arg > 0) 
		isl_die(isl_union_set_get_ctx(domain),
			isl_error_unsupported,
			"data dependent conditions not supported",
			return isl_union_set_free(domain));

	domain_i = isl_set_copy(scop->stmts[i]->domain);
	domain = isl_union_set_add_set(domain, domain_i);
    }

    return domain;
}



Scop::Scop (pet_scop* _s) :
  scop(_s)
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
