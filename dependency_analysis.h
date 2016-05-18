
#pragma once

#include "pet.h"
#include "pet_cxx.h"
#include <isl/arg.h>
#include <isl/flow.h>
#include <isl/map.h>
#include <isl/set.h>
#include <isl/union_set.h>
#include <isl/ctx.h>
#include <iostream>
#include <llvm/ADT/DenseMap.h>
#include "pluto_compat.h"

// a statement has multiple memory accesses

// Adapter class that uses pet_expr to provide information
class MemoryAccess {
public:
  MemoryAccess (pet_expr* _expr) :
    expr(_expr)
  {
      std::cerr << "dep analysis: new access " << std::endl;
      is_read = pet_expr_access_is_read( expr );
      is_write = pet_expr_access_is_write( expr );
      if ( is_read && is_write ) {
	std::cerr << "dep ana: can not handle this right now" << std::endl;
	exit(-1);
      }
      if ( is_read ) {
	access_relation = isl_map_from_union_map(pet_expr_access_get_may_read( expr ));
      }
      if ( is_write ) {
	access_relation = isl_map_from_union_map(pet_expr_access_get_may_write( expr ));
      }
  }
  virtual ~MemoryAccess () {}

  bool isReductionLike() {
    // TODO implement by calling pet_ functions
    //      right now simply return false since we have no idea
    return false;
  }

  // TODO needs to return isl_map not union map -> this means that the access relations 
  //      return by the functions have to containe only one element
  // TODO continue here call the is_* functions and return the result otherwise its just an empty set
  isl_map* getAccessRelation(){
    return access_relation;
  }

  // TODO is something that returns A of A[i+1]
  // Needs to handle accesses to arrays,values ...
  auto getBaseAddr() {
    
  }

  bool isRead(){
    return is_read;
  }
  
  bool isWrite(){
    return is_write;
  }

  isl_id* getId(){
    return pet_expr_access_get_id( expr );
  }

  isl_id* getArrayId(){
    return pet_expr_access_get_ref_id( expr );
  }

  void filter ( std::vector<int>& filter ){
    rename_map( access_relation, filter ); 
  }

private:

  bool is_read = false;
  bool is_write = false;
  //bool is_array = false;
  isl_id* id = nullptr;

  isl_map* access_relation = nullptr;

  pet_expr* expr;

};

static int helper(__isl_keep pet_expr* expr, void* user ){
  std::vector<MemoryAccess>* memory_accesses = (std::vector<MemoryAccess>*) user;
  memory_accesses->emplace_back( expr );
  return 0;
}

class ScopStmt {
public:
    ScopStmt (pet_stmt* stmt, isl_union_map* _schedule) :
      schedule( _schedule )
    {
      std::cerr << "dep analysis: new stmt with " << " x accesses " << std::endl;
      pet_tree_foreach_access_expr( 
	  stmt->body, &helper, &memory_accesses
      );
      
      domain = isl_set_copy( stmt->domain );
      space = isl_set_get_space(stmt->domain);
    }
    virtual ~ScopStmt () {}

    isl_set* getDomain(){
      return domain;    
    }

    auto begin(){
      return memory_accesses.begin();
    }

    auto end(){
      return memory_accesses.end();
    }

    auto getDomainSpace() const {
      return space;
    }

    // from ScopInfo.cpp
    auto getSchedule(){
      isl_set *Domain = getDomain();
      if (isl_set_is_empty(Domain)) {
	isl_set_free(Domain);
	return isl_map_from_aff(
	    isl_aff_zero_on_domain(isl_local_space_from_space(getDomainSpace())));
      }
      auto *Schedule = schedule;
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

    void filter ( std::vector<int>& filter ) {
      rename_set( domain, filter );
      for( auto& access : *this ){
        access.filter( filter );
      }
    }

private:

  isl_set* domain = nullptr;
  isl_space* space = nullptr;
  isl_union_map* schedule = nullptr;
  std::vector<MemoryAccess> memory_accesses;
    
};

class Scop {
public:


    auto getSchedule(){
      return schedule;
    }

    auto getScheduleMap(){
      return schedule_map;
    }

    // pet scop must just be used for construction and not be kept 
    // otherwise the filter operations will not work like expected
    Scop (pet_scop* scop)
    {
      schedule = isl_schedule_copy(scop->schedule);
      schedule_map = isl_schedule_get_map(schedule);
      std::cerr << "dep analysis: new scop with " << scop->n_stmt << " statements " << std::endl;
      for (int i = 0; i < scop->n_stmt; ++i){
        scop_stmts.emplace_back( scop->stmts[i], getScheduleMap() );
      }

      space = isl_set_get_space(scop->context);
    }
    virtual ~Scop () {}


    isl_space* getParamSpace() {
      return space;
    }

    auto begin(){
      return scop_stmts.begin();
    }

    auto end(){
      return scop_stmts.end();
    }

    auto getDomains() {
      isl_union_set *Domain = isl_union_set_empty(getParamSpace());

      for (ScopStmt &Stmt : *this) {
	Domain = isl_union_set_add_set(Domain, Stmt.getDomain());
      }

      return Domain;
    }

    auto getScheduleTree( ) {
      return isl_schedule_intersect_domain(isl_schedule_copy(getSchedule()), getDomains());
    }

    auto filter ( std::vector<int>& filter ){
      linearize_union_map ( space, schedule_map, filter );
      for( auto& stmt : *this ){
        stmt.filter( filter );
      }
    }

private:
    isl_space* space = nullptr;
    isl_union_map* schedule_map = nullptr;
    isl_schedule* schedule = nullptr;
    std::vector<ScopStmt> scop_stmts;
};

class Dependences {
public:

    /// @brief Map type for reduction dependences.
    using ReductionDependencesMapTy = llvm::DenseMap<MemoryAccess *, isl_map *>;

    enum AnalyisLevel {
      AL_Statement = 0,
      // Distinguish accessed memory references in the same statement
      AL_Reference,
      // Distinguish memory access instances in the same statement
      AL_Access,

      NumAnalysisLevels
    };  
    enum AnalysisType { 
      VALUE_BASED_ANALYSIS, 
      MEMORY_BASED_ANALYSIS
    };

    Dependences (pet_scop* _pscop ) :
      pscop( _pscop ),
      scop( pscop ),
      RAW(nullptr), 
      WAR(nullptr), 
      WAW(nullptr), 
      RED(nullptr), 
      TC_RED(nullptr)
    {
      IslCtx = getContext( pscop ) ;

      //collectInfo( scop, &reads, &writes, &may_writes, &access_schedule, &stmt_schedule, Level );
      calculateDependences( scop );
    }
    virtual ~Dependences () {}

    void calculateDependences( Scop& S);

    auto getRAW() { return RAW; };
    auto getWAR() { return WAR; };
    auto getWAW() { return WAW; };
    auto getRED() { return RED; };
    auto getDomains() { return scop.getDomains() ; }

    void make_pluto_compatible( std::vector<int>& filter ) {
      scop.filter( filter );
    }

private:

    void collectInfo(Scop& S, isl_union_map **Read, isl_union_map **Write,
                        isl_union_map **MayWrite,
                        isl_union_map **AccessSchedule,
                        isl_union_map **StmtSchedule,
                        Dependences::AnalyisLevel Level);

    isl_ctx* getContext( pet_scop* pscop );
    void addPrivatizationDependences();
    void setReductionDependences(MemoryAccess *MA, isl_map *D);


    bool UseReductions = true;

    pet_scop* pscop = nullptr;
    isl_union_map* reads;
    isl_union_map* writes;
    isl_union_map* may_writes;
    isl_union_map* access_schedule;
    isl_union_map* stmt_schedule;
    Dependences::AnalyisLevel Level = AL_Statement;
    isl_ctx* IslCtx;

    /// @brief The different basic kinds of dependences we calculate.
    isl_union_map *RAW;
    isl_union_map *WAR;
    isl_union_map *WAW;

    /// @brief The special reduction dependences.
    isl_union_map *RED;

    /// @brief The (reverse) transitive closure of reduction dependences.
    isl_union_map *TC_RED;

    // "Bound the dependence analysis by a maximal amount of "
    // "computational steps (0 means no bound)"
    int OptComputeOut = 500000;

    AnalysisType OptAnalysisType = VALUE_BASED_ANALYSIS;

    /// @brief Mapping from memory accesses to their reduction dependences.
    ReductionDependencesMapTy ReductionDependences;

    Scop scop;
    
};
