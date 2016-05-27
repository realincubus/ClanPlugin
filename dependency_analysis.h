
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

// a statement has multiple memory accesses

// Adapter class that uses pet_expr to provide information
class MemoryAccess {
public:
  MemoryAccess (pet_expr* _expr) :
    expr(_expr)
  {
      std::cerr << "dep analysis: new access " << std::endl;
  }
  virtual ~MemoryAccess () {}

  bool isReductionLike() {
    // TODO implement by calling pet_ functions
    //      right now simply return false since we have no idea
    return pet_expr_access_is_reduction( expr );
    //return false;
  }

  // TODO needs to return isl_map not union map -> this means that the access relations 
  //      return by the functions have to containe only one element
  // TODO continue here call the is_* functions and return the result otherwise its just an empty set
  isl_map* getAccessRelation();

  auto getBaseAddr() {
    //return pet_expr_access_get_ref_id( expr );
    return pet_expr_access_get_id( expr );
  }

  bool isRead(){
    return pet_expr_access_is_read( expr );
  }
  
  bool isWrite(){
    return pet_expr_access_is_write( expr );
  }

  bool isMayWrite(){

  }

  bool isMustWrite(){

  }

  isl_id* getId(){
    return pet_expr_access_get_id( expr );
  }

  isl_id* getArrayId(){
    return pet_expr_access_get_ref_id( expr );
  }

private:
  
  pet_expr* expr = nullptr;  

};

static int helper(__isl_keep pet_expr* expr, void* user ){
  std::vector<MemoryAccess>* memory_accesses = (std::vector<MemoryAccess>*) user;
  memory_accesses->emplace_back( expr );
  return 0;
}

class ScopStmt {
public:
    ScopStmt (pet_stmt* _s, isl_union_map* _schedule) :
      stmt(_s),
      schedule( _schedule )
    {
      std::cerr << "dep analysis: new stmt with " << " x accesses " << std::endl;
      pet_tree_foreach_access_expr( 
	  stmt->body, &helper 
	  /*
	  [&]( __isl_keep pet_expr* expr, void* user ) {
	    memory_accesses.emplace_back( expr );
	    return (int)0;
	  }
	  */
	  ,
	  &memory_accesses
      );
      
    }
    virtual ~ScopStmt () {}

    isl_set* getDomain(){
      return isl_set_copy(stmt->domain);    
    }

    auto begin(){
      return memory_accesses.begin();
    }

    auto end(){
      return memory_accesses.end();
    }

    auto getDomainSpace() const {
      return isl_set_get_space(stmt->domain);
    }

    // from ScopInfo.cpp
    auto getSchedule(){
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

    std::string getTupleName(){
      auto domain = getDomain();
      const char* name = isl_set_get_tuple_name( domain );
      isl_set_free( domain );
      return name;
    }

private:

  pet_stmt* stmt = nullptr;  
  isl_union_map* schedule = nullptr;
  std::vector<MemoryAccess> memory_accesses;
    
};

class Scop {
public:


    auto getSchedule(){
      return scop->schedule;
    }

    Scop (pet_scop* _s) :
      scop(_s)
    {
      std::cerr << "dep analysis: new scop with " << scop->n_stmt << " statements " << std::endl;
      for (int i = 0; i < scop->n_stmt; ++i){
        scop_stmts.emplace_back( scop->stmts[i], isl_schedule_get_map(getSchedule()) );
      }
    }
    virtual ~Scop () {}


    isl_space* getParamSpace() {
      return isl_set_get_space(scop->context);
    }

    auto begin(){
      return scop_stmts.begin();
    }

    auto end(){
      return scop_stmts.end();
    }

    auto getContext(){
      return scop->context;
    }

#if 0
    // this will collect kill statements and domains that are not in use
    auto getDomains() {
      return pet_scop_collect_domains(scop);
    }
#endif

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

    ScopStmt* getStmtByTupleName( std::string name ) {
      for( auto& element : scop_stmts ){
        if ( element.getTupleName() == name ) {
	  return &element;
	}
      }
      return nullptr;
    }

    __isl_give isl_union_map* getAccessesOfType(std::function<bool(MemoryAccess &)> Predicate);
    __isl_give isl_union_map* getMustWrites();
    __isl_give isl_union_map* getMayWrites();
    __isl_give isl_union_map* getWrites();
    __isl_give isl_union_map* getReads();
    __isl_give isl_union_map* getAccesses();
private:


    pet_scop* scop;
    std::vector<ScopStmt> scop_stmts;
};

/// @brief for pluto compatibility
struct PlutoCompatData{
    isl_union_map* schedule = nullptr;
    isl_union_map* reads = nullptr;
    isl_union_map* writes = nullptr;
    isl_union_map* empty  = nullptr;
    isl_union_set* domains = nullptr;
    isl_set* context = nullptr;

    isl_union_map* raw = nullptr;
    isl_union_map* war = nullptr;
    isl_union_map* waw = nullptr;
    isl_union_map* red = nullptr;
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

      calculateDependences( scop );
    }
    virtual ~Dependences () {}

    void calculateDependences( Scop& S);

    auto getRAW() { return RAW; };
    auto getWAR() { return WAR; };
    auto getWAW() { return WAW; };
    auto getRED() { return RED; };
    auto getDomains() { return scop.getDomains() ; }
    
    std::vector<std::pair<std::string,std::string>> find_reduction_variables( );

    PlutoCompatData build_pluto_data( );
    PlutoCompatData make_pluto_compatible( std::vector<int>& rename_table, PlutoCompatData& pcd );


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
    Dependences::AnalyisLevel Level = AL_Statement;
    isl_ctx* IslCtx;


    /// @brief The different basic kinds of dependences we calculate.
    isl_union_map *RAW = nullptr;
    isl_union_map *WAR = nullptr;
    isl_union_map *WAW = nullptr;

    /// @brief The special reduction dependences.
    isl_union_map *RED = nullptr;

    /// @brief The (reverse) transitive closure of reduction dependences.
    isl_union_map *TC_RED = nullptr;

    // "Bound the dependence analysis by a maximal amount of "
    // "computational steps (0 means no bound)"
    int OptComputeOut = 500000;

    AnalysisType OptAnalysisType = VALUE_BASED_ANALYSIS;

    /// @brief Mapping from memory accesses to their reduction dependences.
    ReductionDependencesMapTy ReductionDependences;

    Scop scop;
    
};
