
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

#include "Scop.hpp"

struct PetReductionVariableInfo {
  std::string statement;
  std::string var_name;
  pet_op_type operation;
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
      codegen();
    }
    virtual ~Dependences () {}

    void calculateDependences( Scop& S);

    auto getRAW() { return RAW; };
    auto getWAR() { return WAR; };
    auto getWAW() { return WAW; };
    auto getRED() { return RED; };
    auto getDomains() { return scop.getDomains() ; }
    

    std::vector<PetReductionVariableInfo> find_reduction_variables( );

    PlutoCompatData build_pluto_data( );
    PlutoCompatData make_pluto_compatible( std::vector<int>& rename_table, PlutoCompatData& pcd );
    isl_union_map* considerKillStatements( isl_union_map*, isl_schedule*, isl_union_map*, isl_union_map* );


    void collectInfo(Scop& S, isl_union_map **Read, isl_union_map **Write,
                        isl_union_map **MayWrite,
                        isl_union_map **AccessSchedule,
                        isl_union_map **StmtSchedule,
			isl_union_map **KillStatements,
                        Dependences::AnalyisLevel Level);

    // TODO move to own class if test is successful
    void codegen();

    isl_ctx* getContext( pet_scop* pscop );
    void addPrivatizationDependences();
    void setReductionDependences(MemoryAccess *MA, isl_map *D);

    unsigned int getSourceLocationByTupleName( std::string );

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
    bool OptKillStatementAnalysis = true;

    Scop scop;
    
};
