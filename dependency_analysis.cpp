

#include "dependency_analysis.h"
#include "pluto_compat.h"
#include "MemoryAccess.hpp"
#include "ScopStmt.hpp"
#include "plog/Log.h"

#include <isl/schedule_node.h>

#include <iostream>


/// @brief Tag the @p Relation domain with @p TagId
static __isl_give isl_map *tag(__isl_take isl_map *Relation,
                               __isl_take isl_id *TagId) {
  isl_space *Space = isl_map_get_space(Relation);
  Space = isl_space_drop_dims(Space, isl_dim_out, 0, isl_map_n_out(Relation));
  Space = isl_space_set_tuple_id(Space, isl_dim_out, TagId);
  isl_multi_aff *Tag = isl_multi_aff_domain_map(Space);
  Relation = isl_map_preimage_domain_multi_aff(Relation, Tag);
  return Relation;
}


/// @brief Tag the @p Relation domain with either MA->getArrayId() or
///        MA->getId() based on @p TagLevel
static __isl_give isl_map *tag(__isl_take isl_map *Relation, MemoryAccess *MA,
                               Dependences::AnalyisLevel TagLevel) {
  if (TagLevel == Dependences::AL_Reference)
    // TODO changed this from getArrayId
    return tag(Relation, MA->getId());

  if (TagLevel == Dependences::AL_Access)
    return tag(Relation, MA->getId());

  // No need to tag at the statement level.
  return Relation;
}



/// @brief Collect information about the SCoP @p S.
void
Dependences::collectInfo(Scop &S, isl_union_map **Read, isl_union_map **Write,
                        isl_union_map **MayWrite,
                        isl_union_map **AccessSchedule,
                        isl_union_map **StmtSchedule,
			isl_union_map **KillStatements,
                        Dependences::AnalyisLevel Level) {
  isl_space *Space = S.getParamSpace();
  *Read = isl_union_map_empty(isl_space_copy(Space));
  *Write = isl_union_map_empty(isl_space_copy(Space));
  *MayWrite = isl_union_map_empty(isl_space_copy(Space));
  *AccessSchedule = isl_union_map_empty(isl_space_copy(Space));
  *StmtSchedule = isl_union_map_empty(isl_space_copy(Space));

#if 1
  std::set<const isl_id *> ReductionBaseValues;
  if (UseReductions)
    for (auto& Stmt : S)
      for (MemoryAccess& MA : *Stmt)
        if (MA.isReductionLike())
          ReductionBaseValues.insert(MA.getBaseAddr());
#endif

  for (auto& Stmt : S) {
    for (MemoryAccess& MA : *Stmt) {
      isl_set *domcp = Stmt->getDomain();
      isl_map *accdom = MA.getAccessRelation();
      if ( !accdom ) {
	continue;
      }

      LOGD << "dep anaylsis: dumping isl_union_map of accdom"  ;
      isl_map_dump( accdom );

      accdom = isl_map_intersect_domain(accdom, domcp);
      LOGD << "after intersect with domain" ;
      isl_map_dump( accdom );
      LOGD << "done dumping: after intersect with domain" ;

      if (ReductionBaseValues.count(MA.getBaseAddr())) {
        // Wrap the access domain and adjust the schedule accordingly.
        //
        // An access domain like
        //   Stmt[i0, i1] -> MemAcc_A[i0 + i1]
        // will be transformed into
        //   [Stmt[i0, i1] -> MemAcc_A[i0 + i1]] -> MemAcc_A[i0 + i1]
        //
        // The original schedule looks like
        //   Stmt[i0, i1] -> [0, i0, 2, i1, 0]
        // but as we transformed the access domain we need the schedule
        // to match the new access domains, thus we need
        //   [Stmt[i0, i1] -> MemAcc_A[i0 + i1]] -> [0, i0, 2, i1, 0]
        isl_map *Schedule = Stmt->getSchedule();
        Schedule = isl_map_apply_domain(
            Schedule,
            isl_map_reverse(isl_map_domain_map(isl_map_copy(accdom))));
        accdom = isl_map_range_map(accdom);

        *AccessSchedule = isl_union_map_add_map(*AccessSchedule, Schedule);
      } else {
	LOGD << "dep analysis: tagging accdom" ;
        accdom = tag(accdom, &MA, Level);
        if (Level > Dependences::AL_Statement) {
          isl_map *Schedule = tag(Stmt->getSchedule(), &MA, Level);
          *StmtSchedule = isl_union_map_add_map(*StmtSchedule, Schedule);
        }
      }

      LOGD << "dep analysis: adding reads" ;
      // in contrast to llvm nodes, something from clang AST can be both  
      if (MA.isRead()){
        *Read = isl_union_map_add_map(*Read, isl_map_copy(accdom));
      }
      
      LOGD << "dep analysis: adding writes" ;
      if (MA.isWrite()){
        *Write = isl_union_map_add_map(*Write, isl_map_copy(accdom));
      }
      LOGD << "dep analysis: done MA loop" ;

      // TODO i think i need to delete the accdom now
    }

    if (Level == Dependences::AL_Statement){
      *StmtSchedule = isl_union_map_add_map(*StmtSchedule, Stmt->getSchedule());
    }
    LOGD << "done " << __PRETTY_FUNCTION__ ;
  }

  // TODO i have no idea what this is about
#if 1
  *StmtSchedule =
      isl_union_map_intersect_params(*StmtSchedule, isl_set_copy(S.getContext()));
#endif

  *KillStatements = S.getKillStatements();

  *KillStatements = isl_union_map_coalesce( *KillStatements );
  *Read = isl_union_map_coalesce(*Read);
  *Write = isl_union_map_coalesce(*Write);
  *MayWrite = isl_union_map_coalesce(*MayWrite);

  LOGD << "read" ;
  isl_union_map_dump( *Read );
  LOGD << "write" ;
  isl_union_map_dump( *Write );
  LOGD << "may write" ;
  isl_union_map_dump( *MayWrite );
  LOGD << "schedule" ;
  isl_union_map_dump( *StmtSchedule );
  LOGD << "kill statements" ;
  isl_union_map_dump( *KillStatements );
}

#define DEBUG(x) 
#define dbgs() LOGD 


static __isl_give isl_union_flow *buildFlow(__isl_keep isl_union_map *Snk,
                                            __isl_keep isl_union_map *Src,
                                            __isl_keep isl_union_map *MaySrc,
                                            __isl_keep isl_schedule *Schedule) {
  isl_union_access_info *AI;

  AI = isl_union_access_info_from_sink(isl_union_map_copy(Snk));
  AI = isl_union_access_info_set_may_source(AI, isl_union_map_copy(MaySrc));
  if (Src)
    AI = isl_union_access_info_set_must_source(AI, isl_union_map_copy(Src));
  AI = isl_union_access_info_set_schedule(AI, isl_schedule_copy(Schedule));
  auto Flow = isl_union_access_info_compute_flow(AI);
  if (!Flow) dbgs() << "last error: "
             << isl_ctx_last_error(isl_schedule_get_ctx(Schedule))
             << '\n';;
  return Flow;
}

static isl_stat getMaxScheduleDim(__isl_take isl_map *Map, void *User) {
  unsigned int *MaxScheduleDim = (unsigned int *)User;
  *MaxScheduleDim = std::max(*MaxScheduleDim, isl_map_dim(Map, isl_dim_out));
  isl_map_free(Map);
  return isl_stat_ok;
}

static __isl_give isl_union_map *
addZeroPaddingToSchedule(__isl_take isl_union_map *Schedule) {
  unsigned int MaxScheduleDim = 0;

  isl_union_map_foreach_map(Schedule, getMaxScheduleDim, &MaxScheduleDim);

  auto ExtensionMap = isl_union_map_empty(isl_union_map_get_space(Schedule));
  for (unsigned int i = 0; i <= MaxScheduleDim; i++) {
    auto *Map = isl_map_identity(
        isl_space_alloc(isl_union_map_get_ctx(Schedule), 0, i, i));
    Map = isl_map_add_dims(Map, isl_dim_out, MaxScheduleDim - i);
    for (unsigned int j = 0; j < MaxScheduleDim - i; j++)
      Map = isl_map_fix_si(Map, isl_dim_out, i + j, 0);

    ExtensionMap = isl_union_map_add_map(ExtensionMap, Map);
  }
  Schedule = isl_union_map_apply_range(Schedule, ExtensionMap);

  return Schedule;
}

void Dependences::calculateDependences( Scop& S ){
  isl_union_map *Read, *Write, *MayWrite, *AccessSchedule, *StmtSchedule;
  isl_schedule *Schedule;
  isl_union_map* KillStatements;

  DEBUG(dbgs() << "Scop: \n" << S << "\n");

  collectInfo(S, 
      &Read, 
      &Write, 
      &MayWrite, 
      &AccessSchedule, 
      &StmtSchedule, 
      &KillStatements, 
      Level
  );

  DEBUG(dbgs() << "Read: " << Read << '\n';
        dbgs() << "Write: " << Write << '\n';
        dbgs() << "MayWrite: " << MayWrite << '\n';
        dbgs() << "AccessSchedule: " << AccessSchedule << '\n';
        dbgs() << "StmtSchedule: " << StmtSchedule << '\n';);

  LOGD << "AccessSchedule" ;
  isl_union_map_dump( AccessSchedule );

  if (isl_union_map_is_empty(AccessSchedule)) {
    isl_union_map_free(AccessSchedule);
    Schedule = S.getScheduleTree();
    // Tag the schedule tree if we want fine-grain dependence info
    if (Level > AL_Statement) {
      auto TaggedDom = isl_union_map_domain((isl_union_map_copy(StmtSchedule)));
      auto TaggedMap = isl_union_set_unwrap(TaggedDom);
      auto Tags = isl_union_map_domain_map_union_pw_multi_aff(TaggedMap);
      Schedule = isl_schedule_pullback_union_pw_multi_aff(Schedule, Tags);
    }
  } else {
    auto *ScheduleMap =
        isl_union_map_union(AccessSchedule, isl_union_map_copy(StmtSchedule));
    Schedule = isl_schedule_from_domain(
        isl_union_map_domain(isl_union_map_copy(ScheduleMap)));
    if (!isl_union_map_is_empty(ScheduleMap)) {
      ScheduleMap = addZeroPaddingToSchedule(ScheduleMap);
      Schedule = isl_schedule_insert_partial_schedule(
          Schedule, isl_multi_union_pw_aff_from_union_map(ScheduleMap));
    } else {
      isl_union_map_free(ScheduleMap);
    }
  }


  long MaxOpsOld = isl_ctx_get_max_operations(IslCtx);
  if (OptComputeOut)
    isl_ctx_set_max_operations(IslCtx, OptComputeOut);

  // TODO this might not be part of this isl version 
  //isl_options_set_on_error(IslCtx, ISL_ON_ERROR_CONTINUE);

  DEBUG(dbgs() << "Read: " << Read << "\n";
        dbgs() << "Write: " << Write << "\n";
        dbgs() << "MayWrite: " << MayWrite << "\n";
        dbgs() << "Schedule: " << Schedule << "\n");

  RAW = WAW = WAR = RED = nullptr;

  if (OptAnalysisType == VALUE_BASED_ANALYSIS) {
    isl_union_flow *Flow;

    Flow = buildFlow(Read, Write, MayWrite, Schedule);

    RAW = isl_union_flow_get_must_dependence(Flow);
    isl_union_flow_free(Flow);

    Flow = buildFlow(Write, Write, Read, Schedule);

    WAW = isl_union_flow_get_must_dependence(Flow);
    WAR = isl_union_flow_get_may_dependence(Flow);

    // This subtraction is needed to obtain the same results as were given by
    // isl_union_map_compute_flow. For large sets this may add some compile-time
    // cost. As there does not seem to be a need to distinguish between WAW and
    // WAR, refactoring Polly to only track general non-flow dependences may
    // improve performance.
    WAR = isl_union_map_subtract(WAR, isl_union_map_copy(WAW));

    LOGD << "raw" ;
    isl_union_map_dump( RAW );
    LOGD << "war" ;
    isl_union_map_dump( WAR );
    LOGD << "waw" ;
    isl_union_map_dump( WAW );

    if ( OptKillStatementAnalysis ) {
      LOGD << "deleting paths by kills for WAR";
      WAR = considerKillStatements( WAR, Schedule, Write, KillStatements ) ;
    }

    if ( OptKillStatementAnalysis ) {
      LOGD << "deleting paths by kills for WAW";
      WAW = considerKillStatements( WAW, Schedule, Write, KillStatements ) ;
    }

    isl_union_flow_free(Flow);
    isl_schedule_free(Schedule);
  } else {
    isl_union_flow *Flow;

    Write = isl_union_map_union(Write, isl_union_map_copy(MayWrite));

    Flow = buildFlow(Read, nullptr, Write, Schedule);

    RAW = isl_union_flow_get_may_dependence(Flow);
    isl_union_flow_free(Flow);

    Flow = buildFlow(Write, nullptr, Read, Schedule);

    WAR = isl_union_flow_get_may_dependence(Flow);
    isl_union_flow_free(Flow);

    Flow = buildFlow(Write, nullptr, Write, Schedule);

    WAW = isl_union_flow_get_may_dependence(Flow);
    isl_union_flow_free(Flow);
    isl_schedule_free(Schedule);
  }


  isl_union_map_free(MayWrite);
  isl_union_map_free(Write);
  isl_union_map_free(Read);

  RAW = isl_union_map_coalesce(RAW);
  WAW = isl_union_map_coalesce(WAW);
  WAR = isl_union_map_coalesce(WAR);

  // error handling 
  if (isl_ctx_last_error(IslCtx) == isl_error_quota) {
    isl_union_map_free(RAW);
    isl_union_map_free(WAW);
    isl_union_map_free(WAR);
    RAW = WAW = WAR = nullptr;
    isl_ctx_reset_error(IslCtx);
  }
  // TODO might not be in this isl version isl_options_set_on_error(IslCtx.get(), ISL_ON_ERROR_ABORT);
  isl_ctx_reset_operations(IslCtx);
  isl_ctx_set_max_operations(IslCtx, MaxOpsOld);

  LOGD << "raw" ;
  isl_union_map_dump( RAW );
  LOGD << "war" ;
  isl_union_map_dump( WAR );
  LOGD << "waw" ;
  isl_union_map_dump( WAW );

  isl_union_map *STMT_RAW, *STMT_WAW, *STMT_WAR;
  STMT_RAW = isl_union_map_intersect_domain(
      isl_union_map_copy(RAW),
      isl_union_map_domain(isl_union_map_copy(StmtSchedule)));
  STMT_WAW = isl_union_map_intersect_domain(
      isl_union_map_copy(WAW),
      isl_union_map_domain(isl_union_map_copy(StmtSchedule)));
  STMT_WAR = isl_union_map_intersect_domain(isl_union_map_copy(WAR),
                                            isl_union_map_domain(StmtSchedule));

  LOGD << "stmt_raw" ;
  isl_union_map_dump( STMT_RAW );
  LOGD << "stmt_war" ;
  isl_union_map_dump( STMT_WAR );
  LOGD << "stmt_waw" ;
  isl_union_map_dump( STMT_WAW );

  DEBUG({
    dbgs() << "Wrapped Dependences:\n";
    dump();
    dbgs() << "\n";
  });

  // To handle reduction dependences we proceed as follows:
  // 1) Aggregate all possible reduction dependences, namely all self
  //    dependences on reduction like statements.
  // 2) Intersect them with the actual RAW & WAW dependences to the get the
  //    actual reduction dependences. This will ensure the load/store memory
  //    addresses were __identical__ in the two iterations of the statement.
  // 3) Relax the original RAW and WAW dependences by subtracting the actual
  //    reduction dependences. Binary reductions (sum += A[i]) cause both, and
  //    the same, RAW and WAW dependences.
  // 4) Add the privatization dependences which are widened versions of
  //    already present dependences. They model the effect of manual
  //    privatization at the outermost possible place (namely after the last
  //    write and before the first access to a reduction location).

  // Step 1)
  RED = isl_union_map_empty(isl_union_map_get_space(RAW));
  for (auto& Stmt : S) {
    for (MemoryAccess& MA : *Stmt) {
      if (!MA.isReductionLike())
        continue;
      isl_set *AccDomW = isl_map_wrap(MA.getAccessRelation());
      isl_map *Identity =
          isl_map_from_domain_and_range(isl_set_copy(AccDomW), AccDomW);
      RED = isl_union_map_add_map(RED, Identity);
    }
  }

  // Step 2)
  RED = isl_union_map_intersect(RED, isl_union_map_copy(RAW));
  RED = isl_union_map_intersect(RED, isl_union_map_copy(WAW));

  if (!isl_union_map_is_empty(RED)) {

    // Step 3)
    RAW = isl_union_map_subtract(RAW, isl_union_map_copy(RED));
    WAW = isl_union_map_subtract(WAW, isl_union_map_copy(RED));

    // Step 4)
    addPrivatizationDependences();
  }

  DEBUG({
    dbgs() << "Final Wrapped Dependences:\n";
    dump();
    dbgs() << "\n";
  });

  LOGD << "RED" ;
  isl_union_map_dump( RED );


  // RED_SIN is used to collect all reduction dependences again after we
  // split them according to the causing memory accesses. The current assumption
  // is that our method of splitting will not have any leftovers. In the end
  // we validate this assumption until we have more confidence in this method.
  isl_union_map *RED_SIN = isl_union_map_empty(isl_union_map_get_space(RAW));

  // For each reduction like memory access, check if there are reduction
  // dependences with the access relation of the memory access as a domain
  // (wrapped space!). If so these dependences are caused by this memory access.
  // We then move this portion of reduction dependences back to the statement ->
  // statement space and add a mapping from the memory access to these
  // dependences.
  for (auto& Stmt : S) {
    for (MemoryAccess& MA : *Stmt) {
      if (!MA.isReductionLike())
        continue;

      isl_set *AccDomW = isl_map_wrap(MA.getAccessRelation());
      isl_union_map *AccRedDepU = isl_union_map_intersect_domain(
          isl_union_map_copy(TC_RED), isl_union_set_from_set(AccDomW));
      if (isl_union_map_is_empty(AccRedDepU) && !isl_union_map_free(AccRedDepU))
        continue;

      isl_map *AccRedDep = isl_map_from_union_map(AccRedDepU);
      RED_SIN = isl_union_map_add_map(RED_SIN, isl_map_copy(AccRedDep));
      AccRedDep = isl_map_zip(AccRedDep);
      AccRedDep = isl_set_unwrap(isl_map_domain(AccRedDep));
    }
  }

  assert(isl_union_map_is_equal(RED_SIN, TC_RED) &&
         "Intersecting the reduction dependence domain with the wrapped access "
         "relation is not enough, we need to loosen the access relation also");
  isl_union_map_free(RED_SIN);

  RAW = isl_union_map_zip(RAW);
  WAW = isl_union_map_zip(WAW);
  WAR = isl_union_map_zip(WAR);
  RED = isl_union_map_zip(RED);
  TC_RED = isl_union_map_zip(TC_RED);

  DEBUG({
    dbgs() << "Zipped Dependences:\n";
    dump();
    dbgs() << "\n";
  });

  RAW = isl_union_set_unwrap(isl_union_map_domain(RAW));
  WAW = isl_union_set_unwrap(isl_union_map_domain(WAW));
  WAR = isl_union_set_unwrap(isl_union_map_domain(WAR));
  RED = isl_union_set_unwrap(isl_union_map_domain(RED));
  TC_RED = isl_union_set_unwrap(isl_union_map_domain(TC_RED));

  DEBUG({
    dbgs() << "Unwrapped Dependences:\n";
    dump();
    dbgs() << "\n";
  });

  RAW = isl_union_map_union(RAW, STMT_RAW);
  WAW = isl_union_map_union(WAW, STMT_WAW);
  WAR = isl_union_map_union(WAR, STMT_WAR);

  RAW = isl_union_map_coalesce(RAW);
  WAW = isl_union_map_coalesce(WAW);
  WAR = isl_union_map_coalesce(WAR);
  RED = isl_union_map_coalesce(RED);
  TC_RED = isl_union_map_coalesce(TC_RED);

  LOGD << "TC_RED" ;
  isl_union_map_dump( TC_RED );

#if 0
  DEBUG(dump());
#endif

}

isl_ctx* Dependences::getContext( pet_scop* pscop ){
  return isl_set_get_ctx(pscop->context);
}

/// @brief Fix all dimension of @p Zero to 0 and add it to @p user
static isl_stat fixSetToZero(__isl_take isl_set *Zero, void *user) {
  isl_union_set **User = (isl_union_set **)user;
  for (unsigned i = 0; i < isl_set_dim(Zero, isl_dim_set); i++)
    Zero = isl_set_fix_si(Zero, isl_dim_set, i, 0);
  *User = isl_union_set_add_set(*User, Zero);
  return isl_stat_ok;
}

/// @brief Compute the privatization dependences for a given dependency @p Map
///
/// Privatization dependences are widened original dependences which originate
/// or end in a reduction access. To compute them we apply the transitive close
/// of the reduction dependences (which maps each iteration of a reduction
/// statement to all following ones) on the RAW/WAR/WAW dependences. The
/// dependences which start or end at a reduction statement will be extended to
/// depend on all following reduction statement iterations as well.
/// Note: "Following" here means according to the reduction dependences.
///
/// For the input:
///
///  S0:   *sum = 0;
///        for (int i = 0; i < 1024; i++)
///  S1:     *sum += i;
///  S2:   *sum = *sum * 3;
///
/// we have the following dependences before we add privatization dependences:
///
///   RAW:
///     { S0[] -> S1[0]; S1[1023] -> S2[] }
///   WAR:
///     {  }
///   WAW:
///     { S0[] -> S1[0]; S1[1024] -> S2[] }
///   RED:
///     { S1[i0] -> S1[1 + i0] : i0 >= 0 and i0 <= 1022 }
///
/// and afterwards:
///
///   RAW:
///     { S0[] -> S1[i0] : i0 >= 0 and i0 <= 1023;
///       S1[i0] -> S2[] : i0 >= 0 and i0 <= 1023}
///   WAR:
///     {  }
///   WAW:
///     { S0[] -> S1[i0] : i0 >= 0 and i0 <= 1023;
///       S1[i0] -> S2[] : i0 >= 0 and i0 <= 1023}
///   RED:
///     { S1[i0] -> S1[1 + i0] : i0 >= 0 and i0 <= 1022 }
///
/// Note: This function also computes the (reverse) transitive closure of the
///       reduction dependences.
void Dependences::addPrivatizationDependences() {
  isl_union_map *PrivRAW, *PrivWAW, *PrivWAR;

  // The transitive closure might be over approximated, thus could lead to
  // dependency cycles in the privatization dependences. To make sure this
  // will not happen we remove all negative dependences after we computed
  // the transitive closure.
  TC_RED = isl_union_map_transitive_closure(isl_union_map_copy(RED), 0);

  // FIXME: Apply the current schedule instead of assuming the identity schedule
  //        here. The current approach is only valid as long as we compute the
  //        dependences only with the initial (identity schedule). Any other
  //        schedule could change "the direction of the backward dependences" we
  //        want to eliminate here.
  isl_union_set *UDeltas = isl_union_map_deltas(isl_union_map_copy(TC_RED));
  isl_union_set *Universe = isl_union_set_universe(isl_union_set_copy(UDeltas));
  isl_union_set *Zero = isl_union_set_empty(isl_union_set_get_space(Universe));
  isl_union_set_foreach_set(Universe, fixSetToZero, &Zero);
  isl_union_map *NonPositive = isl_union_set_lex_le_union_set(UDeltas, Zero);

  TC_RED = isl_union_map_subtract(TC_RED, NonPositive);

  TC_RED = isl_union_map_union(
      TC_RED, isl_union_map_reverse(isl_union_map_copy(TC_RED)));
  TC_RED = isl_union_map_coalesce(TC_RED);

  isl_union_map **Maps[] = {&RAW, &WAW, &WAR};
  isl_union_map **PrivMaps[] = {&PrivRAW, &PrivWAW, &PrivWAR};
  for (unsigned u = 0; u < 3; u++) {
    isl_union_map **Map = Maps[u], **PrivMap = PrivMaps[u];

    *PrivMap = isl_union_map_apply_range(isl_union_map_copy(*Map),
                                         isl_union_map_copy(TC_RED));
    *PrivMap = isl_union_map_union(
        *PrivMap, isl_union_map_apply_range(isl_union_map_copy(TC_RED),
                                            isl_union_map_copy(*Map)));

    *Map = isl_union_map_union(*Map, *PrivMap);
  }

  isl_union_set_free(Universe);
}

PlutoCompatData Dependences::build_pluto_data( ) {
  PlutoCompatData pcd;

  LOGD << "dep ana: creating compat data" ;

  isl_space* space = scop.getParamSpace();

  pcd.schedule = isl_schedule_get_map( scop.getSchedule() );
  LOGD << "dep ana: reads" ;
  pcd.reads = scop.getReads();
  LOGD << "dep ana: writes" ;
  pcd.writes = scop.getWrites();

  pcd.context = isl_set_copy(scop.getContext());
  pcd.empty = isl_union_map_empty(space);

  LOGD << "dep ana: domains" ;
  //pcd.domains = scop.getDomains();
  pcd.domains = scop.getNonKillDomains( );

  pcd.raw = isl_union_map_copy(RAW);
  pcd.war = isl_union_map_copy(WAR);
  pcd.waw = isl_union_map_copy(WAW);
  pcd.red = isl_union_map_copy(RED);

  return pcd;
}

PlutoCompatData Dependences::make_pluto_compatible( std::vector<int>& rename_table, PlutoCompatData& pcd ) {
  
  isl_space* space = scop.getParamSpace();

  LOGD << "writes before rename " << pcd.writes ;
  isl_union_map_dump(pcd.writes);

  LOGD << "domains before rename" ;
  isl_union_set_dump(pcd.domains);

  LOGD << "done writes before rename" ;
  if ( rename_table.size() > 0 ) {
    pcd.schedule = linearize_union_map( space, pcd.schedule, rename_table );
    pcd.reads = linearize_union_map( space, pcd.reads, rename_table );
    pcd.writes = linearize_union_map( space, pcd.writes, rename_table );
    pcd.raw = linearize_union_map( space, pcd.raw, rename_table );
    pcd.war = linearize_union_map( space, pcd.war, rename_table );
    pcd.waw = linearize_union_map( space, pcd.waw, rename_table );
    pcd.red = linearize_union_map( space, pcd.red, rename_table );
    pcd.domains = linearize_union_set( space, pcd.domains, rename_table );
  }
  LOGD << "writes after rename" ;
  isl_union_map_dump(pcd.writes);

  LOGD << "domains after rename" ;
  isl_union_set_dump(pcd.domains);

  return pcd;
}



// TODO one can improve this by not just fetching the tuple name but also the 
// variable that it writes to. i have no idea on how to do that but for the time beeing
// its ok to assume that if i find the statement that corresponds to this tuple name
// it will only have one reduction like memory access
// if a statement has more than one reduction like memory access it is most properbly wrong 
// since the c++ standard says that multiple updates to variables in one statement 
// will leed to undefined behaviour
// TODO also handle the type of the reduction operation
std::vector<PetReductionVariableInfo> Dependences::find_reduction_variables( ){

  std::vector<PetReductionVariableInfo> reduction_variables;

  auto pair = std::make_pair( &reduction_variables, this );
  typedef decltype( pair ) data_type;

  isl_union_map_foreach_map( RED, 
      [](isl_map* map, void* user)
      { 
	auto user_data = (data_type*) user;
	Dependences* dependences = user_data->second;
	int in = isl_map_n_in( map );
	int out = isl_map_n_out( map );
	int param = isl_map_n_param( map );
	LOGD << "depana: " << in << " " << out  << " " << param  ;
	const char* in_name = isl_map_get_tuple_name( map, isl_dim_in );
	LOGD << "depana: in name " << in_name ;
	const char* out_name = isl_map_get_tuple_name( map, isl_dim_out );
	if ( strcmp(in_name,out_name) != 0 ) {
	  LOGD << "depana warning: in and out name are not the same. never tested this case " ;
	  exit(-1);
	}

	auto* s = dependences->scop.getStmtByTupleName( in_name );

	if ( s ) {
          LOGD << "depana: domain of statement"  ;
          auto* domain = s->getDomain();
          isl_set_dump( domain );
          LOGD << "depana: intersect with domain"  ;
          auto* intersect_res = isl_map_intersect_domain(map, domain);
          isl_map_dump(intersect_res);
	  LOGD << "depana: found the corresponding statement"  ;
	  for( auto& MA : *s ){
            isl_map_dump( intersect_res );
	    if ( MA.isReductionLike() ) {
	      auto ba = MA.getBaseAddr();
	      const char* name = isl_id_get_name( ba );
	      LOGD << "depana: name " << name  << " storing result in vector ";
	      auto op_type = MA.getReductionType();
	      user_data->first->push_back( PetReductionVariableInfo{ in_name, name, (pet_op_type)op_type } );
	    }
	  }
	  
	}else{
	  LOGD << "depana error: could not find the statement by its id" ;
	  exit(-1);
	}


	return (isl_stat)0; 
      }
      ,
      &pair
       
  );

  return reduction_variables;

}

typedef std::pair<isl_set*, isl_schedule_node*> find_result;


#if 0
static isl_bool find_set_in_node( isl_schedule_node* node, void* user ) {
  find_result* fr = (find_result*)user;
  isl_set* set = fr->first;

  auto type = isl_schedule_node_get_type( node );
  std::cout << "  type " << type << std::endl;

}
#endif

static isl_bool find_set_in_schedule( isl_schedule_node* node, void* user ) {

  find_result* fr = (find_result*)user;
  isl_set* set = fr->first;

  auto type = isl_schedule_node_get_type( node );
  if ( type == isl_schedule_node_filter  ) {
    isl_schedule_node_dump( node );


    isl_union_set* filter = isl_schedule_node_filter_get_filter( node );
    //LOGD << "filter: " ;
    //isl_union_set_dump( filter );
    // skip all filter nodes with more than one set
    if ( isl_union_set_n_set( filter ) == 1 ) {
      auto* result = isl_union_set_intersect( isl_union_set_from_set(isl_set_copy(set)), filter );
      if ( isl_union_set_is_empty( result ) ){
	isl_union_set_free( result );
	LOGV << "this set does not contain this set" ;
      }else{
	isl_union_set_free( result );
	LOGV << "this set DOES contain this set" ;
	fr->second = isl_schedule_node_copy(node);
	// stop recursing
	return isl_bool_false;
      }
    }else{
      LOGV << "not considering this node since it has to have subnodes" ;
    }
  }
#if 0
  else{
    LOGD << " type of this schedule node is " << type ;
    isl_schedule_node_dump( node );
    if ( type == isl_schedule_node_band ) {
      LOGD << "is a band";
      auto* partial_schedule = isl_schedule_node_band_get_partial_schedule( node );
      LOGD << "partial schedule";
      isl_multi_union_pw_aff_dump( partial_schedule );
      auto members = isl_schedule_node_band_n_member( node );
      LOGD << "has n memebers = " << members;
      auto* um = isl_schedule_node_band_get_partial_schedule_union_map( node );
      LOGD << "UM:";
      isl_union_map_dump( um );
      auto* umi = isl_union_map_intersect_params(um, set);

      isl_schedule_node_foreach_descendant_top_down( node, &find_set_in_node, user );
    }
  }
#endif
  return isl_bool_true; 
}

// TODO get the position in the schedule
static isl_schedule_node* getScheduleNode( isl_schedule* schedule, isl_set* set ) {
  LOGD << "searching for :" ;
  isl_set_dump( set );
  //LOGD << "in schedule :" ;
  //isl_schedule_dump( schedule );
  find_result f = std::make_pair( set, nullptr );
  isl_schedule_foreach_schedule_node_top_down( schedule, &find_set_in_schedule, &f );
  return f.second;
}

static isl_set* get_source_from_map( isl_map* map ) {
  LOGD << "source: " ;
  isl_set* set = isl_map_domain( map );
  isl_set_dump( set );
  return set;
  
}

static isl_set* get_destination_from_map ( isl_map* map ) {
  LOGD << "destination: " ;
  isl_set* set = isl_map_range( map );
  isl_set_dump( set );
  return set;
}

typedef std::tuple<isl_schedule_node*, isl_schedule_node*, bool, bool> find_node_data;

static isl_bool find_nodes( isl_schedule_node* node, void* user ) {
  find_node_data* fnd = (find_node_data*) user;
  isl_schedule_node* a = std::get<0>(*fnd);
  isl_schedule_node* b = std::get<1>(*fnd);
  bool& is_before = std::get<2>(*fnd);
  bool& a_found = std::get<3>(*fnd);

#if 0
  LOGD << "a node" ;
  isl_schedule_node_dump( a ) ;

  LOGD << "b node" ;
  isl_schedule_node_dump( b ) ;

  LOGD << "n node" ;
  isl_schedule_node_dump( node ) ;
#endif

  if ( !a_found && isl_schedule_node_is_equal(node,a)  ) {
    a_found = true;
    LOGD << "a found" ;
    return isl_bool_true;
  }

  if ( a_found && isl_schedule_node_is_equal(node,b) ) {
    is_before = true;
    LOGD << "b found" ;
  }

  return isl_bool_true;
}

static bool is_before( isl_schedule* schedule, isl_schedule_node* a, isl_schedule_node* b ) {
  find_node_data fnd = std::make_tuple( a, b, false, false );
  isl_schedule_foreach_schedule_node_top_down( schedule, &find_nodes, &fnd );
  return std::get<2>(fnd);
}

typedef std::tuple< 
    isl_schedule_node*, // source
    isl_schedule_node*, // destination
    isl_union_map*,     // kill_statements
    isl_set*,           // filter for the range 
    bool,		// is_killed ?
    bool		// source found ?
    > KillStatementAnalysisData;

static isl_bool find_kill_statement( isl_schedule_node* node, void* user ) {
  auto ksad = (KillStatementAnalysisData*)user;

  isl_union_set* filter = nullptr;

  // check that we got a filter node 
  auto type = isl_schedule_node_get_type( node );
  if ( type == isl_schedule_node_filter  ) {
    filter = isl_schedule_node_filter_get_filter( node );
    // skip all filter nodes with more than one set
    if ( isl_union_set_n_set( filter ) != 1 ) {
      LOGD << "skipping this filter node since it has to have children" ;
      // recurse
      return isl_bool_true;
    }
  }else{
    return isl_bool_true;
  }

  // first find the source statement
  isl_schedule_node* source_node = std::get<0>(*ksad);
  bool& source_found = std::get<5>( *ksad );

  if ( !source_found && isl_schedule_node_is_equal( node, source_node ) ) {
    LOGD << "found the source statement heading for the destination statement" ;
    source_found = true;
    // dont recurse -> kill stmt has to be in sequence
    return isl_bool_false;
  }


  bool& is_killed = std::get<4>( *ksad );
#if 0
  // now search for the destination statement 
  // if we find it and it was not killed on route 
  // we are sure everything is ok
  if ( source_found && !is_killed && isl_schedule_node_is_equal( node, destination_node ) ){
    // TODO do i need this ?? 
  }
#endif

  // if the source was found
  // check wether we touch a kill statement 
  // and if this statement kills the range we are looking for 
  // set the kill flag to true
  if ( source_found && !is_killed ) {
    LOGV << "checking for killstatement " ;
    isl_union_map* kill_statements = std::get<2>(*ksad);
    LOGV << "kill statements are: " ;
    isl_union_map_dump( kill_statements );
    LOGV << "intersecting with filter: ";
    isl_union_set_dump( filter );
    isl_union_map* kills = isl_union_map_intersect_domain( isl_union_map_copy(kill_statements), filter ); 
    LOGV << "kills are:" ;
    isl_union_map_dump( kills );

    // check wether this statement is a kill_statement 
    if ( !isl_union_map_is_empty( kills ) ){
      // has to be one element
      if ( isl_union_map_n_map( kills ) != 1 ) {
	LOGV << "union map has != 1 element cant handle this" ;
	exit(-1);
      }

      isl_set* range = std::get<3>(*ksad);
      LOGV << "checking range:" ;
      isl_set_dump( range );
      isl_map* kill = isl_map_from_union_map( kills );
      isl_set* kill_range = isl_map_range( kill );
      LOGV << "with kill range:"  ;
      isl_set_dump( kill_range );
      
      isl_space* kill_space = isl_set_get_space(kill_range);
      LOGV << "kill range has following space";
      isl_space_dump( kill_space );

      isl_space* range_space = isl_set_get_space(range);
      LOGV << "range has following space";
      isl_space_dump( range_space );

      // now check that both ranges are the same 
      // TODO for arrays this does not work like expected 
      //isl_set* is_same = isl_set_intersect( isl_set_copy(range), kill_range );
      //if ( isl_set_is_empty( is_same ) ) {
      if ( isl_space_is_equal( range_space, kill_space ) ) {
	LOGV << "both ranges are identical setting is_killed true" ;
	is_killed = true;
	return isl_bool_false;
      }else{
	LOGV << "ranges are not identical";
      }
    }
  }

  return isl_bool_true;

}

static bool is_killed( 
    isl_schedule* schedule, 
    isl_schedule_node* a,
    isl_schedule_node* b,
    isl_union_map* kill_statements, 
    isl_set* range 
){
  LOGD << __PRETTY_FUNCTION__ ;
  // TODO intersect it with the kill statements on route from source to destination
  KillStatementAnalysisData ksad = std::make_tuple( a, b, kill_statements, range, false, false );
  // need to call this two times if source is after destination
  isl_schedule_foreach_schedule_node_top_down( schedule, &find_kill_statement, &ksad );
  isl_schedule_foreach_schedule_node_top_down( schedule, &find_kill_statement, &ksad );
  return std::get<4>(ksad);
}

// the schedule, the write statements, the kill_statements, the new map ...
typedef std::tuple< isl_schedule*, isl_union_map*, isl_union_map*, isl_union_map* > KillStatementsData;

void dump( isl_union_map* um ) {
  std::cerr << "is a isl_union_map" << std::endl;
  isl_union_map_dump ( um );
}

void dump( isl_union_set* us ) {
  std::cerr << "is a isl_union_set" << std::endl;
  isl_union_set_dump ( us );
}

void dump( isl_map* map ) {
  std::cerr << "is a isl_map" << std::endl;
  isl_map_dump ( map );
}

void dump( isl_set* set ) {
  std::cerr << "is a isl_set" << std::endl;
  isl_set_dump ( set );
}

void dump( isl_space* space ) {
  std::cerr << "is a isl_space" << std::endl;
  isl_space_dump ( space );
}

std::string isl_dim_to_str[] = { "isl_dim_cst", "isl_dim_param", " isl_dim_in", "isl_dim_out", "isl_dim_set/isl_dim_out", "isl_dim_div"};

void print_map_information( isl_map* map ) {

  std::cout << "information for :" << std::endl;
  dump (map);

  auto n_in = isl_map_n_in( map );
  auto n_out = isl_map_n_out( map );
  auto n_param = isl_map_n_param( map );

  std::cout << "Dimensions:" << std::endl;

  std::cout << "n in " << n_in << std::endl;
  std::cout << "n out " << n_out << std::endl;
  std::cout << "n param " << n_param << std::endl;

  std::cout << "Dimensions of (): " << std::endl;
  if ( n_in ){
    std::cout << "dim in " << isl_map_dim( map, isl_dim_in ) << std::endl;
  }

  if( n_out ){
    std::cout << "dim out " << isl_map_dim( map, isl_dim_out ) << std::endl;
  }

  if( n_param ){
    std::cout << "dim param " << isl_map_dim( map, isl_dim_param ) << std::endl;
  }

  std::cout << "Dimension Names:" << std::endl;
  for (int i = 0; i < n_in; ++i){
    std::cout << "dim in " << isl_map_get_dim_name( map, isl_dim_in, i )<< std::endl;
  }

  for (int i = 0; i < n_out; ++i){
    std::cout << "dim out " << isl_map_get_dim_name( map, isl_dim_out, i )<< std::endl;
  }

  for (int i = 0; i < n_param; ++i){
    std::cout << "dim param " << isl_map_get_dim_name( map, isl_dim_param, i )<< std::endl;
  }

  std::cout << "Has tuple id ?: " << std::endl;
  std::cout << "dim in(id) " << isl_map_has_tuple_id(map, isl_dim_in) << std::endl;
  std::cout << "dim out(id) " << isl_map_has_tuple_id(map, isl_dim_out) << std::endl;
  std::cout << "dim param(id) " << " not possible " << std::endl;

}

void print_space_information( isl_space* space, int recurse = 2 )
{
  
  std::cout << "information for :" << std::endl;
  dump (space);


  auto is_wrapping = isl_space_is_wrapping(space);
  auto is_domain_wrapping = isl_space_domain_is_wrapping(space);
  auto is_range_wrapping = isl_space_range_is_wrapping(space);

  std::cout << "is wrapping " << is_wrapping << std::endl;
  std::cout << "is domain wrapping " << isl_space_domain_is_wrapping(space) << std::endl;
  std::cout << "is range wrapping " << isl_space_range_is_wrapping(space) << std::endl;
  std::cout << "can curry " << isl_space_can_curry(space) << std::endl;
  std::cout << "can uncurry " << isl_space_can_uncurry(space) << std::endl;

  if ( is_wrapping ){
    std::cout << "unwrapping" << std::endl;
    auto unwrapped = isl_space_unwrap( isl_space_copy(space) );
    print_space_information( unwrapped );
  }

  auto can_curry = isl_space_can_curry(space);
  auto can_uncurry = isl_space_can_uncurry(space);

  if ( can_curry && recurse ) {
    std::cout << "curring" << std::endl;
    auto curried = isl_space_curry( isl_space_copy(space) );
    print_space_information( curried, recurse-1 );
  }

  if ( can_uncurry && recurse ) {
    std::cout << "uncurring" << std::endl;
    auto uncurried = isl_space_uncurry( isl_space_copy(space) );
    print_space_information( uncurried, recurse-1 );
  }

  auto can_zip = isl_space_can_zip( space );

  std::cout << "can zip " << can_zip << std::endl;

  std::cout << "Dimensions :" << std::endl;
  int dims[isl_dim_all];
  for (int i = 0; i < isl_dim_all; ++i){
    dims[i] = isl_space_dim( space, (isl_dim_type)i);
    std::cout << "dim i " << i << " " << dims[i] << std::endl;
  }

  std::cout << "Has ?: " << std::endl;
  std::cout << "tuple name in "  << " "  << isl_space_has_tuple_name(space, isl_dim_in) << std::endl;
  std::cout << "tuple name out "  << " "  << isl_space_has_tuple_name(space, isl_dim_out) << std::endl;
  std::cout << "tuple name set "  << " "  << isl_space_has_tuple_name(space, isl_dim_set) << std::endl;

  for (int j = 0; j < isl_dim_all; ++j){
    std::cout << "type " << isl_dim_to_str[j] << std::endl;
    for (int i = 0; i < dims[j]; ++i){
      std::cout << "  has dim name " << isl_space_has_dim_name( space, (isl_dim_type)j, i) << std::endl;
    }
  }

  auto has_tuple_name = [](isl_space* space, auto isl_dim ){
    auto has_tuple_name = isl_space_has_tuple_name( space, isl_dim );
    if ( has_tuple_name ) {
      std::cout << "tuple name for type " << isl_dim_to_str[(int)isl_dim] << " " << isl_space_get_tuple_name( space, isl_dim ) << std::endl;
    }
  };

  has_tuple_name( space, isl_dim_in );
  has_tuple_name( space, isl_dim_out );
  has_tuple_name( space, isl_dim_set );

  std::cout  << std::endl;

}


using PlainCooridnates = std::pair<isl_map*, std::vector<int>>;

PlainCooridnates extract_order ( isl_map* map ) {
  std::cout << __PRETTY_FUNCTION__ << std::endl ;
  auto space = isl_map_get_space( map );
  if ( space ) {
    dump(space);
  } 

  int n_out = isl_map_n_out( map );
  std::cout << "n in " << isl_map_n_in( map ) << std::endl;
  std::cout << "n out " << n_out << std::endl;
  std::cout << "n param " << isl_map_n_param( map ) << std::endl;

  std::cout << "out dim" << isl_map_dim( map, isl_dim_out) << std::endl;

  for (int i = 0; i < n_out; ++i){
    auto val = isl_map_plain_get_val_if_fixed( map, isl_dim_out, i ); 
    auto v = isl_val_get_num_si( val );
    auto is_nan = isl_val_is_nan( val );
    if ( is_nan == isl_bool_false ){
      std::cout << "v[" << i << "] " << v << std::endl;
    }else{
      std::cout << "v[" << i << "] " << -1  << std::endl;
    }
  }


  PlainCooridnates ret;

  auto& coordinates = ret.second;

  coordinates.resize(n_out);

  for (int i = 0; i < n_out; ++i){
    auto val = isl_map_plain_get_val_if_fixed( map, isl_dim_out, i ); 
    auto v = isl_val_get_num_si( val );
    auto is_nan = isl_val_is_nan( val );
    if ( is_nan == isl_bool_false ){
      coordinates[i] = v;
    }else{
      coordinates[i] = -1;
    }
  }

  auto& this_map = ret.first;

  this_map = map;

  std::cout << "returning from " << __PRETTY_FUNCTION__ << std::endl;
  return ret;
}


template < typename T >
isl_stat for_each_helper( T* element, void* user ){
  auto& f = *((std::function<isl_stat(T*)>*)user);
  isl_stat stat = f( element );
  return stat;
} 

void for_each( isl_union_set* uset, std::function<isl_stat(isl_set*)> functor)
{
  isl_union_set_foreach_set( uset, &for_each_helper<isl_set>, (void*)&functor); 
}

static isl_stat considerKillStatementsForMapNew( isl_map* map, void* user ) {

  auto kill_statements_data = (KillStatementsData*)user;
  isl_schedule* schedule = std::get<0>(*kill_statements_data);
  isl_union_map* writes = std::get<1>(*kill_statements_data);
  isl_union_map* kill_statements = std::get<2>(*kill_statements_data);
  isl_union_map* new_map = std::get<3>(*kill_statements_data);


  auto um_schedule = isl_schedule_get_map( schedule );
  LOGD << "schedule as map :";
  dump ( um_schedule );

  std::vector<PlainCooridnates> plain_coordinates;
  auto pair = std::make_pair((isl_set*)nullptr,&plain_coordinates);

  // TODO remove the pair it is not needed
  std::cout << "individual maps" << std::endl;
  isl_union_map_foreach_map( um_schedule, [](isl_map* map, void* user){ 
    if ( map ) {
      dump( map );
    }
    auto pair = (std::pair<isl_set*,std::vector<PlainCooridnates>*>*)user;
    PlainCooridnates pc = extract_order( map );
    pair->second->push_back( pc );
    return isl_stat_ok;
  }, &pair);

  int ctr = 0;
  for( auto& plain_coordinate : plain_coordinates ){
    std::cout << "got plain_coordinate " << ctr++ <<  std::endl;
  }
  
  if ( plain_coordinates.empty() ) return isl_stat_ok;

  // sanity check. all have to have the same dimensionality
  
  auto first_dims = plain_coordinates.front().second.size();

  ctr = 0;
  for( auto& plain_coordinate : plain_coordinates ){
    if ( first_dims != plain_coordinate.second.size() ) {
      std::cout << "dimensions differ in element " << ctr << std::endl;
    }
  }

  std::sort( begin(plain_coordinates), end(plain_coordinates), [&](PlainCooridnates& a, PlainCooridnates& b){ 
    //return recursive_greater(a.second,b.second, 0);
    return a.second < b.second;
  });

  std::cout << "sorted by coordinates" << std::endl;
  ctr = 0;
  for( auto& plain_coordinate : plain_coordinates ){
    dump( plain_coordinate.first );
    for( auto&& element : plain_coordinate.second ){
      std::cout << element << " ";
    }
    std::cout << std::endl;
  }

  // TODO find statement source and try to walk to statement destination
  
  auto find_statement_by_name = [&](const char* search_name){ 
    for( int i = 0 ; i < plain_coordinates.size() ; i++ ){
      auto statement = plain_coordinates[i].first;
      // TODO is source statement ?
      auto name = isl_map_get_tuple_name(statement, isl_dim_in );
      std::cout << "name " << name << std::endl;
      if ( strcmp( search_name, name ) == 0 ) {
        std::cout << "found source statement" << std::endl;
      }
    }
    return -1;
  };


  auto space = isl_map_get_space( map );
  //print_space_information( space );
  //dump ( space );

  auto source = get_source_from_map( isl_map_copy(map) );
  auto destination = get_destination_from_map( isl_map_copy(map) );

  //print_space_information( isl_set_get_space( source ) );
  //print_space_information( isl_set_get_space( destination ) );

  auto get_tuple_name_from_wrapped = [](isl_set* set){ 
    auto space = isl_set_get_space( set );
    if ( space ) {
      isl_space* unwrapped_space = space;
      auto dim_type = isl_dim_in;
      if ( isl_space_is_wrapping( space ) ) {
        unwrapped_space = isl_space_unwrap( space );
      }else{
        dim_type = isl_dim_out;
      }
      auto isl_tuple_name = isl_space_get_tuple_name( unwrapped_space, dim_type );
      return isl_tuple_name;
    }else{
      std::cout << "FATAL: could not get the space for the set " << set << std::endl;
    }
    return (const char*)nullptr;
  };

  auto source_name = get_tuple_name_from_wrapped( source );
  auto destination_name = get_tuple_name_from_wrapped( destination );

  std::cout << "source " << source_name << " destination " << destination_name << std::endl;

  isl_union_set* kill_domains = isl_union_map_domain( isl_union_map_copy( kill_statements ) );

  auto is_killed = [&](isl_set* domain ){ 
    bool is_kill = false;
    // find out if this domain is a kill domain
    for_each( kill_domains, [&](isl_set* kill_domain){ 
      auto inter = isl_set_intersect( isl_set_copy(kill_domain), isl_set_copy(domain) ); 
      if ( !isl_set_is_empty( inter ) ) {
        is_kill = true;
        return isl_stat_error; 
      }
      return isl_stat_ok;
    } );
    return is_kill; 
  };

  bool found_source = false;

  auto from_source_to_destination = [&](auto source, auto destination, auto plain_coordinates ){ 
    for( auto& plain_coordinate : plain_coordinates ){
      auto statement = plain_coordinate.first;
      auto domain = isl_map_domain( statement );
      auto tuple_name = get_tuple_name_from_wrapped( domain ); 
      std::cout << "tuple_name " << tuple_name << std::endl;

      if ( std::string(tuple_name) == std::string(source) ) {
        found_source = true;
        continue;
      }

      // if we found the source and we are now
      // heading to the destination statement
      if ( found_source ) {
        if ( std::string(tuple_name) == std::string(destination) ) {
          break;
        }
        // if this is a kill statement for this dependency 
        if ( is_killed( domain ) ) {
          return tuple_name;
        }
      }
    }
    return (const char*)nullptr;
  };

  auto was_killed = from_source_to_destination( source_name, destination_name, plain_coordinates );

  if ( was_killed == nullptr ) {
    isl_union_map_add_map( new_map, map );
  }else{
    std::cout << "dependency from " << source_name << " to " << destination_name << " was killed" << std::endl;
  }

  return isl_stat_ok;
}


static isl_stat considerKillStatementsForMap( isl_map* map, void* user ) {

  auto kill_statements_data = (KillStatementsData*)user;
  isl_schedule* schedule = std::get<0>(*kill_statements_data);
  isl_union_map* writes = std::get<1>(*kill_statements_data);
  isl_union_map* kill_statements = std::get<2>(*kill_statements_data);
  isl_union_map* new_map = std::get<3>(*kill_statements_data);

  // i need source and targets from the map 
  auto source = get_source_from_map( isl_map_copy(map) );
  auto destination = get_destination_from_map( isl_map_copy(map) );

  auto schedule_node_source = getScheduleNode( schedule, source );
  auto schedule_node_destination = getScheduleNode( schedule, destination );

  if ( !schedule_node_source ) {
    LOGD << "did not get schedule node for source" ;
    isl_union_map_add_map( new_map, map );
    return (isl_stat)0;
  }

  if ( !schedule_node_destination ) {
    LOGD << "did not get schedule node for destination" ;
    isl_union_map_add_map( new_map, map );
    return (isl_stat)0;
  }

  // the destination is the write statement in a write after read
  isl_union_set* filter = isl_schedule_node_filter_get_filter( schedule_node_destination ); 

  // get the entry from the writes 
  isl_union_map* filtered_writes = isl_union_map_intersect_domain( isl_union_map_copy(writes), filter );
  LOGD << "filter statement is ";
  isl_union_map_dump( filtered_writes );

  // since its possible that there are multiple writes in the same statement ( althoug c and c++ forbid this )
  if ( isl_union_map_n_map( filtered_writes ) == 1 ) {  
    isl_map* filtered_write = isl_map_from_union_map( filtered_writes );

    // get the range from this map ( its the thing the statement is writing on )
    isl_set* range = isl_map_range( filtered_write );
    LOGD << "filter range is:";
    isl_set_dump ( range );

    // if the source statement is before the destination statement its ok 
    // but if its vice versa one has to check the kill statements 
    if ( is_before( schedule, schedule_node_source, schedule_node_destination ) ) {
      LOGD << "destination is after source -> no next iter" ;
    }else{
      LOGD << "destination is before source -> next iter" ;
      bool isKilled = is_killed( 
	  schedule, 
	  schedule_node_source, 
	  schedule_node_destination, 
	  kill_statements, 
	  range 
      );

      if ( isKilled ) {
	LOGD << "the write operation was killed by a kill statement on route to the destination"
	 << " you can delete this dependency" ;
	// return prematurely to not add this map to the new union map
	return (isl_stat)0;
      }
    }

  }else{
    LOGD << "can not handle multiple writes in one statement -> not implemented" ;
    exit(-1);
  }

  isl_union_map_add_map( new_map, map );

  return (isl_stat)0; 
}

isl_union_map* Dependences::considerKillStatements( isl_union_map* DEPS, 
    isl_schedule* schedule, 
    isl_union_map* writes, 
    isl_union_map* kill_statements 
){
  LOGD << __PRETTY_FUNCTION__ << " begin " ;
  isl_space* space = isl_union_map_get_space( DEPS );
  isl_union_map* new_deps = isl_union_map_empty( space );
  KillStatementsData ksd = std::make_tuple( schedule, writes, kill_statements, new_deps );
  // iterate over all dependencies
  //isl_union_map_foreach_map( DEPS , &considerKillStatementsForMap, &ksd );
  isl_union_map_foreach_map( DEPS , &considerKillStatementsForMapNew, &ksd );

  LOGD << "old deps:" ;
  isl_union_map_dump( DEPS );
  LOGD << "new deps:" ;
  isl_union_map_dump( std::get<3>(ksd ) );
  LOGD << __PRETTY_FUNCTION__ << " end " ;

  return std::get<3>(ksd);
}


// TODO tests isl ast generation
void Dependences::codegen(){

  LOGD << "building isl ast from context";
  auto build = isl_ast_build_from_context(isl_set_universe(scop.getParamSpace()));
  LOGD << "building isl ast from schedule";
  auto node = isl_ast_build_node_from_schedule( build, isl_schedule_copy(scop.getSchedule()) );

  // a printer to stderr
  auto printer = isl_printer_to_file( IslCtx, stderr );
  printer = isl_printer_set_output_format( printer, ISL_FORMAT_C );

  printer = isl_printer_print_ast_node( printer, node );



}

unsigned int 
Dependences::getSourceLocationByTupleName( std::string tuple_name ){
  auto* s = scop.getStmtByTupleName( tuple_name );
  return s->getSourceLocation();
}
