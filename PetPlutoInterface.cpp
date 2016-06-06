

#include "PetPlutoInterface.hpp"
#include "dependency_analysis.h"
#include "pluto_codegen_cxx.hpp"
#include "pluto_compat.h"
#include "pet_cxx.h"
#include "pet.h"

#include <chrono>
#include <iostream>

using namespace std;

extern "C"{
// TODO this has to go into the libpluto header
int pluto_schedule_pluto( PlutoProg* prog, PlutoOptions* options );
}

extern "C"{
  // TODO this has to go into one of plutos headers perhaps libpluto
  // TODO rename this to isl_to_plutp_prog
  PlutoProg* pluto_compute_deps( isl_union_map* schedule, 
      isl_union_map* read, 
      isl_union_map* write, 
      isl_union_map* empty, 
      isl_union_set* domain,
      isl_set* context,
      PlutoOptions* options,
      isl_union_map* raw,
      isl_union_map* war,
      isl_union_map* waw,
      isl_union_map* red
  );
}

using pluto_codegen_cxx::StatementInformation;



PetPlutoInterface::PetPlutoInterface( 
    std::set<std::string>& _header_includes, 
    CodeGenerationType _emit_code_type, 
    bool _write_cloog_file 
  ) : 
  header_includes(_header_includes),
  emit_code_type(_emit_code_type),
  write_cloog_file(_write_cloog_file)
{

}

void PetPlutoInterface::build_rename_table( isl_union_set* domains, std::vector<int>& table ) {
  
  // get the highest number
  int max_id = -1;
  isl_union_set_foreach_set(domains, 
      []( __isl_take isl_set* set, void* user ){
	std::cerr << "Line " << __LINE__ << " " << __FILE__ << std::endl;
	int* max_id = (int*) user;

	/* A statement's domain (isl_set) should be named S_%d */
	const char *name = isl_set_get_tuple_name(set);
	assert(isdigit(name[2]));
	int id = atoi(&name[2]);
	if ( id > *max_id ) {
	  *max_id = id;
	}
	return (isl_stat)0;
      }, 
      &max_id
  );
  if ( max_id <= 0 ) return;

  // for half open range usage
  max_id++;

  std::cerr << "plugin: max id " << max_id << std::endl;
  table.resize(max_id);
  int new_id = 0;
  std::fill( begin(table), end(table), -1 );

  // i cannot assume that the domains are in order so i have to search through the list
  for (int i = 0; i < max_id; ++i){
    std::pair<int,int> find_id = std::make_pair( i, -1 );
    std::cerr << "plugin: who has " << i << std::endl;
    isl_union_set_foreach_set(domains, 
	[]( __isl_take isl_set* set, void* user ){

	  std::pair<int,int>* find_id = (std::pair<int,int>*) user;
  
	  const char *name = isl_set_get_tuple_name(set);
	  assert(isdigit(name[2]));
	  int id = atoi(&name[2]);

	  std::cerr << "plugin: this is " << id << std::endl;

	  if ( find_id->first == id ) {
	    std::cerr << "plugin: found id " << id << " at pos " << find_id->first << std::endl;
	    find_id->second = id;
	    return (isl_stat)1;
	  }
	  return (isl_stat)0;   
	}, 
	&find_id
    );
    if ( find_id.second != -1 ) {
      table[find_id.second] = new_id++;
    }
  }

  std::cerr << "rename table: " << std::endl;
  for (int i = 0; i < max_id; ++i){
    std::cerr << i << " " << table[i] << std::endl;
  }

  // if there is no change simply clear the table and do nothing
  for (int i = 0; i < max_id; ++i){
    if ( table[i] != i ) return ;    
  }
  table.clear();
  
}

isl_union_set* PetPlutoInterface::collect_non_kill_domains(struct pet_scop *scop )
{
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

// needed to call c++ delete and not c free
static void delete_statement_information( void* user ){
  StatementInformation* sinfo = (StatementInformation*)user;
  delete sinfo;
}

struct AddInfoHelper {

  AddInfoHelper( 
      isl_union_set* _result, 
      std::vector<std::string>& _statement_texts,
      std::unique_ptr<std::map<std::string,std::string>>& _call_texts,
      std::vector<PetReductionVariableInfo>& _reduction_variables_for_tuple_names    
  ) :
    result(_result),
    statement_texts(_statement_texts),
    call_texts(_call_texts),
    reduction_variables_for_tuple_names(_reduction_variables_for_tuple_names)
  {
  }

  isl_union_set* result;
  std::vector<std::string>& statement_texts;
  std::unique_ptr<std::map<std::string,std::string>>& call_texts;
  std::vector<PetReductionVariableInfo>& reduction_variables_for_tuple_names;
};


struct PlutoRedcutionVariableInfo {
  explicit PlutoRedcutionVariableInfo( PetReductionVariableInfo& p ) {
    statement = p.statement;
    var_name = p.var_name;  
    // TODO map pet operations to pluto reduction operations
    if ( p.operation == pet_op_add_assign ) {
      std::cerr << "plugin: converted to pluto + sum" << std::endl;
      operation = StatementInformation::REDUCTION_SUM;
      return;
    } 
    if ( p.operation == pet_op_mul_assign ) {
      std::cerr << "plugin: converted to pluto + mul" << std::endl;
      operation = StatementInformation::REDUCTION_MUL;
      return;
    } 

    std::cerr << "plugin: dont know this reduction type " << p.operation << std::endl;
    exit(-1);
  }
  std::string statement;
  std::string var_name;
  pluto_codegen_cxx::StatementInformation::ReductionOperation operation;
};



// TODO make all of this get the information from statement_map and call_map or however they are called
static isl_stat add_info_to_id( __isl_take isl_set* set, void* user ) {

  auto user_data = (AddInfoHelper*) user;

  if ( auto tuple_id = isl_set_get_tuple_id( set ) ) {
    auto name = isl_id_get_name( tuple_id );

    // extract the number from the tuple id 
    assert(isdigit(name[2]));
    int id = atoi(&name[2]);

    // get the entry from the statement texts
    auto statement_text = user_data->statement_texts[id];

    auto ctx = isl_id_get_ctx( tuple_id );
    StatementInformation* sinfo = new StatementInformation();

    // add information from the statement table 
    sinfo->statement_text = statement_text;
    
    for( auto& rvar_info : user_data->reduction_variables_for_tuple_names ){
      std::cerr << "plugin: " << rvar_info.statement << " " << name << std::endl;
      if ( name == rvar_info.statement ) {
	PlutoRedcutionVariableInfo p(rvar_info);
	sinfo->reductions.insert( std::make_pair( p.var_name, p.operation ) );
      }
    }
    

    auto new_id = isl_id_alloc( ctx, name, sinfo );
    new_id = isl_id_set_free_user( new_id, &delete_statement_information ); 

    auto new_set = isl_set_set_tuple_id( set, new_id );
    isl_union_set_add_set( user_data->result, new_set );
    return (isl_stat)0;
  }

  std::cerr << "plugin: this should never happen" << std::endl;
  exit(-1);
  // add the original if nothing changes
  isl_union_set_add_set( user_data->result, set );
  return (isl_stat)0;
}


isl_union_set* add_extra_infos_to_ids( 
    isl_space* space, 
    isl_union_set* sets, 
    std::vector<std::string>& statement_texts, 
    std::unique_ptr<std::map<std::string,std::string>>& call_texts,
    std::vector<PetReductionVariableInfo>& reduction_variables_for_tuple_names    
  ) {

  AddInfoHelper helper( isl_union_set_empty( space ) ,
      statement_texts,
      call_texts,
      reduction_variables_for_tuple_names 
  );
  isl_union_set_foreach_set( sets, &add_info_to_id, &helper );
  isl_union_set_dump( helper.result );
  return helper.result;
}

PlutoProg* PetPlutoInterface::compute_deps( 
    pet_scop* pscop, 
    PlutoOptions* options, 
    std::vector<std::string>& statement_texts,
    std::unique_ptr<std::map<std::string,std::string>>& call_texts ) 
  {

  std::cerr << "plugin: building rename table" << std::endl;
  isl_union_set* domains = collect_non_kill_domains( pscop );
  std::vector<int> rename_table;
  build_rename_table( domains, rename_table );
  std::cerr << "plugin: done building rename table" << std::endl;

  std::cerr << "plugin: starting to calculate the dependencies" << std::endl;
  //Dependences dependences( pscop );
  Dependences dependences( pscop );

  auto reduction_variables_for_tuple_names = dependences.find_reduction_variables();
  std::cerr << "plugin: r vars from dep ana " << reduction_variables_for_tuple_names.size() << std::endl;

  std::cerr << "plugin: building pluto data (non compatible) " << std::endl;
  // build the data that will not be linear
  auto pluto_compat_data = dependences.build_pluto_data( );

  std::cerr << "plugin: adding info to ids (non compatible) " << std::endl;
  // add information that corresponds to this data
  pluto_compat_data.domains = add_extra_infos_to_ids( isl_set_get_space(pscop->context), 
      pluto_compat_data.domains, 
      statement_texts, 
      call_texts,
      reduction_variables_for_tuple_names
  );

  std::cerr << "plugin: making pluto data compatible" << std::endl;
  // reorder all to make it pluto compatible
  dependences.make_pluto_compatible( rename_table, pluto_compat_data );


  if ( dependency_analysis_style == DependencyAnalysisType::PollyLike ) {
    std::cerr << "plugin: calling pluto_compute_deps" << std::endl;
    // TODO the kill statements are not respected in isls dependency analysis 
    //      this needs to be taken into account in order to make scoped variables work like expected
    return pluto_compute_deps( 
	pluto_compat_data.schedule, 
	pluto_compat_data.reads, 
	pluto_compat_data.writes, 
	pluto_compat_data.empty, 
	pluto_compat_data.domains, 
	pluto_compat_data.context, 
	options, 
	pluto_compat_data.raw,  
	pluto_compat_data.war,  
	pluto_compat_data.waw,  
	pluto_compat_data.red 
    );
  }else{
    isl_union_map* schedule= isl_schedule_get_map(pscop->schedule);
    isl_union_map* read = pet_scop_collect_may_reads(pscop);
    isl_union_map* write = pet_scop_collect_must_writes(pscop);
    isl_union_map* empty = isl_union_map_empty(isl_set_get_space(pscop->context));
    isl_set* context = isl_set_copy(pscop->context);

    auto space = isl_set_get_space( pscop->context );

    if ( rename_table.size() > 0 ) {
      domains = linearize_union_set( space, domains, rename_table );
      schedule = linearize_union_map( space, schedule, rename_table );
      read = linearize_union_map( space, read, rename_table );
      write = linearize_union_map( space, write, rename_table );
      empty = linearize_union_map( space, empty, rename_table );
    }

    reduction_variables_for_tuple_names.clear();

    domains = add_extra_infos_to_ids( 
      isl_set_get_space(pscop->context),  
      domains, 
      statement_texts, 
      call_texts,
      reduction_variables_for_tuple_names
    );

    return pluto_compute_deps( schedule,
			       read,
			       write,
			       empty,
			       domains,
			       context,
			       options,
			       nullptr,
			       nullptr,
			       nullptr,
			       nullptr
    );
  }

}


PlutoProg* PetPlutoInterface::pet_to_pluto_prog(pet_scop* scop, PlutoOptions* pluto_options, std::vector<std::string>& statement_texts ,std::unique_ptr<std::map<std::string,std::string>>& call_texts ){
  PlutoProg* prog =  compute_deps( scop, pluto_options, statement_texts, call_texts ) ;
  std::cerr << "plugin: pluto program generated"  << std::endl;
  return prog;
}

static pluto_codegen_cxx::EMIT_CODE_TYPE to_pluto_emit_type( CodeGenerationType cgt ) {
  if ( cgt == CodeGenerationType::ACC ) {
    return pluto_codegen_cxx::EMIT_ACC;
  }
  if ( cgt == CodeGenerationType::OMP ) {
    return pluto_codegen_cxx::EMIT_OPENMP;
  }
  if ( cgt == CodeGenerationType::CILK ) {
    return pluto_codegen_cxx::EMIT_CILK;
  }
  if ( cgt == CodeGenerationType::TBB ) {
    return pluto_codegen_cxx::EMIT_TBB;
  }
  if ( cgt == CodeGenerationType::HPX ) {
    return pluto_codegen_cxx::EMIT_HPX;
  }
}

bool PetPlutoInterface::create_scop_replacement(  
    pet_scop* scop, 
    std::vector<std::string>& statement_texts,
    std::unique_ptr<std::map<std::string,std::string>>& call_texts
  ) {

  pet_scop_align_params( scop );

  auto begin_pluto = std::chrono::high_resolution_clock::now();

  // find prallelism
  PlutoOptions* pluto_options = pluto_options_alloc(); // memory leak if something goes wrong
  pluto_options->parallel = true;
  pluto_options->debug = true;
  pluto_options->isldep = true;

  std::cerr << "generating pluto program from pet" << std::endl;
  auto prog = pet_to_pluto_prog(scop, pluto_options, statement_texts, call_texts);
  if ( !prog ) {
    std::cerr << "could not generate a pluto program from the given pet_scop" << std::endl;
    // TODO memory leak put everything into unique_ptr
    // TODO need proper error handling no replacement must be generated
    return false;
  }else{
    std::cerr << "done generating pluto program from scop" << std::endl;
  }

  std::cerr << "schedule pluto prog" << std::endl;
  
  // the pluto_function returns a number that indicated how many loops are parallel 
  int parallel_loops = pluto_schedule_pluto( prog, pluto_options );
  std::cerr << "schedule_pluto done " << std::endl;

  auto end_pluto = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> diff = end_pluto-begin_pluto;
  std::cerr << "pluto time consumption " << diff.count() << " s" << std::endl;

  if ( parallel_loops <= 0 ) {
    std::cerr << "loop is not parallel" << std::endl;
#if 0
    // TODO emit diagnostic on why its not parallel
    // TODO run sequential STL algorithm matcher 
    auto begin_analyzer = std::chrono::high_resolution_clock::now();
    {
      stdlib_matchers::analyze( for_stmt, SM, ctx_clang, false );
    }
    auto end_analyzer = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end_analyzer-begin_analyzer;
    std::cerr << "analyzer time consumption " << diff.count() << " s" << std::endl;
#endif
    return false;
  }

  // at this point we know that the loop is parallel 

  pet_scop_dump( scop );

  //auto call_texts = get_call_texts( scop , sloc_file, SM, for_stmt );

  std::stringstream outfp;
  auto begin_codegen = std::chrono::high_resolution_clock::now();

  if ( pluto_codegen_cxx::pluto_multicore_codegen( outfp, prog, statement_texts, to_pluto_emit_type(emit_code_type), write_cloog_file, *call_texts, header_includes ) == EXIT_FAILURE ) {
    // stop if codegeneration failed
    return "";
  }

  auto end_codegen = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> diff_cg = end_codegen-begin_codegen;
  std::cerr << "codegen time consumption " << diff_cg.count() << " s" << std::endl;

  std::cerr << outfp.str() << std::endl;
  replacement = outfp.str();

  return true;
}
