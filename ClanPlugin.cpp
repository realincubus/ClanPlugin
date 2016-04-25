//===-  islClan.cpp ---------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Example clang plugin which simply prints the names of all the top-level decls
// in the input file.
//
//===----------------------------------------------------------------------===//

#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include "llvm/Support/raw_ostream.h"
#include <fstream>
#include <chrono>
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <iostream>
#include <sstream>
#include <map>
#include <fstream>
#include <string>
#include <thread>
#include <signal.h>
#include <setjmp.h>
#include <map>
#include <clang/AST/AST.h>
#include "stdlib_matchers.hpp"
#include <memory>
#include <map>

#include <isl/options.h>
#include <isl/arg.h>
#include <isl/flow.h>
#include <isl/map.h>
#include <isl/set.h>
#include <isl/ctx.h>

#include <libpluto.h>
#include <pluto_codegen_cxx.hpp>

#include "pet.h"
#include "pet_cxx.h"

extern "C"{
// TODO this has to go into the libpluto header
int pluto_schedule_pluto( PlutoProg* prog, PlutoOptions* options );
}



using namespace clang;
using namespace clang::ast_matchers;

namespace {

extern "C"{
  // TODO this has to go into one of plutos headers perhaps libpluto
  // TODO rename this to isl_to_plutp_prog
  PlutoProg* pluto_compute_deps( isl_union_map* schedule, 
      isl_union_map* read, 
      isl_union_map* write, 
      isl_union_map* empty, 
      isl_union_set* domain,
      isl_set* context,
      PlutoOptions* options 
  );
}


struct set_rename_data {
    isl_union_set* new_set;
    std::vector<int>* rename_table;
};

struct map_rename_data {
    isl_union_map* new_map;
    std::vector<int>* rename_table;
};


// let the domain names be in accending order without gaps
isl_union_set* linearize_domains( pet_scop* pscop, isl_union_set* domains, std::vector<int>& rename_table ) {
  set_rename_data user_data;
  // start with 0 
  isl_union_set* new_domain = isl_union_set_empty( isl_set_get_space(pscop->context) );

  user_data.new_set = new_domain; 
  user_data.rename_table = &rename_table;

  isl_union_set_foreach_set(domains, 
      []( __isl_take isl_set* set, void* user ){
	  set_rename_data* user_data = (set_rename_data*)(user);

	  const char *name = isl_set_get_tuple_name(set);
	  char *new_name = (char*)malloc(sizeof(const char) * 10 );

	  // extract name and change it with the rename table
	  assert(isdigit(name[2]));
	  int id = atoi(&name[2]);

	  sprintf( new_name, "S_%d", (*user_data->rename_table)[id] );

	  std::cerr << "renaming from " << name << " to " << new_name << std::endl;    

	  auto new_isl_set = isl_set_set_tuple_name(set, new_name );
	  isl_set_dump( new_isl_set );
	  const char *set_name = isl_set_get_tuple_name(new_isl_set);
	  std::cerr << "done renaming new name is " << set_name << std::endl;    

	  isl_union_set_add_set( user_data->new_set, new_isl_set );

	  return (isl_stat)0;    
      }, 
      &user_data
  );
  return new_domain;
}

isl_union_map* linearize_union_map( pet_scop* pscop, isl_union_map* schedule, std::vector<int>& rename_table){
  map_rename_data user_data;
  isl_union_map* new_map = isl_union_map_empty( isl_set_get_space(pscop->context) );
  user_data.new_map = new_map; 
  user_data.rename_table = &rename_table;

  isl_union_map_foreach_map(schedule, 
      []( __isl_take isl_map* map, void* user ) {
	map_rename_data* user_data = (map_rename_data*)(user);

	isl_dim_type t = isl_dim_in;
	const char *name = isl_map_get_tuple_name(map,t);
	char *new_name = (char*)malloc(sizeof(const char) * 10 );

	assert(isdigit(name[2]));
	int id = atoi(&name[2]);

	sprintf( new_name, "S_%d", (*user_data->rename_table)[id] );
	std::cerr << "renaming from " <<  name << " to " << new_name << std::endl;    
	
	isl_map_dump( map );
	auto new_isl_map = isl_map_set_tuple_name(map,t, new_name );
	isl_map_dump( new_isl_map );
	const char *set_name = isl_map_get_tuple_name(new_isl_map, t );
	std::cerr << "done renaming" << std::endl;    

	isl_union_map_add_map( user_data->new_map, new_isl_map );

	return (isl_stat)0;    
      }, 
      &user_data
  ); 

  return new_map;
}

void build_rename_table( isl_union_set* domains, std::vector<int>& table ) {
  
  // get the highest number
  int max_id = -1;
  isl_union_set_foreach_set(domains, 
      []( __isl_take isl_set* set, void* user ){
	printf("Line %d %s\n",__LINE__,__FILE__);
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

  table.resize(max_id);
  int new_id = 0;
  std::fill( begin(table), end(table), -1 );

  // i cannot assume that the domains are in order so i have to search through the list
  for (int i = 0; i < max_id; ++i){
    std::pair<int,int> find_id = std::make_pair( i, -1 );
    isl_union_set_foreach_set(domains, 
	[]( __isl_take isl_set* set, void* user ){

	  std::pair<int,int>* find_id = (std::pair<int,int>*) user;
  
	  const char *name = isl_set_get_tuple_name(set);
	  assert(isdigit(name[2]));
	  int id = atoi(&name[2]);
	  if ( find_id->first == id ) {
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

static isl_stat correct_alignment( __isl_take isl_map *schedule, void* user ){
  std::pair<pet_scop*,isl_union_map*>* user_data = (std::pair<pet_scop*,isl_union_map*>*)user;

  // correcting schedule 
  auto new_schedule = isl_map_align_params(schedule, isl_set_get_space(user_data->first->context));
  isl_union_map_add_map( user_data->second, new_schedule );
  return (isl_stat)0;
}

#if 1
PlutoProg* compute_deps( pet_scop* pscop, PlutoOptions* options ) {

  isl_union_map* schedule= isl_schedule_get_map(pscop->schedule);
  isl_union_map* read = pet_scop_collect_may_reads(pscop);
  isl_union_map* write = pet_scop_collect_must_writes(pscop);
  isl_union_map* empty = isl_union_map_empty(isl_set_get_space(pscop->context));
  isl_union_set* domains = pet_scop_collect_domains( pscop );

  std::vector<int> rename_table;
  build_rename_table( domains, rename_table );

  if ( rename_table.size() > 0 ) {
    domains = linearize_domains( pscop, domains, rename_table );
    schedule = linearize_union_map( pscop, schedule, rename_table );
    read = linearize_union_map( pscop, read, rename_table );
    write = linearize_union_map( pscop, write, rename_table );
    empty = linearize_union_map( pscop, empty, rename_table );
  }

  isl_set* context = pscop->context;
  std::cerr << "calling pluto_compute_deps with this context " << std::endl;
  isl_set_dump( pscop->context );

  // TODO plutos pet branch says that the schedule is not aligned with 
  //      the context. i dont know whether this is still needed after 
  //      pet also changed since the pet branch implementation
#if 0
  isl_union_map* new_schedule = isl_union_map_empty(isl_set_get_space(pscop->context));
  std::pair<pet_scop*,isl_union_map*> user_data = std::make_pair( pscop, new_schedule );
  isl_union_map_foreach_map( schedule, correct_alignment, &user_data );

  schedule = new_schedule;
#endif

  // TODO pluto complains about non unified basic sets in the domains
  //      to overcome this i will simply unify them in isl before passing them to pluto
  
  // loop over all domains 
  isl_union_set_foreach_set( domains, 
      []( __isl_take isl_set* set, void* user_data ) {
	std::cerr << "isl set before unification" << std::endl;
	isl_set_dump( set );
	auto rrs = isl_set_remove_redundancies( set );
	std::cerr << "rrs" << std::endl;
	isl_set_dump( rrs );

	auto cset = isl_set_coalesce( set );
	auto n_set = isl_set_n_basic_set( set );
	std::cerr << "coalesce result with n basic sets " << n_set  << std::endl;
	isl_set_dump( cset );

	auto iset = isl_set_union( isl_set_copy(set), isl_set_copy(set) );
	auto ni_set = isl_set_n_basic_set( iset );
	std::cerr << "intersection result " << ni_set  << std::endl;
	isl_set_dump ( iset );

#if 1
	isl_set* uni = nullptr;
	isl_set_foreach_basic_set ( set , 
	    [] ( __isl_take isl_basic_set* bset, void* user_data ) {
	      isl_set** uni = (isl_set**)user_data;
	      std::cerr << "basic set: "   << std::endl;
	      isl_basic_set_dump( bset );
#if 0
	      if ( *uni == nullptr ) {
		std::cerr << "setting first basic set" << std::endl;
		// promote the basic set to a set
		auto bset_set = isl_set_from_basic_set( bset );
		*uni = bset_set;
	      }else{
		std::cerr << "first set already set -> unionizing" << std::endl;
		auto bset_set = isl_set_from_basic_set( bset );
		isl_set* new_bset = isl_set_union( *uni, bset_set );
		auto n_bset = isl_set_n_basic_set( new_bset );
		std::cerr << "dumping the union with n basic sets " << n_bset << std::endl;
		isl_set_dump( new_bset );
		std::cerr << "done dumping the union" << std::endl;

	      }
#endif
	      return (isl_stat)0;
	    },
	    &uni
	);
	std::cerr << std::endl << std::endl;
#endif
	return (isl_stat)0;
      },
      nullptr
  );

  return pluto_compute_deps( schedule, read, write, empty, domains, context, options );
}
#endif


PlutoProg* pet_to_pluto_prog(pet_scop* scop, PlutoOptions* pluto_options){
  PlutoProg* prog =  compute_deps( scop, pluto_options ) ;
  return prog;
}


class DeclRefVisitor
  : public clang::RecursiveASTVisitor<DeclRefVisitor> {
public:

  DeclRefVisitor( std::vector<NamedDecl*>& _iterators, SourceLocation _begin, SourceLocation _end, SourceManager& _SM ):
    iterators(_iterators),
    begin(_begin),
    end(_end),
    SM(_SM)
  {

  }

  bool VisitDeclRefExpr( const DeclRefExpr* declRefExpr ) {

    auto decl_ref_loc_start = declRefExpr->getLocStart();
    if ( SM.isBeforeInTranslationUnit( decl_ref_loc_start , begin ) ) return true;
    if ( SM.isBeforeInTranslationUnit( end , decl_ref_loc_start ) ) return true;

    std::cerr << "visited a node" << std::endl;
    for( auto i = 0 ; i < iterators.size() ; i++ ){
      auto& iterator = iterators[i];
      if ( declRefExpr->getDecl() == iterator ) {
	std::cerr << "found a reference" << std::endl;
	// push_this occurence to the list of excludes for this iterator
	exclude_ranges.push_back( make_pair( declRefExpr->getSourceRange(), std::to_string(i)) );
	return true;
      }
    }
    
    // everything that is not an iterator passes this point
    return true;
  }
  std::vector<std::pair<SourceRange,std::string>> exclude_ranges;
private:
  std::vector<NamedDecl*>& iterators;
  SourceLocation begin;
  SourceLocation end;
  SourceManager& SM;
};

int ctr = 0;

std::vector<NamedDecl*> get_parameters_for_pet_stmt( pet_stmt* stmt ) {
    // get the iteration space of this statement
    isl_space* space = pet_stmt_get_space( stmt );
    int in_param = isl_space_dim(space, isl_dim_in);
    int out_param = isl_space_dim(space, isl_dim_out);

    std::cerr << "in_param " << in_param << std::endl;
    std::cerr << "out_param " << out_param << std::endl;

    std::vector<NamedDecl*> parameters;

    if ( in_param > 0 && out_param > 0 ) {
      assert( 0 && "not implemented" );
    }

    // TODO loop over all paramters 
    if ( in_param > 0 ) {
      auto type = isl_dim_in;
      const char* name = isl_space_get_dim_name( space, type, 0 );
      std::cerr << "dim in param " << name << std::endl;
      assert( 0 && "not implemented" );
    }

    // loop over all parameters 
    for (int i = 0; i < out_param; ++i){
      auto type = isl_dim_out;
      const char* name = isl_space_get_dim_name( space, type, i );
      isl_id* id = isl_space_get_dim_id( space, type, i );
      std::cerr << "dim out param " << name << std::endl;
      if ( id ) {
	std::cerr << "id " << id << std::endl;
	void* user_data = isl_id_get_user( id );
	if ( user_data ) {
	  NamedDecl* named_decl = (NamedDecl*) user_data ;
	  parameters.push_back( named_decl );
	}
      }else{
	std::cerr << "no id" << std::endl;
      }
    }

    return parameters;
}

// pet already pareses the comment till the end of the line 
// but it does not add the \n 
// if the statement is not followed by a comment the new line character is already in it
std::string getSourceText( SourceLocation starts_with, 
    std::vector<std::pair<SourceRange,std::string>>& exclude_ranges, 
    SourceLocation ends_with, SourceManager& SM )  {

  std::string lexer_result = "";
  std::string comment = "";
  int skip_end = 0; 

  for ( auto& exclude : exclude_ranges){

    std::string ret = Lexer::getSourceText(
      CharSourceRange::getCharRange(
	SourceRange(
	  Lexer::getLocForEndOfToken(starts_with,0,SM,LangOptions()), 
	  exclude.first.getBegin()
	)
      ), 
      SM,
      LangOptions()
    );

    std::cerr << "parsed: " << ret << std::endl;

    lexer_result += ret;
    lexer_result += std::string("...") + exclude.second + std::string("...");
    
    starts_with = exclude.first.getEnd();
  }

  std::string ret = Lexer::getSourceText(
    CharSourceRange::getTokenRange(
      SourceRange(
	Lexer::getLocForEndOfToken(starts_with,0,SM,LangOptions()), 
	Lexer::getLocForEndOfToken(ends_with,0,SM,LangOptions()) 
      )
    ), 
    SM,
    LangOptions()
  );

  std::cerr << "parsed: " << ret << std::endl;

  lexer_result += ret;

  // to skip the closing bracket if its present
  if ( skip_end ) {
    lexer_result = lexer_result.substr( 0, lexer_result.size()-1);
  }
  lexer_result += comment; // the comment include the ";"

  // add a newline at the end if it does not exist
  if ( lexer_result.size() > 0 ) {
    if ( lexer_result.back() != '\n' ){
      lexer_result.push_back('\n');
    }
  }

  std::cerr << "lexer_result: " << lexer_result << std::endl;

  return lexer_result;

}

// search it by scanning this decl group for the source location // might be very slow
void replace_with_placeholder( pet_loc* loc, std::vector<NamedDecl*>& parameters, const ForStmt* for_stmt, 
    SourceLocation sloc_file, SourceManager& SM,
    std::vector<std::string>& statement_texts ) {

  // translate this to a source locations 
  std::cerr << "statement at " << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) << std::endl;
  auto begin_stmt = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
  auto end_stmt = sloc_file.getLocWithOffset( pet_loc_get_end(loc)-1 );
  std::cerr << "begin loc " << begin_stmt.printToString(SM) << std::endl;
  std::cerr << "end loc " << end_stmt.printToString(SM) << std::endl;
  
  // TODO i believe it should be enought to do this once
  DeclRefVisitor visitor(parameters, begin_stmt, end_stmt, SM);
  visitor.TraverseStmt( (ForStmt*)for_stmt );

  auto res = getSourceText(begin_stmt, visitor.exclude_ranges, end_stmt, SM );
  statement_texts.push_back( res );
}

// returns the statements with some placeholders so that the iterators can be replaced with new iterator names  
std::vector<std::string> get_statement_texts( pet_scop* scop, SourceLocation sloc_file, SourceManager& SM, const ForStmt* for_stmt ){

  std::vector<std::string> statement_texts;
  // loop over all statements 
  for (int i = 0; i < scop->n_stmt; ++i){
    pet_stmt* stmt = scop->stmts[i];

    auto parameters = get_parameters_for_pet_stmt( stmt );
	
    pet_loc* loc = stmt->loc;
    // replace the iterator name in this string with a placeholder
    replace_with_placeholder( loc, parameters, for_stmt, sloc_file, SM, statement_texts );
    
    
  } // loop over all statements

  return statement_texts;
}

#if 0
// TODO think about adding placeholders for iterators
std::map<std::string,std::string> get_call_texts(pet_scop* pscop, SourceLocation sloc_file, SourceManager& SM ){
  
  std::map<std::string,std::string> call_texts;
  for( auto& element : pscop->name_to_expr ){
    std::string call_text = Lexer::getSourceText( 
      CharSourceRange::getTokenRange( element.second->getSourceRange() ),
      SM, 
      LangOptions() 
    );
    call_texts[element.first] = call_text;
  }
  
}
#endif

static void create_scop_replacement( ASTContext& ctx_clang, 
    pet_scop* scop, 
    const ForStmt* for_stmt, 
    pluto_codegen_cxx::EMIT_CODE_TYPE emit_code_type, 
    bool write_cloog_file, 
    std::unique_ptr<std::map<std::string,std::string>>& call_texts 
  ) {

  SourceManager& SM = ctx_clang.getSourceManager();
  DiagnosticsEngine& diag = ctx_clang.getDiagnostics();

  FileID fid = SM.getFileID( for_stmt->getLocStart() );
  SourceLocation sloc_file = SM.translateLineCol(fid,1,1);

  std::cerr << "this decl group contains a scop at:" << std::endl;
  pet_loc* loc = scop->loc;
  std::cerr << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) << std::endl;
  std::cerr << "at line " << pet_loc_get_line(loc) << std::endl;

  auto begin_scop = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
  auto end_scop = sloc_file.getLocWithOffset( pet_loc_get_end(loc) );

  pet_scop_align_params( scop );

  auto begin_pluto = std::chrono::high_resolution_clock::now();
    // find prallelism
    PlutoOptions* pluto_options = pluto_options_alloc(); // memory leak if something goes wrong
    pluto_options->parallel = true;
    pluto_options->debug = true;
    pluto_options->isldep = true;
    // TODO this is a catastrophe !!!!! remove it
    //options = pluto_options;

    std::cerr << "generating pluto program from pet" << std::endl;
    auto prog = pet_to_pluto_prog(scop, pluto_options);
    if ( !prog ) {
      std::cerr << "could not generate a pluto program from the given pet_scop" << std::endl;
      // TODO memory leak put everything into unique_ptr
      return;
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
    // TODO emit diagnostic on why its not parallel
    // TODO run sequential STL algorithm matcher 
    auto begin_analyzer = std::chrono::high_resolution_clock::now();
    {
      stdlib_matchers::analyze( for_stmt, SM, ctx_clang, false );
    }
    auto end_analyzer = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end_analyzer-begin_analyzer;
    std::cerr << "analyzer time consumption " << diff.count() << " s" << std::endl;
    return;
  }

  // at this point we know that the loop is parallel 

  pet_scop_dump( scop );

  // find the text of the original statement
  auto statement_texts = get_statement_texts( scop, sloc_file, SM, for_stmt );
  //auto call_texts = get_call_texts( scop , sloc_file, SM, for_stmt );

  std::stringstream outfp;

  if ( pluto_codegen_cxx::pluto_multicore_codegen( outfp, prog, statement_texts, emit_code_type, write_cloog_file, *call_texts ) == EXIT_FAILURE ) {
    // stop if codegeneration failed
    return;
  }

  std::cerr << outfp.str() << std::endl;

  std::string repl = outfp.str();

  std::cerr << "emitting diagnositc" << std::endl;
  unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "found a scop");
  std::cerr << "got id " << DiagID << std::endl;

  // replace the for statement
  diag.Report(begin_scop, DiagID) 
  << FixItHint::CreateReplacement(for_stmt->getSourceRange(), repl.c_str() );
  std::cerr << "reported error " << DiagID << std::endl;
}


static void extract_scop_with_pet( ASTContext& ctx_clang, const ForStmt* for_stmt, const FunctionDecl* function_decl, pluto_codegen_cxx::EMIT_CODE_TYPE emit_code_type, bool write_cloog_file ) {
  
  DiagnosticsEngine& diag = ctx_clang.getDiagnostics();
  SourceManager& SM = ctx_clang.getSourceManager();

  std::cerr << "handling for_stmt " << ctr++ << std::endl;
  Pet pet_scanner( diag, &ctx_clang );
  std::cerr << "done creating the Pet scanner object" << std::endl;

  std::cerr << "LINE" << __LINE__ << std::endl;
  std::cerr << "ast context " << &ctx_clang << " sm " << &SM << std::endl;
  std::cerr << "LINE" << __LINE__ << std::endl;


  pet_scop* scop = nullptr;

  std::unique_ptr<std::map<std::string,std::string>> call_texts;

  auto begin_pet = std::chrono::high_resolution_clock::now();
  std::cerr << "calling pet_scop_extract_from_clang_ast" << std::endl;
  pet_scanner.pet_scop_extract_from_clang_ast(&ctx_clang,(ForStmt*)for_stmt, (FunctionDecl*) function_decl, call_texts, &scop); 
  std::cerr << "done calling pet_scop_extract_from_clang_ast" << std::endl;
  auto end_pet = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> diff = end_pet-begin_pet;
  std::cerr << "pet time consumption " << diff.count() << " s" << std::endl;


  if ( scop ) {
    std::cerr << "found a valid scop" << std::endl;
    create_scop_replacement( ctx_clang, scop, for_stmt, emit_code_type, write_cloog_file, call_texts );
  }
}

class Callback : public MatchFinder::MatchCallback {
  public:
    Callback ( pluto_codegen_cxx::EMIT_CODE_TYPE _emit_code_type, bool _write_cloog_file ) :
      emit_code_type(_emit_code_type),
      write_cloog_file(_write_cloog_file)
    {

    }
     // is the function that is called if the matcher finds something
     virtual void run(const MatchFinder::MatchResult &Result){
       std::cerr << "plugin callback called " << std::endl;
       ASTContext& context = *Result.Context;
       SourceManager& SM = context.getSourceManager();

       if ( auto* function_decl = Result.Nodes.getNodeAs<FunctionDecl>("function_decl") ) {
	 if ( auto* for_stmt = Result.Nodes.getNodeAs<ForStmt>("for_stmt") ) {
	   auto loc = for_stmt->getLocStart();
	   if ( SM.isInMainFile( loc ) ) {
	     extract_scop_with_pet( context, for_stmt, function_decl, emit_code_type, write_cloog_file );
	   }
	   //else{
	   //  std::cerr << "location of for_stmt is not in the main file but in " << SM.getFilename(loc).str() << std::endl;
	   //}
	 }
       }

     }

  private:
     pluto_codegen_cxx::EMIT_CODE_TYPE emit_code_type;
     bool write_cloog_file;
};

class ForLoopConsumer : public ASTConsumer {
public:

  
  ForLoopConsumer( pluto_codegen_cxx::EMIT_CODE_TYPE _emit_code_type, bool _write_cloog_file) :
    emit_code_type(_emit_code_type),
    write_cloog_file(_write_cloog_file)
  { 
    std::cerr << "for loop consumer created " << this << std::endl;
  }

  ~ForLoopConsumer(){
    std::cerr << "for loop consumer destroyed " << this << std::endl;
  }


  // all for loops that dont have a nested for loop
  DeclarationMatcher makeForLoopMatcher(){
    return functionDecl(
	forEachDescendant(
	  forStmt(
#if 0
	    unless(
	      hasDescendant(
		forStmt()
	      )
	    )
#endif
	  ).bind("for_stmt")
	)	  
    ).bind("function_decl");
  }

#if 1
  void HandleTranslationUnit( ASTContext& clang_ctx ) {
    auto begin = std::chrono::high_resolution_clock::now();
    ctr = 0;
    MatchFinder Finder;
    Callback Fixer(emit_code_type, write_cloog_file);
    std::cerr << "adding matcher" << std::endl;
    Finder.addMatcher( makeForLoopMatcher(), &Fixer);
    std::cerr << "running matcher" << std::endl;
    Finder.matchAST(clang_ctx);
    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end-begin;
    std::cerr << "plugin time consumption " << diff.count() << " s" << std::endl;
  }
#endif

private: 
  pluto_codegen_cxx::EMIT_CODE_TYPE emit_code_type;
  bool write_cloog_file;

};

static bool once_std_out = true;
static bool once_std_err = true;

class ClanAction : public PluginASTAction {

  public:
    ClanAction(){
      std::cerr << "clang action " << this << " created " << std::endl;
    }

    virtual ~ClanAction(){
      std::cerr << "clang action " << this << " destroyed " << std::endl;
    }

  //std::set<std::string> ParsedTemplates;
protected:


  pluto_codegen_cxx::EMIT_CODE_TYPE emit_code_type = pluto_codegen_cxx::EMIT_ACC;
  bool write_cloog_file = false;
  std::string redirect_stdout_file = "";
  std::string redirect_stderr_file = "";
  std::string* next_arg = nullptr;

  // NOTE: stefan this creates the consumer that is given the TU after everything is done
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {
    if ( redirect_stdout_file != "" ) {
      std::cout << "redirect_stdout_file " << redirect_stdout_file << std::endl;
      // TODO mutex
      if ( once_std_out ) {
	std::freopen(redirect_stdout_file.c_str(), "a", stdout);
	setvbuf ( stdout , NULL , _IOLBF , 1024 );
	once_std_out = false;
      }     
    }
    if ( redirect_stderr_file != "" ) {
      std::cout << "redirect_stderr_file " << redirect_stderr_file << std::endl;
      // TODO mutex
      if ( once_std_err ) {
	std::freopen(redirect_stderr_file.c_str(), "a", stderr);
	setvbuf ( stderr , NULL , _IOLBF , 1024 );
	once_std_err = false;
      }     
    }
    std::cerr << "makeing new Consumer object with compiler instance " << &CI << std::endl;
    auto ret =  llvm::make_unique<ForLoopConsumer>(emit_code_type, write_cloog_file);
    std::cerr << "at load ci " << ret.get() << " instance " << &CI << " ast context " << &CI.getASTContext() << " sm " << &CI.getSourceManager() << std::endl;
    std::cerr << "done with the new consumer object" << std::endl;
    return std::move(ret);
  }


  void PrintHelp(llvm::raw_ostream& ros) {
    ros << "Help for Clan plugin goes here\n";
  }

  // TODO add instructions on how to do that
  // #stefan: here one can parse some arugments for this plugin
  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {

    for (unsigned i = 0, e = args.size(); i != e; ++i) {
      llvm::errs() << "Clan arg = " << args[i] << "\n";

      if ( next_arg ) {
	*next_arg = args[i];
	next_arg = nullptr;
	continue;
      }

      if ( args[i] == "-emit-openacc" ) {
	std::cerr << "emiting openacc" << std::endl;
	emit_code_type = pluto_codegen_cxx::EMIT_ACC;
      }

      if ( args[i] == "-emit-openmp" ) {
	std::cerr << "emiting openmp" << std::endl;
	emit_code_type = pluto_codegen_cxx::EMIT_OPENMP;
      }

      if ( args[i] == "-emit-hpx" ) {
	std::cerr << "emiting hpx" << std::endl;
	emit_code_type = pluto_codegen_cxx::EMIT_HPX;
      }

      if ( args[i] == "-write-cloog-file" ) {
	std::cerr << "writing cloog file" << std::endl;
	write_cloog_file = true;
      }

      if ( args[i] == "-redirect-stdout" ) {
	std::cerr << "redirecting stdout" << std::endl;
	next_arg = &redirect_stdout_file;
      }

      if ( args[i] == "-redirect-stderr" ) {
	std::cerr << "redirecting stderr" << std::endl;
	next_arg = &redirect_stderr_file;
      }

    }

    return true;
  }


};

}

static FrontendPluginRegistry::Add<ClanAction>
X("clan", "run clan as part of the compiler");
