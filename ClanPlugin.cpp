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

#include "dependency_analysis.h"
#include "pluto_compat.h"

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
      PlutoOptions* options,
      isl_union_map* raw,
      isl_union_map* war,
      isl_union_map* waw,
      isl_union_map* red
  );
}


class PetPlutoInterface{

  public:

    PetPlutoInterface( std::set<std::string>& _header_includes ) : header_includes(_header_includes) 
    {
    }

void build_rename_table( isl_union_set* domains, std::vector<int>& table ) {
  
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

isl_stat correct_alignment( __isl_take isl_map *schedule, void* user ){
  std::pair<pet_scop*,isl_union_map*>* user_data = (std::pair<pet_scop*,isl_union_map*>*)user;

  // correcting schedule 
  auto new_schedule = isl_map_align_params(schedule, isl_set_get_space(user_data->first->context));
  isl_union_map_add_map( user_data->second, new_schedule );
  return (isl_stat)0;
}

__isl_give isl_union_set *collect_non_kill_domains(struct pet_scop *scop )
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

#if 1
PlutoProg* compute_deps( pet_scop* pscop, PlutoOptions* options ) {

  // pet injects kill statements into every map 
  // i need to filter all of these things out in order to make it run like expected
  isl_union_map* schedule= isl_schedule_get_map(pscop->schedule);
  isl_union_map* read = pet_scop_collect_may_reads(pscop);
  isl_union_map* write = pet_scop_collect_must_writes(pscop);
  isl_union_map* empty = isl_union_map_empty(isl_set_get_space(pscop->context));

  isl_union_set* domains = collect_non_kill_domains( pscop );

  std::vector<int> rename_table;
  build_rename_table( domains, rename_table );

  auto space = isl_set_get_space( pscop->context );

  // filter all that is -1 or not in the table 
  if ( rename_table.size() > 0 ) {
    domains = linearize_union_set( space, domains, rename_table );
    schedule = linearize_union_map( space, schedule, rename_table );
    read = linearize_union_map( space, read, rename_table );
    write = linearize_union_map( space, write, rename_table );
    empty = linearize_union_map( space, empty, rename_table );
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
  
  // TODO not sure that this is still needed i changed pluto to allow non unified sets to work aswell
  //      so this might not change anything at all

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


  //Dependences dependences( pscop );
  Dependences dependences( pscop );

  auto pluto_compat_data = dependences.make_pluto_compatible( rename_table );

  // TODO the kill statements are not respected in isls dependency analysis 
  //      this needs to be taken into account in order to make scoped variables work like expected
#if 0
  return pluto_compute_deps( schedule, read, write, empty, domains, context, options, 
      dependences.getRAW(),  
      dependences.getWAR(),  
      dependences.getWAW(),  
      dependences.getRED() 
      );
#endif
#if 1
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
#endif
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

void create_scop_replacement( ASTContext& ctx_clang, 
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
  auto begin_codegen = std::chrono::high_resolution_clock::now();

  if ( pluto_codegen_cxx::pluto_multicore_codegen( outfp, prog, statement_texts, emit_code_type, write_cloog_file, *call_texts, header_includes ) == EXIT_FAILURE ) {
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

  auto end_codegen = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> diff_cg = end_codegen-begin_codegen;
  std::cerr << "codegen time consumption " << diff_cg.count() << " s" << std::endl;
}


void extract_scop_with_pet( ASTContext& ctx_clang, const ForStmt* for_stmt, const FunctionDecl* function_decl, pluto_codegen_cxx::EMIT_CODE_TYPE emit_code_type, bool write_cloog_file ) {
  
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

protected:

  std::set<std::string>& header_includes;

}; // PetPlutoInterface

class Callback : public MatchFinder::MatchCallback {
  public:
    Callback ( pluto_codegen_cxx::EMIT_CODE_TYPE _emit_code_type, bool _write_cloog_file ) :
      emit_code_type(_emit_code_type),
      write_cloog_file(_write_cloog_file)
    {

    }
     // is the function that is called if the matcher finds something
     virtual void run(const MatchFinder::MatchResult &Result){
       std::cerr << "plugin: callback called " << std::endl;
       ASTContext& context = *Result.Context;
       SourceManager& SM = context.getSourceManager();

       if ( auto* function_decl = Result.Nodes.getNodeAs<FunctionDecl>("function_decl") ) {
	 if ( auto* for_stmt = Result.Nodes.getNodeAs<ForStmt>("for_stmt") ) {
	   auto loc = for_stmt->getLocStart();
	   if ( SM.isInMainFile( loc ) ) {
	     PetPlutoInterface ppi(header_includes);
	     ppi.extract_scop_with_pet( context, for_stmt, function_decl, emit_code_type, write_cloog_file );
	   }
	 }
       }

     }

  std::set<std::string> header_includes;

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
    MatchFinder Finder;
    Callback Fixer(emit_code_type, write_cloog_file);
    std::cerr << "adding matcher" << std::endl;
    Finder.addMatcher( makeForLoopMatcher(), &Fixer);
    std::cerr << "running matcher" << std::endl;
    Finder.matchAST(clang_ctx);

    add_missing_includes(Fixer, clang_ctx);

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end-begin;
    std::cerr << "plugin: time consumption " << diff.count() << " s" << std::endl;
  }

  void add_missing_includes(Callback& Fixer, ASTContext& clang_ctx) {
    for( auto& header : Fixer.header_includes ){
      // TODO dont add if the header is already included
      // TODO skip the lines that begin with a comment 
      //      this way its possible to skip licences that are mostly at the beginning of a file
      auto& SM = clang_ctx.getSourceManager();
      auto fid = SM.getMainFileID();
      auto line = 1;
      auto col = 1;
      auto name = header;
      auto begin_of_file = SM.translateLineCol( fid, line, col );
      auto& diag = clang_ctx.getDiagnostics();
      unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning, "missing header for hpx");

      diag.Report(begin_of_file, id)  << FixItHint::CreateInsertion(begin_of_file, std::string("#include <") + name + ">\n" );
    }
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

      if ( args[i] == "-emit-tbb" ) {
	std::cerr << "emiting tbb" << std::endl;
	emit_code_type = pluto_codegen_cxx::EMIT_TBB;
      }

      if ( args[i] == "-emit-cilk" ) {
	std::cerr << "emiting cilk" << std::endl;
	emit_code_type = pluto_codegen_cxx::EMIT_CILK;
      }

      // add new back-ends here 

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
