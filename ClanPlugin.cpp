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
#include <pluto/libpluto.h>
#include <string>
#include <pluto_codegen_clang.hpp>
#include <thread>
#include <signal.h>
#include <setjmp.h>
#include <map>
#include <clang/AST/AST.h>
#include "pet.h"
#include "pet_cxx.h"

#include <isl/options.h>
#include <isl/arg.h>
#include <isl/flow.h>
#include <isl/map.h>

extern "C"{
// TODO PlutoProg is not known outside of libpluto
//      since i want to write my own unparser thats not a big problem but its definitly something i 
//      want to change temporarily
//      
int pluto_multicore_codegen(FILE *cloogfp, FILE *outfp, const PlutoProg *prog);
PlutoProg *scop_to_pluto_prog(osl_scop_p scop, PlutoOptions *options);
void pluto_prog_free(PlutoProg* prog);
int pluto_stmt_is_member_of(int stmt_id, Stmt **slist, int len);
void pluto_detect_transformation_properties(PlutoProg *prog);
int pluto_schedule_pluto( PlutoProg* prog, PlutoOptions* options );

int pet_tree_foreach_sub_tree(__isl_keep pet_tree *tree,
    int (*fn)(__isl_keep pet_tree *tree, void *user), void *user);


}



using namespace clang;
using namespace clang::ast_matchers;

namespace {

extern "C"{
  PlutoProg* pluto_compute_deps( isl_union_map* schedule, 
      isl_union_map* read, 
      isl_union_map* write, 
      isl_union_map* empty, 
      isl_union_set* domains,
      PlutoOptions* options 
  );
}

PlutoProg* compute_deps( pet_scop* pscop, PlutoOptions* options ) {

  isl_union_map* schedule= isl_schedule_get_map(pscop->schedule);
  isl_union_map* read = pet_scop_collect_may_reads(pscop);
  isl_union_map* write = pet_scop_collect_must_writes(pscop);
  isl_union_map* empty = isl_union_map_empty(isl_set_get_space(pscop->context));
  isl_union_set* domains = pet_scop_collect_domains( pscop );

  return pluto_compute_deps( schedule, read, write, empty, domains, options );
}


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

    std::cout << "visited a node" << std::endl;
    for( auto i = 0 ; i < iterators.size() ; i++ ){
      auto& iterator = iterators[i];
      if ( declRefExpr->getDecl() == iterator ) {
	std::cout << "found a reference" << std::endl;
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

    std::cout << "in_nparam " << in_param << std::endl;

    std::vector<NamedDecl*> parameters;

    if ( in_param > 0 && out_param > 0 ) {
      assert( 0 && "not implemented" );
    }

    // TODO loop over all paramters 
    if ( in_param > 0 ) {
      auto type = isl_dim_in;
      const char* name = isl_space_get_dim_name( space, type, 0 );
      std::cout << "dim in param " << name << std::endl;
      assert( 0 && "not implemented" );
    }

    // TODO loop over all paramters 
    if ( out_param > 0 ) {
      auto type = isl_dim_out;
      const char* name = isl_space_get_dim_name( space, type, 0 );
      isl_id* id = isl_space_get_dim_id( space, type, 0 );
      std::cout << "dim out param " << name << std::endl;
      if ( id ) {
	std::cout << "id " << id << std::endl;
	void* user_data = isl_id_get_user( id );
	if ( user_data ) {
	  NamedDecl* named_decl = (NamedDecl*) user_data ;
	  parameters.push_back( named_decl );
	}
      }else{
	std::cout << "no id" << std::endl;
      }
    }

    return parameters;
}


std::vector<std::string> get_statement_texts( pet_scop* scop, SourceLocation sloc_file, SourceManager& SM, const ForStmt* for_stmt ){

  std::vector<std::string> statement_texts;
  // loop over all statements 
  for (int i = 0; i < scop->n_stmt; ++i){
    pet_stmt* stmt = scop->stmts[i];

    pet_loc* loc = stmt->loc;
    std::cout << "statement at " << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) << std::endl;
    // translate this to a source locations 
    auto begin_stmt = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
    auto end_stmt = sloc_file.getLocWithOffset( pet_loc_get_end(loc) );
    std::cout << "begin loc " << begin_stmt.printToString(SM) << std::endl;
    std::cout << "end loc " << end_stmt.printToString(SM) << std::endl;

    auto parameters = get_parameters_for_pet_stmt( stmt );
    
    // get the string describing this statement 
    auto getString = [](SourceLocation starts_with, SourceLocation ends_with, SourceManager& SM){ 
      std::string ret = Lexer::getSourceText(
	CharSourceRange::getTokenRange(
	  SourceRange(
	    //Lexer::getLocForEndOfToken(starts_with,0,SM,LangOptions()), 
	    starts_with,
	    ends_with
	  )
	), 
	SM,
	LangOptions()
      );
      return ret;
    };
    auto stmt_text = getString( begin_stmt, end_stmt, SM );

    std::cout << "stmt_text " << stmt_text << std::endl;
	
    // replace the iterator name in this string with a placeholder
    
    // option 1 search it by scanning this decl group for the source location // might be very slow
    
    DeclRefVisitor visitor(parameters, begin_stmt, end_stmt, SM);
    visitor.TraverseStmt( (ForStmt*)for_stmt );

    std::string lexer_result = "";
    std::string comment = "";
    int skip_end = 0; 
    // TODO export to function
    {
      auto starts_with = begin_stmt;
      auto expr_end = end_stmt;

      for ( auto& exclude : visitor.exclude_ranges){

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

	std::cout << "parsed: " << ret << std::endl;

	lexer_result += ret;
	lexer_result += std::string("...") + exclude.second + std::string("...");
	
	starts_with = exclude.first.getEnd();
      }

      std::string ret = Lexer::getSourceText(
	CharSourceRange::getTokenRange(
	  SourceRange(
	    Lexer::getLocForEndOfToken(starts_with,0,SM,LangOptions()), 
	    expr_end
	  )
	), 
	SM,
	LangOptions()
      );

      std::cout << "parsed: " << ret << std::endl;

      lexer_result += ret;
      // to skip the closing bracket if its present
      if ( skip_end ) {
	lexer_result = lexer_result.substr( 0, lexer_result.size()-1);
      }
      lexer_result += comment; // the comment include the ";"

      std::cout << "lexer_result: " << lexer_result << std::endl;
    }

    statement_texts.push_back( lexer_result );

  } // loop over all statements

  return statement_texts;

}


static void create_scop_replacement( ASTContext& ctx_clang, pet_scop* scop, const ForStmt* for_stmt ) {

  SourceManager& SM = ctx_clang.getSourceManager();
  DiagnosticsEngine& diag = ctx_clang.getDiagnostics();

  FileID fid = SM.getFileID( for_stmt->getLocStart() );
  SourceLocation sloc_file = SM.translateLineCol(fid,1,1);

  std::cout << "this decl group contains a scop at:" << std::endl;
  pet_loc* loc = scop->loc;
  std::cout << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) << std::endl;
  std::cout << "at line " << pet_loc_get_line(loc) << std::endl;

  auto begin_scop = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
  auto end_scop = sloc_file.getLocWithOffset( pet_loc_get_end(loc) );

  // find prallelism
  PlutoOptions* pluto_options = pluto_options_alloc(); // memory leak if something goes wrong
  pluto_options->parallel = true;
  pluto_options->debug = true;
  pluto_options->isldep = true;
  // TODO this is a catastrophe !!!!! remove it
  options = pluto_options;

  std::cout << "generating pluto program from pet" << std::endl;
  auto prog = pet_to_pluto_prog(scop, pluto_options);
  std::cout << "done generating pluto program from scop" << std::endl;

  std::cout << "schedule pluto prog" << std::endl;
  pluto_schedule_pluto( prog, options );
  std::cout << "schedule_pluto done " << std::endl;
  std::cout << "ClanPlugin " << prog->ndeps << std::endl;

  // TODO determin parallelism
  // dont continue if not found

  pet_scop_dump( scop );

  // find the text of the original statement
  auto statement_texts = get_statement_texts( scop, sloc_file, SM, for_stmt );

  // cloog has to generate some file that can then be read by clast
  // to make it faster and thread save, we put this into a memory buffer 
  size_t in_memory_file_size = 2*1024*1024;
  char in_memory_file[in_memory_file_size]; // 2MB should be ok for this crutch if this becomes a problem rewrite the code to use streams
  FILE* cloogfp = fmemopen( in_memory_file, in_memory_file_size, "w" ); 
  pluto_gen_cloog_file(cloogfp, prog);
  fclose( cloogfp );
  cloogfp = fmemopen( in_memory_file, in_memory_file_size, "r" );

  std::stringstream outfp;
  pluto_codegen_clang::pluto_multicore_codegen( outfp, prog, cloogfp, statement_texts);

  std::cout << outfp.str() << std::endl;

  std::string repl = outfp.str();

  std::cerr << "emitting diagnositc" << std::endl;
  unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "found a scop");
  std::cerr << "got id " << DiagID << std::endl;

  // replace the for statement
  diag.Report(begin_scop, DiagID) 
  << FixItHint::CreateReplacement(for_stmt->getSourceRange(), repl.c_str() );
  std::cerr << "reported error " << DiagID << std::endl;
}


static void extract_scop_with_pet( ASTContext& ctx_clang, const ForStmt* for_stmt, const FunctionDecl* function_decl ) {
  
  isl_ctx* ctx_isl = isl_ctx_alloc();

  DiagnosticsEngine& diag = ctx_clang.getDiagnostics();
  SourceManager& SM = ctx_clang.getSourceManager();

  std::cout << "handling for_stmt " << ctr++ << std::endl;
  Pet pet_scanner(ctx_isl, diag, &ctx_clang );
  std::cout << "done creating the Pet scanner object" << std::endl;

  std::cout << "LINE" << __LINE__ << std::endl;
  std::cout << "ast context " << &ctx_clang << " sm " << &SM << std::endl;
  std::cout << "LINE" << __LINE__ << std::endl;


  pet_scop* scop = nullptr;

  std::cout << "calling pet_scop_extract_from_clang_ast" << std::endl;
  pet_scanner.pet_scop_extract_from_clang_ast(&ctx_clang,(ForStmt*)for_stmt, (FunctionDecl*) function_decl ,&scop); 
  std::cout << "done calling pet_scop_extract_from_clang_ast" << std::endl;

  if ( scop ) {
    std::cout << "found a valid scop" << std::endl;
    create_scop_replacement( ctx_clang, scop, for_stmt );
  }
}

class Callback : public MatchFinder::MatchCallback {
  public:
    Callback () {

    }
     // is the function that is called if the matcher finds something
     virtual void run(const MatchFinder::MatchResult &Result){
       std::cout << "callback called " << std::endl;
       ASTContext& context = *Result.Context;
       SourceManager& SM = context.getSourceManager();

       if ( auto* function_decl = Result.Nodes.getNodeAs<FunctionDecl>("function_decl") ) {
	 if ( auto* for_stmt = Result.Nodes.getNodeAs<ForStmt>("for_stmt") ) {
	   auto loc = for_stmt->getLocStart();
	   if ( SM.isInMainFile( loc ) ) {
	     //unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning, "test diagnostic from callback");
	     //diag.Report(loc, id) << "test diagnostic text ";
	     //std::cout << "location of for_stmt is in the main file " << SM.getFilename(loc).str() << std::endl;
	     extract_scop_with_pet( context, for_stmt, function_decl );
	   }
	   //else{
	   //  std::cout << "location of for_stmt is not in the main file but in " << SM.getFilename(loc).str() << std::endl;
	   //}
	 }
       }

     }
};

class ForLoopConsumer : public ASTConsumer {
public:
#if 0
  SourceManager* SM = nullptr;
  ASTContext* clang_ctx = nullptr;
  DiagnosticsEngine* diags = nullptr;// = Instance.getDiagnostics();
  CompilerInstance& Instance;
#endif

  ForLoopConsumer(CompilerInstance& _Instance) 
#if 0
    :
      Instance(_Instance)
#endif
  { 
    std::cout << "for loop consumer created " << this << std::endl;
    //fill_context_info( Instance );
  }

  ~ForLoopConsumer(){
    std::cout << "for loop consumer destroyed " << this << std::endl;
  }


#if 0
  void fill_context_info( CompilerInstance& Instance ){
    if ( Instance.hasASTContext() && clang_ctx == nullptr ){
      clang_ctx = &Instance.getASTContext();
    }
    if ( Instance.hasDiagnostics() && diags == nullptr ) {
      diags = &Instance.getDiagnostics();
    }
    if ( Instance.hasSourceManager() && SM == nullptr ){
      SM = &Instance.getSourceManager();
    }
  }
#endif

#if 0
  void Initialize( ASTContext& ctx ) override {

    clang_ctx = &ctx;
    SM = &ctx.getSourceManager();
    diags = &ctx.getDiagnostics();

  }
#endif

  DeclarationMatcher makeForLoopMatcher(){
    return functionDecl(
	forEachDescendant(
	  forStmt().bind("for_stmt")
	)	  
    ).bind("function_decl");
  }

#if 1
  void HandleTranslationUnit( ASTContext& clang_ctx ) {
    ctr = 0;
    MatchFinder Finder;
    Callback Fixer;
    std::cout << "adding matcher" << std::endl;
    Finder.addMatcher( makeForLoopMatcher(), &Fixer);
    std::cout << "running matcher" << std::endl;
    Finder.matchAST(clang_ctx);
  }
#endif

#if 0
  virtual bool HandleTopLevelDecl(DeclGroupRef dg) {

     std::cout << "HandleTopLevelDecl " << this << std::endl;

     if ( !this ) return false;

     isl_ctx* ctx = isl_ctx_alloc();

     // TODO limit the printout to the file we are looking at 
     //      we are not interested for optimizations in <vector> or other headers 
     
     //fill_context_info(Instance);
     for( auto&& element : dg ){
	 auto loc = element->getLocStart();
	 if ( SM->isInMainFile( loc ) ) {
	   DiagnosticsEngine &diag = Instance.getDiagnostics();
	   unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
						      "test diagnostic from htld");
	   std::cout << "location of dg is in the main file " << SM->getFilename(loc).str() << std::endl;
	   diag.Report(loc, id) << "test diagnostic text ";
	 }else{
	   std::cout << "location of dg is not in the main file but in " << SM->getFilename(loc).str() << std::endl;
	 }
     }

     

#if 0
     std::cout << "handling top level decl take " << ctr++ << " in consumer instance " << this << std::endl;
     //Pet pet_scanner(ctx, Instance.getPreprocessor() ,*diags, clang_ctx,false);
     std::cout << "done creating the Pet scanner object" << std::endl;

     std::cout << "LINE" << __LINE__ << std::endl;


     std::cout << "LINE" << __LINE__ << std::endl;
     std::cout << "ci " << this << " ast context " << &clang_ctx << " sm " << SM  << std::endl;
     std::cout << "LINE" << __LINE__ << std::endl;

     unsigned diag_id_found = diags->getCustomDiagID(DiagnosticsEngine::Warning, "scop if found" );
     std::cout << "LINE" << __LINE__ << std::endl;
     unsigned diag_id_outside = diags->getCustomDiagID(DiagnosticsEngine::Warning, "scop outside" );
     std::cout << "diagID if found " << diag_id_found << std::endl;
     std::cout << "diagID outside " << diag_id_outside << std::endl;
     FileID dg_fid = SM->getFileID( (*dg.begin())->getLocStart() );
     SourceLocation sloc_file = SM->translateLineCol(dg_fid,1,1);
      
     pet_scop* scop = nullptr;
#if 0
     std::cout << "pet_scop " << scop << std::endl;
     std::cout << "calling pet_scop_extract_from_clang_ast" << std::endl;
     pet_scanner.pet_scop_extract_from_clang_ast(clang_ctx,nullptr,dg,&scop); 
     std::cout << "pet_scop " << scop << std::endl;
#endif


 
     if ( scop ) {
      std::cout << "this decl group contains a scop at:" << std::endl;
      pet_loc* loc = scop->loc;
      std::cout << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) << std::endl;
      std::cout << "at line " << pet_loc_get_line(loc) << std::endl;

      auto begin_scop = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
      auto end_scop = sloc_file.getLocWithOffset( pet_loc_get_end(loc) );

      // find prallelism
      PlutoOptions* pluto_options = pluto_options_alloc(); // memory leak if something goes wrong
      pluto_options->parallel = true;
      pluto_options->debug = true;
      pluto_options->isldep = true;
      // TODO this is a catastrophe !!!!! remove it
      options = pluto_options;

      std::cout << "generating pluto program from pet" << std::endl;
      auto prog = pet_to_pluto_prog(scop, pluto_options);
      std::cout << "done generating pluto program from scop" << std::endl;

      std::cout << "schedule pluto prog" << std::endl;
      pluto_schedule_pluto( prog, options );
      std::cout << "schedule_pluto done " << std::endl;
      std::cout << "ClanPlugin " << prog->ndeps << std::endl;

      pet_scop_dump( scop );

      std::vector<std::string> statement_texts;
      // loop over all statements 
      for (int i = 0; i < scop->n_stmt; ++i){
          pet_stmt* stmt = scop->stmts[i];

	  pet_loc* loc = stmt->loc;
	  std::cout << "statement at " << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) << std::endl;
	  // translate this to a source locations 
	  auto begin_stmt = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
	  auto end_stmt = sloc_file.getLocWithOffset( pet_loc_get_end(loc) );
	  std::cout << "begin loc " << begin_stmt.printToString(*SM) << std::endl;
	  std::cout << "end loc " << end_stmt.printToString(*SM) << std::endl;

	  // get the iteration domain
	  isl_set* domain = stmt->domain;
	  isl_set_dump( domain );

	  // get the iteration space of this statement
	  isl_space* space = pet_stmt_get_space( stmt );
	  int in_param = isl_space_dim(space, isl_dim_in);
	  int out_param = isl_space_dim(space, isl_dim_out);

	  std::cout << "in_nparam " << in_param << std::endl;

	  std::vector<NamedDecl*> parameters;

	  // TODO loop over all paramters 
	  if ( in_param > 0 ) {

	    auto type = isl_dim_in;
	    const char* name = isl_space_get_dim_name( space, type, 0 );
	    std::cout << "dim in param " << name << std::endl;
	    
	  }

	  if ( out_param > 0 ) {
	    auto type = isl_dim_out;
	    const char* name = isl_space_get_dim_name( space, type, 0 );
	    isl_id* id = isl_space_get_dim_id( space, type, 0 );
	    std::cout << "dim out param " << name << std::endl;
	    if ( id ) {
	      std::cout << "id " << id << std::endl;
	      void* user_data = isl_id_get_user( id );
	      if ( user_data ) {
		std::cout << "user_data " << user_data << std::endl;
		NamedDecl* named_decl = (NamedDecl*) user_data ;
		parameters.push_back( named_decl );
	      }
	    }else{
	      std::cout << "no id" << std::endl;
	    }
	  }

	  // get the string describing this statement 
	  auto getString = [](SourceLocation starts_with, SourceLocation ends_with, SourceManager& SM){ 
	    std::string ret = Lexer::getSourceText(
	      CharSourceRange::getTokenRange(
		SourceRange(
		  //Lexer::getLocForEndOfToken(starts_with,0,SM,LangOptions()), 
		  starts_with,
		  ends_with
		)
	      ), 
	      SM,
	      LangOptions()
	    );
	    return ret;
	  };
	  auto stmt_text = getString( begin_stmt, end_stmt, *SM );

	  std::cout << "stmt_text " << stmt_text << std::endl;
	      
	  // replace the iterator name in this string with a placeholder
	  
	  // option 1 search it by scanning this decl group for the source location // might be very slow
	  
	  DeclRefVisitor visitor(parameters, begin_stmt, end_stmt, *SM);
	  for( auto& declare : dg ){
	    visitor.TraverseDecl( declare );
	  }

	  std::string lexer_result = "";
	  std::string comment = "";
	  int skip_end = 0; 
	  // TODO export to function
	  {
	    auto starts_with = begin_stmt;
	    auto expr_end = end_stmt;

	    for ( auto& exclude : visitor.exclude_ranges){

	      std::string ret = Lexer::getSourceText(
		CharSourceRange::getCharRange(
		  SourceRange(
		    Lexer::getLocForEndOfToken(starts_with,0,*SM,LangOptions()), 
		    exclude.first.getBegin()
		  )
		), 
		*SM,
		LangOptions()
	      );

	      std::cout << "parsed: " << ret << std::endl;

	      lexer_result += ret;
	      lexer_result += std::string("...") + exclude.second + std::string("...");
	      
	      starts_with = exclude.first.getEnd();
	    }

	    std::string ret = Lexer::getSourceText(
	      CharSourceRange::getTokenRange(
		SourceRange(
		  Lexer::getLocForEndOfToken(starts_with,0,*SM,LangOptions()), 
		  expr_end
		)
	      ), 
	      *SM,
	      LangOptions()
	    );

	    std::cout << "parsed: " << ret << std::endl;

	    lexer_result += ret;
	    // to skip the closing bracket if its present
	    if ( skip_end ) {
	      lexer_result = lexer_result.substr( 0, lexer_result.size()-1);
	    }
	    lexer_result += comment; // the comment include the ";"

	    std::cout << "lexer_result: " << lexer_result << std::endl;
	  }

	  
	  // option 2 store the pointer to the ast node into the pet_stmt structure // requires changes to pet
	  
	  // option 3 change clangs variable names ( in the AST ) to make it very easy to find the variable names
	  // Problem: this does not change them in the underlying file
	  
	  // option 4 it is already stored in the pet_stmt as a refrence to its arguments;
	  // pet does not store anything usefull the onlything that is stored is the NamedDecl that is references by 
	  // the iterator since i need the stmt or the DeclRefExpr itself this is kinda useless
	  statement_texts.push_back( lexer_result );

      } // loop over all statements



      // cloog has to generate some file that can then be read by clast
      size_t in_memory_file_size = 2*1024*1024;
      char in_memory_file[in_memory_file_size]; // 2MB should be ok for this crutch if this becomes a problem rewrite the code to use streams
      FILE* cloogfp = fmemopen( in_memory_file, in_memory_file_size, "w" ); 
      pluto_gen_cloog_file(cloogfp, prog);
      fclose( cloogfp );
      cloogfp = fmemopen( in_memory_file, in_memory_file_size, "r" );

      std::stringstream outfp;
      pluto_codegen_clang::pluto_multicore_codegen( outfp, prog, cloogfp, statement_texts);

      std::cout << outfp.str() << std::endl;

      std::string repl = outfp.str();

      std::cerr << "emitting diagnositc" << std::endl;
      unsigned DiagID = diags->getCustomDiagID(DiagnosticsEngine::Warning, "found a scop");
      std::cerr << "got id " << DiagID << std::endl;
      diags->Report(begin_scop, DiagID) 
	<< FixItHint::CreateReplacement(SourceRange(begin_scop,end_scop), repl.c_str() );
      std::cerr << "reported error " << DiagID << std::endl;

    } // if scop 
    else{
      std::cout << "no scop in this decl group" << std::endl;
    }

#endif
     return true;
  }
#endif

};

static bool once = true;

class ClanAction : public PluginASTAction {

  public:
    ClanAction(){
      if ( once ) {
	std::freopen("/home/incubus/log/clan_redir_stdout.log", "a", stdout);
	std::freopen("/home/incubus/log/clan_redir_stderr.log", "a", stderr);
	setvbuf ( stdout , NULL , _IOLBF , 1024 );
	setvbuf ( stderr , NULL , _IOLBF , 1024 );
	once = false;
      }
      std::cout << "clang action " << this << " created " << std::endl;
    }

    virtual ~ClanAction(){
      std::cout << "clang action " << this << " destroyed " << std::endl;
    }

  //std::set<std::string> ParsedTemplates;
protected:
  // NOTE: stefan this creates the consumer that is given the TU after everything is done
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {

    std::cout << "makeing new Consumer object with compiler instance " << &CI << std::endl;
    auto ret =  llvm::make_unique<ForLoopConsumer>(CI);
    std::cout << "at load ci " << ret.get() << " instance " << &CI << " ast context " << &CI.getASTContext() << " sm " << &CI.getSourceManager() << std::endl;
    std::cout << "done with the new consumer object" << std::endl;
    return std::move(ret);
  }

  // #stefan: here one can parse some arugments for this plugin
  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {
#if 0
    for (unsigned i = 0, e = args.size(); i != e; ++i) {
      llvm::errs() << "Clan arg = " << args[i] << "\n";

      // Example error handling.
      DiagnosticsEngine &D = CI.getDiagnostics();
      if (args[i] == "-an-error") {
        unsigned DiagID = D.getCustomDiagID(DiagnosticsEngine::Error,
                                            "invalid argument '%0'");
        D.Report(DiagID) << args[i];
        return false;
      } else if (args[i] == "-parse-template") {
        if (i + 1 >= e) {
          D.Report(D.getCustomDiagID(DiagnosticsEngine::Error,
                                     "missing -parse-template argument"));
          return false;
        }
        ++i;
        ParsedTemplates.insert(args[i]);
      }
    }
    if (!args.empty() && args[0] == "help")
      PrintHelp(llvm::errs());
#endif
    return true;
  }
  void PrintHelp(llvm::raw_ostream& ros) {
    ros << "Help for Clan plugin goes here\n";
  }

};

}

static FrontendPluginRegistry::Add<ClanAction>
X("clan", "run clan as part of the compiler");
