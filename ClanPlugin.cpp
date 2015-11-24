//===- Clan.cpp ---------------------------------------------===//
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
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Sema/Sema.h"
#include "llvm/Support/raw_ostream.h"
#include <fstream>
#include <chrono>
//#include <clan/clan.h>
//#include <osl/scop.h>
//#include <osl/extensions/irregular.h>
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

extern "C"{
// TODO PlutoProg is not known outside of libpluto
//      since i want to write my own unparser thats not a big problem but its definitly something i 
//      want to change temporarily
//      
//int pluto_multicore_codegen(FILE *cloogfp, FILE *outfp, const PlutoProg *prog);
PlutoProg *scop_to_pluto_prog(osl_scop_p scop, PlutoOptions *options);
void pluto_prog_free(PlutoProg* prog);
int pluto_stmt_is_member_of(int stmt_id, Stmt **slist, int len);
void pluto_detect_transformation_properties(PlutoProg *prog);
//Ploop **pluto_get_all_loops(const PlutoProg *prog, int *num);
}



using namespace clang;
using namespace clang::ast_matchers;

// TODO make header
osl_scop_p handleForLoop( const ForStmt* for_stmt, const SourceManager& SM, std::string filename, std::vector<std::pair<SourceRange,std::string>>& messages, std::vector<std::string>& statement_texts, std::map<osl_statement_p,const clang::Stmt*>& osl_to_clang );


const char* SCOP_ID = "scop";
const char* FOR_LOOP_ID = "for_loop";
const char* LOOP_ITERATOR_ID = "loop_iterator";
const char* LOOP_INITIALIZER_ID = "loop_initializer";
const char* LOOP_CONDITION_LIST_ID = "loop_condition_list";

const char* DECREMENT_ONE_ID = "decrement_one";
const char* INCREMENT_ONE_ID = "increment_one";

const char* CEILD_ID = "ceild";
const char* FLOORD_ID = "floord";

std::ofstream out;


jmp_buf env;
int restore_point = 0;
int restore_error = false;
void signalHandler(int signum) {
  std::cout << "Signal " << signum << " received" << std::endl;
  restore_error = true;
  longjmp(env, 1);
}

namespace {

class ForLoopConsumer : public ASTConsumer {
  CompilerInstance &Instance;
  std::set<std::string> ParsedTemplates;

public:
  ForLoopConsumer(CompilerInstance &Instance,
                         std::set<std::string> ParsedTemplates)
      : Instance(Instance), ParsedTemplates(ParsedTemplates) { llvm::errs() << "consumer created\n" ;}



  StatementMatcher makeLoopConditionMatcher(){
      return expr().bind(LOOP_CONDITION_LIST_ID);
  }

  StatementMatcher makeIncrementMatcher(){
    return anyOf( 
       unaryOperator( hasOperatorName("++") ).bind(INCREMENT_ONE_ID) ,
       binaryOperator( 
	 hasOperatorName("+="),
	 hasRHS(
	   integerLiteral(equals(1))
	 )
       ).bind(INCREMENT_ONE_ID),
       binaryOperator( 
	 hasOperatorName("="),
	 hasLHS( declRefExpr() ),
	 hasRHS( 
	   binaryOperator( 
	     hasOperatorName("+"),
	     hasLHS( declRefExpr() )
	     //hasRHS(  )
	  )
	)
       ).bind(INCREMENT_ONE_ID) 
    );
  }

  StatementMatcher makeDecrementMatcher(){
    return anyOf( 
       unaryOperator( hasOperatorName("--") ).bind(DECREMENT_ONE_ID),
       binaryOperator( 
	 hasOperatorName("-="),
	 hasRHS(
	   integerLiteral(equals(1))
	 )
       ).bind(DECREMENT_ONE_ID),
       binaryOperator( 
	 hasOperatorName("="),
	 hasLHS( declRefExpr() ),
	 hasRHS( 
	   binaryOperator( 
	     hasOperatorName("-"),
	     hasLHS( declRefExpr() )
	     //hasRHS( anything() )
	  )
	)
       ).bind(DECREMENT_ONE_ID) 
    );
  }


  StatementMatcher makeLoopStrideMatcher(){
      return anyOf( 
	makeIncrementMatcher(),
	makeDecrementMatcher()
      );
  }


  StatementMatcher makeIterationStmtMatcher(){
    return forStmt( 
#if 0
	hasLoopInit(
	  makeLoopInitializationMatcher()
	),
#endif
	hasCondition(
	  makeLoopConditionMatcher()
	),
	//hasIncrement(
	//  makeLoopStrideMatcher()
	//),
	unless(
	  hasAncestor(
	    forStmt()
	  )
	)
    ).bind(FOR_LOOP_ID); 
  }

  typedef std::pair<std::string,int> path_and_line_t;
  typedef std::map<path_and_line_t, double > line_profile_t;

  line_profile_t loadProfileDB(){
    std::cout << __PRETTY_FUNCTION__ << std::endl;
    using namespace std;

    line_profile_t statement_to_weight;
    string profile_db_name = "perf.data.eval.db"; // TODO make name changeable
    ifstream in(profile_db_name);
    if ( in.good() ){

      // read the file line by line 
      string line;
      while( getline( in, line ) ) {
	stringstream sstr( line ) ;
	string path;
	int line;
	double weight;
	sstr >> path;
	sstr >> line;
	sstr >> weight;

	statement_to_weight[make_pair(path,line)] = weight;
      }

    }

    std::cout << "leaving " << __PRETTY_FUNCTION__ << std::endl;
    return statement_to_weight;
  }

  bool is_loop_parallel( PlutoProg* prog, Ploop* loop) {
    std::cout << __PRETTY_FUNCTION__ << std::endl;
     bool parallel, i;

      /* All statements under a parallel loop should be of type orig */
      for (i=0; i<loop->nstmts; i++) {
	  if (loop->stmts[i]->type != ORIG) break;
      }
      if (i<loop->nstmts) {
	  return false;
      }

      if (prog->hProps[loop->depth].dep_prop == PARALLEL) {
	  return true;
      }

      parallel = true;

      for (int i=0; i<prog->ndeps; i++) {
	  printf("dep %d ", i);
	  Dep *dep = prog->deps[i];
	  if (IS_RAR(dep->type)) {
	    printf("is rar\n");
	    continue;
	  }
	  assert(dep->satvec != NULL);
	  if (pluto_stmt_is_member_of(prog->stmts[dep->src]->id, loop->stmts, loop->nstmts)
		  && pluto_stmt_is_member_of(prog->stmts[dep->dest]->id, loop->stmts,
		      loop->nstmts)) {
	      printf("both are members of the loops statements: ");
	      if (dep->satvec[loop->depth]) {
		  printf("satvec is != 0 at loop->depth %d\n",loop->depth);
		  parallel = 0;
		  printf("setting parallel to 0\n");
		  break;
	      }
	      printf("\n");
	  }
      }

      printf("pluto_loop_is_parallel returning %d\n",parallel);
      return parallel;
       
  }

  void explain_program( PlutoProg* prog ) {
    int nloops = 0;
    std::cout << "get all loops" << std::endl;
    // TODO cant call this function because we have c++ linkage 
    Ploop** loops = pluto_get_all_loops( prog, &nloops);
    std::cout << "done" << std::endl;
    
    for ( int i = 0; i < nloops; i++) {
      if (is_loop_parallel(prog, loops[i])) {

      }
    }

  }

  void HandleTranslationUnit(ASTContext& context) override {
    
    // TODO call the initialization functions for clan-clang here !!!

    out << "called the function" << std::endl;

    class Callback : public MatchFinder::MatchCallback {
    private:

    public:
      Callback (line_profile_t& _profile_db) :
	profile_db(_profile_db)
      { 
      }

      // TODO filter loops in (system)-headers 
      void handleForLoops( const MatchFinder::MatchResult &Result ){
	std::cout << __PRETTY_FUNCTION__ << std::endl;
	const auto* for_loop = Result.Nodes.getNodeAs<ForStmt>(FOR_LOOP_ID);
	ASTContext& context = *Result.Context;
	const SourceManager& SM = context.getSourceManager();

	all_for_loops.push_back(for_loop);

	assoziateForLoopWithWeight( for_loop, SM );
	std::cout << "leaving " << __PRETTY_FUNCTION__ << std::endl;
      }

      void assoziateForLoopWithWeight( const ForStmt* for_loop, const SourceManager& SM ){
	std::cout << __PRETTY_FUNCTION__ << std::endl;
	using namespace std;
	SourceLocation start =  for_loop->getLocStart();
	SourceLocation end = for_loop->getLocEnd();
	// go through all entries in the map and check whether they are inside the loop
	for( auto&& element : profile_db ){
	  auto& key = element.first;
	  auto& value = element.second;
	  auto filename = SM.getFilename( start );
	  if ( filename != key.first ) continue;
	  
	  auto line_number_start = SM.getSpellingLineNumber( start );
	  auto line_number_end = SM.getSpellingLineNumber( end );

	  if ( key.second >= line_number_start && key.second <= line_number_end ) {
	    for_loop_to_weight[for_loop] += value;
	  }
	}

	for( auto&& element : for_loop_to_weight ){
	    std::cout << "loop " << element.first << " weight " << element.second << std::endl;
	}
	std::cout << "leaving " << __PRETTY_FUNCTION__ << std::endl;
	
	
      }

      void select_target_loop() {
	const ForStmt* max_loop = nullptr;
	double max_weight = -1;

	for( auto&& element : for_loop_to_weight ){
	  if ( element.second > max_weight ){
	    max_weight = element.second;
	    max_loop = element.first;
	  }
	}

	target_for_loop = max_loop;
      }

      // is the function that is called if the matcher finds something
      virtual void run(const MatchFinder::MatchResult &Result){
	std::cout << "callback called" << std::endl;
	handleForLoops( Result ); // from clan-clang
      }

      const ForStmt* getTargetForLoop(){
	// if there is no target for loop 
	// select a random one
	if ( !target_for_loop ) {
	  // there is none return nullptr
	  if ( all_for_loops.size() > 0 ) {
	    auto id = drand48() * all_for_loops.size();
	    return all_for_loops[id];
	  }else{
	    return nullptr;
	  }
	}
	return target_for_loop;
      }

    private:
      const ForStmt* target_for_loop = nullptr;
      line_profile_t& profile_db;
      std::map<const ForStmt*, double> for_loop_to_weight;
      std::vector<const ForStmt*> all_for_loops;
    };

    out << "load profile db" << std::endl;
    // this the entry point for finding loops in the code
    // TODO load the profiling db if available
    auto profile_db = loadProfileDB();
    
    out << "adding matcher"<< std::endl ;
    MatchFinder Finder;
    Callback Fixer(profile_db);
    std::cout << "adding matcher" << std::endl;
    Finder.addMatcher( makeIterationStmtMatcher(), &Fixer);
    std::cout << "running matcher" << std::endl;
    Finder.matchAST(context);

    std::cout << "select a target loop "<< std::endl;
    out << "select a target loop "<< std::endl;
    Fixer.select_target_loop();

    // TODO remove this stuff
    signal(SIGABRT, signalHandler);

    std::cout << "optimize it "<< std::endl;
    out << "optimize it "<< std::endl;
    if ( auto target_for_loop = Fixer.getTargetForLoop() ){

      std::vector<std::string> statement_texts;
      const SourceManager& SM = context.getSourceManager();
      std::vector<std::pair<SourceRange, std::string>> messages;
      std::map<osl_statement_p,const clang::Stmt*> osl_to_clang;
      auto scop = handleForLoop( target_for_loop, SM, "outfile.test.scop.change.this.", messages, statement_texts, osl_to_clang ); 
      // emit all the messages we got from the analysis
      for( auto&& message : messages ){
	
	// dirty hack to get clang to do what i want
	const char a[2000] = "";
	sprintf((char*)a, message.second.c_str() );

	DiagnosticsEngine &D = Instance.getDiagnostics();
	    unsigned DiagID = D.getCustomDiagID(DiagnosticsEngine::Warning, a );
	    D.Report(message.first.getBegin(), DiagID) << message.second;

      }

      // if we where able to extract a scop from this loop. handle it
      if ( scop ) {

	std::thread generator_thread( [&](){

	  restore_point = setjmp(env);

	  if ( restore_error ) {
	    std::cout << "there was an error in generating a new scop" << std::endl;
	    return;
	  }

	  PlutoOptions* pluto_options = pluto_options_alloc(); // memory leak if something goes wrong
	  pluto_options->parallel = true;
	  pluto_options->debug = true;
  	  pluto_options->isldep = true;
	  // TODO this is a catastrophe !!!!! remove it
	  options = pluto_options;
	  //pluto_schedule_osl( scop, pluto_options );
	  FILE* temp = fopen("debug.scop", "w" );
	  osl_scop_print( temp, scop );
	  fclose( temp );

	  std::cout << "generating pluto program from scop" << std::endl;
	  auto prog = scop_to_pluto_prog(scop, pluto_options);
	  std::cout << "done generating pluto program from scop" << std::endl;

	  std::cout << "computing prallelization possibilities" << std::endl;
	  pluto_detect_transformation_properties(prog);
	  std::cout << "computing prallelization possibilities done " << std::endl;
	  std::cout << "ClanPlugin " << prog->ndeps << std::endl;

	  std::stringstream outfp;
	  pluto_codegen_clang::pluto_multicore_codegen( outfp, prog, scop, statement_texts);

	  //std::cout << "try to explain why something is not parallel" << std::endl;
	  //explain_program( prog );

	  std::cout << "done generating cloog code" << std::endl;
	  pluto_prog_free(prog);

	  std::string repl = outfp.str();

	  std::cout << "emitting diagnositc" << std::endl;
	  DiagnosticsEngine &D = Instance.getDiagnostics();
	    unsigned DiagID = D.getCustomDiagID(DiagnosticsEngine::Warning, "found a scop");
	    D.Report(target_for_loop->getLocStart(), DiagID) 
	    << FixItHint::CreateReplacement(SourceRange(target_for_loop->getLocStart(),target_for_loop->getLocEnd()), repl.c_str() );

	}); // thread lambda end;

	generator_thread.join();
      }
    }
    out << "exiting normaly "<< std::endl;
    out.close();
  }
};

class ClanAction : public PluginASTAction {
  std::set<std::string> ParsedTemplates;
protected:
  // #stefan this creates the consumer that is given the TU after everything is done
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 llvm::StringRef) override {
    out.open("/home/incubus/log/handle_translation_unit.log");
    out << __PRETTY_FUNCTION__ << std::endl;
    return llvm::make_unique<ForLoopConsumer>(CI, ParsedTemplates);
  }

  // #stefan: here one can parse some arugments for this plugin
  bool ParseArgs(const CompilerInstance &CI,
                 const std::vector<std::string> &args) override {
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

    return true;
  }
  void PrintHelp(llvm::raw_ostream& ros) {
    ros << "Help for Clan plugin goes here\n";
  }

};

}

static FrontendPluginRegistry::Add<ClanAction>
X("clan", "run clan as part of the compiler");
