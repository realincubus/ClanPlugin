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

// clang llvm
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Preprocessor.h"
#include "llvm/Support/raw_ostream.h"

// std
#include <fstream>
#include <chrono>
#include <iostream>
#include <map>
#include <string>
#include <memory>
#include <mutex>

#include "PetPlutoInterface.hpp"
#include "ClangPetInterface.hpp"

using namespace clang;
using namespace clang::ast_matchers;
using namespace pluto_codegen_cxx;

namespace {

class Callback : public MatchFinder::MatchCallback {
  public:
    Callback ( CodeGenerationType _emit_code_type, bool _write_cloog_file ) :
      emit_code_type(_emit_code_type),
      write_cloog_file(_write_cloog_file)
    {

    }
     // is the function that is called if the matcher finds something
     virtual void run(const MatchFinder::MatchResult &Result){
       std::cerr << "plugin: callback called " << std::endl;
       ASTContext& context = *Result.Context;
       SourceManager& SM = context.getSourceManager();

       if ( auto function_decl = Result.Nodes.getNodeAs<FunctionDecl>("function_decl") ) {
	 if ( auto for_stmt = Result.Nodes.getNodeAs<ForStmt>("for_stmt") ) {
	   auto loc = for_stmt->getLocStart();
	   if ( SM.isInMainFile( loc ) ) {

	     std::unique_ptr<std::map<std::string,std::string>> call_texts;

	     ClangPetInterface cp_interface(context, for_stmt);
	     pet_scop* scop = cp_interface.extract_scop( function_decl, call_texts );

	     if ( scop ) {
	       std::cerr << "found a valid scop" << std::endl;
	       
	       // TODO move to pet code
	       // find the text of the original statement
	       auto statement_texts = cp_interface.get_statement_texts( scop );

	       // TODO move common variables into the ctor
	       PetPlutoInterface pp_interface(header_includes, emit_code_type, write_cloog_file);
	       if ( pp_interface.create_scop_replacement( scop, statement_texts, call_texts ) ){

		 std::cerr << "emitting diagnositc" << std::endl;
		 DiagnosticsEngine& diag = context.getDiagnostics();
		 unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "found a scop");
		 std::cerr << "got id " << DiagID << std::endl;

		 auto replacement = pp_interface.getReplacement();
		 auto begin_scop = cp_interface.getLocBeginOfScop();

		 // replace the for statement
		 diag.Report(begin_scop, DiagID) << FixItHint::CreateReplacement(for_stmt->getSourceRange(), replacement.c_str() );
		 std::cerr << "reported error " << DiagID << std::endl;
	       }

	     }
	   }
	 }
       }

     }

     std::set<std::string> header_includes;

  private:
     CodeGenerationType emit_code_type;
     bool write_cloog_file;
};


// return everything beginnign with l to the end of the line
static std::string getText( SourceLocation l, SourceManager& SM ) {

  bool invalid;
  const char* data = SM.getCharacterData( l, &invalid ) ;

  if ( !invalid ) {
     const char* line_end = strchr(data, '\n');
     if ( !line_end ) 
       return data;
     return std::string(data, line_end - data);
  }

  return "invalid";
}


// used to track what the preprocessor does when it enters the separate files
class PPEnterCallback : public clang::PPCallbacks {
public:
    PPEnterCallback ( clang::SourceManager& _SM) :
      SM(_SM)
    {
    }

    std::string parseHeaderName( std::string include_stmt ) {
      // skip " " to first char 
      // check for < or " 
      // search for corresponding closing char
    
      bool local_include = false;
      bool global_include = false;
      bool skip = true;
      std::string name = "";

      for (int i = 0; i < include_stmt.size(); ++i){
	char c = include_stmt[i];

	if ( skip && isWhitespace( std::isspace( c ) ) ) continue;
	if ( c == '"' ) {
	  local_include = true;
	  skip = false;
	  continue;
	}
	if ( c == '<' ) {
	  global_include = true;
	  skip = false;
	  continue;
	}

	if ( local_include && c == '"' ) {
	  break;
	}

	if ( global_include && c == '>' ) {
	  break;
	}

	name += c;

      }

      return name;

    }

    virtual void FileChanged( SourceLocation Loc, FileChangeReason Reason, SrcMgr::CharacteristicKind FileType, FileID PrevFID=FileID() ) {
      if ( Reason == EnterFile ) {
	auto file_begin = Loc;
	auto iloc = SM.getIncludeLoc( SM.getFileID(file_begin) );
	auto text = getText( iloc, SM );
	if ( text != "invalid" ) {
	  std::cerr << "preprocessor " << text << std::endl;
	  auto name = parseHeaderName( text );
	  std::cerr << "preprocessor parsed name " << name << std::endl;
	  // TODO this can happen in parallel lock it with a mutex 
	  std::lock_guard<std::mutex> lock(getMutex());
	  getHeaderSet().insert( name );
	}
      }
    }

    std::mutex& getMutex( ){
      static std::mutex header_mutex;
      return header_mutex;
    }
    // as a first step simply store the header names 
    // TODO add the positions in which they were included
    std::set<std::string>& getHeaderSet(){
      static std::set<std::string> headers;
      return headers;
    }

private:

    clang::SourceManager& SM;

};







class ForLoopConsumer : public ASTConsumer {
public:

  
  ForLoopConsumer( CodeGenerationType _emit_code_type, bool _write_cloog_file, PPEnterCallback* callbacks ) :
    emit_code_type(_emit_code_type),
    write_cloog_file(_write_cloog_file),
    enter_callback( callbacks )
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

  bool isHeaderAlreadyIncluded( std::string header, ASTContext& clang_ctx ) {

    std::lock_guard<std::mutex> lock(enter_callback->getMutex());
    std::cerr << "plugin: number of already included headers " << enter_callback->getHeaderSet().size() << std::endl;
    for( auto& included_header : enter_callback->getHeaderSet() ){
      std::cerr << "comparing: " << included_header << " with " << header  << std::endl;
      if ( header == included_header ) {
	std::cerr << "plugin: header is already included" << std::endl;
	return true;
      }
    }

    return false;
  }


  void add_missing_includes(Callback& Fixer, ASTContext& clang_ctx) {
    for( auto& header : Fixer.header_includes ){

      if ( isHeaderAlreadyIncluded( header, clang_ctx ) ) continue;

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
      unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning, "missing header");

      diag.Report(begin_of_file, id)  << FixItHint::CreateInsertion(begin_of_file, std::string("#include <") + name + ">\n" );
    }
  }
#endif

private: 
  CodeGenerationType emit_code_type;
  bool write_cloog_file;
  PPEnterCallback* enter_callback;

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

protected:

  CodeGenerationType emit_code_type = CodeGenerationType::ACC;
  bool write_cloog_file = false;
  std::string redirect_stdout_file = "";
  std::string redirect_stderr_file = "";

  // NOTE: stefan this creates the consumer that is given the TU after everything is done
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, llvm::StringRef) override;
  bool ParseArgs(const CompilerInstance &CI, const std::vector<std::string> &args) override;
  void PrintHelp(llvm::raw_ostream& ros) {
    ros << "run the plugin with -emit-[openmp,openacc,hpx,tbb,cilk] to get different implementations for the loops\n";
  }


};



PPEnterCallback* setupCallbacks( CompilerInstance& CI ) {

  if ( CI.hasPreprocessor() ) {
    auto& pp = CI.getPreprocessor(); 
    std::cerr << "plugin: got the preprocessor" << std::endl;

    if ( CI.hasSourceManager() ) {
      auto& SM = CI.getSourceManager();

      std::unique_ptr<PPCallbacks> base_ptr( new PPEnterCallback(SM) );
      auto* ret = (PPEnterCallback*)base_ptr.get();
      pp.addPPCallbacks( std::move( base_ptr ) );
    
      return ret;
    }

    }else{
    std::cerr << "ci does not have a preprocessor"  << std::endl;
  }
  return nullptr;
}

std::unique_ptr<ASTConsumer> 
ClanAction::CreateASTConsumer(CompilerInstance &CI, llvm::StringRef){
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
  auto enter_callback = setupCallbacks( CI );
  auto ret =  llvm::make_unique<ForLoopConsumer>(emit_code_type, write_cloog_file, enter_callback);
  std::cerr << "at load ci " << ret.get() << " instance " << &CI << " ast context " << &CI.getASTContext() << " SM " << &CI.getSourceManager() << std::endl;
  std::cerr << "done with the new consumer object" << std::endl;

  // TODO find all header includs in the main file and pass them to the ForLoopConsumer

  return std::move(ret);
}

bool 
ClanAction::ParseArgs(const CompilerInstance &CI, const std::vector<std::string> &args)  {
  std::string* next_arg = nullptr;

  for (unsigned i = 0, e = args.size(); i != e; ++i) {
    llvm::errs() << "Clan arg = " << args[i] << "\n";

    if ( next_arg ) {
      *next_arg = args[i];
      next_arg = nullptr;
      continue;
    }

    if ( args[i] == "-emit-openacc" ) {
      std::cerr << "emiting openacc" << std::endl;
      emit_code_type = CodeGenerationType::ACC;
    }

    if ( args[i] == "-emit-openmp" ) {
      std::cerr << "emiting openmp" << std::endl;
      emit_code_type = CodeGenerationType::OMP;
    }

    if ( args[i] == "-emit-hpx" ) {
      std::cerr << "emiting hpx" << std::endl;
      emit_code_type = CodeGenerationType::HPX;
    }

    if ( args[i] == "-emit-tbb" ) {
      std::cerr << "emiting tbb" << std::endl;
      emit_code_type = CodeGenerationType::TBB;
    }

    if ( args[i] == "-emit-cilk" ) {
      std::cerr << "emiting cilk" << std::endl;
      emit_code_type = CodeGenerationType::CILK;
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


} // namespace end

static FrontendPluginRegistry::Add<ClanAction>
X("clan", "run clan as part of the compiler");
