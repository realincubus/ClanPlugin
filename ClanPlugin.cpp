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

// logging 
#include "plog/Log.h"
#include "plog/Appenders/ConsoleAppender.h"

// error reporting
#include "error_reporting.hpp"

#include "PetPlutoInterface.hpp"
#include "ClangPetInterface.hpp"

using namespace clang;
using namespace clang::ast_matchers;
using namespace pluto_codegen_cxx;

namespace {

void report_warning(FileID fid, ASTContext& context, unsigned int offset, std::string message ) {
   auto& SM = context.getSourceManager();
   auto sloc_file = SM.translateLineCol(fid,1,1);
   auto clang_src_loc = sloc_file.getLocWithOffset( offset );

   DiagnosticsEngine& diag = context.getDiagnostics();
   unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "%0" );
   diag.Report(clang_src_loc, DiagID) << message ;
}

void report_error(FileID fid, ASTContext& context, unsigned int offset, std::string message) {
   auto& SM = context.getSourceManager();
   auto sloc_file = SM.translateLineCol(fid,1,1);
   auto clang_src_loc = sloc_file.getLocWithOffset( offset );

   DiagnosticsEngine& diag = context.getDiagnostics();
   unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Error, "%0" );
   diag.Report(clang_src_loc, DiagID) << message ;
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

    virtual void FileChanged( SourceLocation Loc, FileChangeReason Reason, SrcMgr::CharacteristicKind FileType, FileID PrevFID=FileID() ) {
      if ( Reason == EnterFile ) {
	auto file_begin = Loc;
	auto iloc = SM.getIncludeLoc( SM.getFileID(file_begin) );
	auto text = getText( iloc, SM );
	if ( text != "invalid" ) {
	  LOGD << "preprocessor " << text ;
	  auto name = parseHeaderName( text );
	  LOGD << "preprocessor parsed name " << name ;
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


// FIXME put this to class scope
bool global_editor_compat = false;

struct IncludesConverter {

  IncludesConverter(ASTContext& _ctx, std::set<std::string> _headers, PPEnterCallback* _enter_callback ) 
    :
      headers(_headers),
      ctx(_ctx),
      enter_callback(_enter_callback)
  {
    
  }

  auto add_include_fixit( std::string header  ) {
    has_insertions = true;
    insertion_text += std::string("#include <") + header + ">\n";
  }

  auto emit_fixit_hint() {
    // TODO skip the lines that begin with a comment 
    //      this way its possible to skip licences that are mostly at the beginning of a file
    // TODO perhaps search for a marker that the user can add to the file 
    //      might be better to add the includes there if the user has to ensure a certain order of includes
    auto& SM = ctx.getSourceManager();
    auto fid = SM.getMainFileID();
    // FileID line column
    auto begin_of_file = SM.translateLineCol( fid, 1, 1 );

    if ( global_editor_compat ) {
      insertion_text += '\n';
    }

    return FixItHint::CreateInsertion(begin_of_file, insertion_text  );
  }

  bool isHeaderAlreadyIncluded( std::string header ) {

    std::lock_guard<std::mutex> lock(enter_callback->getMutex());
    LOGD << "plugin: number of already included headers " << enter_callback->getHeaderSet().size() ;
    for( auto& included_header : enter_callback->getHeaderSet() ){
      LOGD << "comparing: " << included_header << " with " << header  ;
      if ( header == included_header ) {
	LOGD << "plugin: header is already included" ;
	return true;
      }
    }

    return false;
  }

  std::string insertion_text;
  bool has_insertions=false;


  PPEnterCallback* enter_callback;
  std::set<std::string> headers;
  ASTContext& ctx;

};

template < typename T >
T& operator << ( T& lhs, IncludesConverter rhs ) {
  for( auto&& header : rhs.headers ){
    if ( rhs.isHeaderAlreadyIncluded( header ) ) continue;
    rhs.add_include_fixit( header ); 
  }
  if ( rhs.has_insertions ) {
    lhs << rhs.emit_fixit_hint();
  }
  return lhs;
}

class Callback : public MatchFinder::MatchCallback {
  public:
    Callback ( CodeGenerationType _emit_code_type, bool _write_cloog_file, bool _keep_comments, PPEnterCallback* _enter_callback ) :
      emit_code_type(_emit_code_type),
      write_cloog_file(_write_cloog_file),
      keep_comments(_keep_comments),
      enter_callback(_enter_callback)
    {

    }

    void set_print_guards( bool val ) {
      print_guards = val;
    }

     // is the function that is called if the matcher finds something
     virtual void run(const MatchFinder::MatchResult &Result){
       LOGD << "plugin: callback called " ;
       ASTContext& context = *Result.Context;
       SourceManager& SM = context.getSourceManager();

       if ( auto function_decl = Result.Nodes.getNodeAs<FunctionDecl>("function_decl") ) {
	 if ( auto for_stmt = Result.Nodes.getNodeAs<ForStmt>("for_stmt") ) {
	   auto loc = for_stmt->getLocStart();
	   if ( SM.isInMainFile( loc ) ) {

	     function_decl->dumpColor();

	     std::unique_ptr<std::map<std::string,std::string>> call_texts;

	     ClangPetInterface cp_interface(context, for_stmt);
	     cp_interface.set_keep_comments( keep_comments );
	     pet_scop* scop = cp_interface.extract_scop( function_decl, call_texts );

	     if ( scop ) {
	       LOGD << "found a valid scop" ;
	       
	       // TODO move to pet code
	       // find the text of the original statement
	       auto statement_texts = cp_interface.get_statement_texts( scop );

	       reporter_function warning_reporter = [&](unsigned int offset, std::string message){
		  FileID fid = SM.getFileID( for_stmt->getLocStart() );
		  report_warning(fid,context,offset,message);
	       };
	       reporter_function error_reporter = [&](unsigned int offset, std::string message){
		  FileID fid = SM.getFileID( for_stmt->getLocStart() );
		  report_error(fid,context,offset,message);
	       };

	       // TODO move common variables into the ctor
	       PetPlutoInterface pp_interface(header_includes, emit_code_type, write_cloog_file, warning_reporter, error_reporter);
               pp_interface.set_print_guards ( print_guards );

	       if ( pp_interface.create_scop_replacement( scop, statement_texts, call_texts ) ){

		 LOGD << "emitting diagnositc" ;
		 DiagnosticsEngine& diag = context.getDiagnostics();
		 unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "found a loop to optimize");
		 LOGD << "got id " << DiagID ;

		 auto replacement = pp_interface.getReplacement();
		 auto begin_scop = cp_interface.getLocBeginOfScop();

		 // replace the for statement
                 //
                 if ( header_includes.empty() ) {
		   diag.Report(begin_scop, DiagID) << FixItHint::CreateReplacement(for_stmt->getSourceRange(), replacement.c_str() );
                 }else{
		   diag.Report(begin_scop, DiagID) << FixItHint::CreateReplacement(for_stmt->getSourceRange(), replacement.c_str() ) << IncludesConverter(context,header_includes, enter_callback);
                   //for( auto&& header_include : header_includes ){
                     //diag.Report(begin_scop, DiagID) << add_include_fixit( context, header_include );
                   //}
                 }



		 auto begin_str = for_stmt->getLocStart().printToString(SM);	
		 auto end_str = for_stmt->getLocEnd().printToString(SM);	
		 LOGD << "reported error for range " << begin_str << " to " << end_str << " diag id " << DiagID ;
	       }else{
		 // TODO this is the point to emit information about why it was not possible to 
		 // parallelize this loop
		 for( auto& pet_explanation : pp_interface.pet_expanations ){

		   unsigned int loc = std::get<0>(pet_explanation);
		   auto clang_src_loc = cp_interface.getLocRelativeToFileBegin( loc );

		   DiagnosticsEngine& diag = context.getDiagnostics();
		   unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "Dependency: %0" );
		   diag.Report(clang_src_loc, DiagID) << std::get<2>(pet_explanation) ;
		 }
	       }

	     }
	   }
	 }
       }

     }

     std::set<std::string> header_includes;

  private:
     CodeGenerationType emit_code_type;
     // TODO needs restructuring
     bool write_cloog_file;
     bool keep_comments;
     bool print_guards = true;
     PPEnterCallback* enter_callback;
};






class ForLoopConsumer : public ASTConsumer {
public:

  
  ForLoopConsumer( 
      CodeGenerationType _emit_code_type, 
      bool _write_cloog_file, 
      PPEnterCallback* callbacks, 
      bool _keep_comments ) 
    :
    emit_code_type(_emit_code_type),
    write_cloog_file(_write_cloog_file),
    enter_callback( callbacks ),
    keep_comments(_keep_comments)
  { 
    LOGD << "for loop consumer created " << this ;
  }

  ~ForLoopConsumer(){
    LOGD << "for loop consumer destroyed " << this ;
  }

  // all for loops that dont have a nested for loop
  StatementMatcher makeForLoopMatcher(){
    return forStmt(
	unless(
	  hasAncestor(
	    forStmt()
	  )
	)
      ).bind("for_stmt");
  }

  // match function declarations that are not in function templates
  DeclarationMatcher makeFunctionMatcher(){
    return functionDecl(
	forEachDescendant(
	  makeForLoopMatcher() 
	),
	unless(
	  hasAncestor(
	    functionTemplateDecl()
	  )
	)	
    ).bind("function_decl");
  }


  // match function declarations that are in function templates and are instantiations
  DeclarationMatcher makeInstantiatedFunctionMatcher(){
    return functionDecl(
	forEachDescendant(
	  makeForLoopMatcher() 
	),
	hasAncestor(
	  functionTemplateDecl()
	),
	isTemplateInstantiation()	
    ).bind("function_decl");
  }

  void HandleTranslationUnit( ASTContext& clang_ctx ) {
    auto begin = std::chrono::high_resolution_clock::now();
    MatchFinder Finder;
    Callback Fixer(emit_code_type, write_cloog_file, keep_comments, enter_callback);

    Fixer.set_print_guards( print_guards ) ;

    LOGD << "adding matcher" ;
    Finder.addMatcher( makeFunctionMatcher(), &Fixer);
    Finder.addMatcher( makeInstantiatedFunctionMatcher(), &Fixer);
    LOGD << "running matcher" ;
    Finder.matchAST(clang_ctx);

    //add_missing_includes(Fixer, clang_ctx);

    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> diff = end-begin;
    LOGD << "plugin: time consumption " << diff.count() << " s" ;
  }

  void set_print_guards( bool val ){
    print_guards = val;
  } 

private: 
  CodeGenerationType emit_code_type;
  bool write_cloog_file;
  bool keep_comments;
  bool print_guards;
  PPEnterCallback* enter_callback;

};

static bool once_std_out = true;
static bool once_std_err = true;

class ClanAction : public PluginASTAction {

  public:
    ClanAction(){
      static bool once = true;
      if ( once ) {
	static plog::ConsoleAppender<plog::TxtFormatter> consoleAppender;
	plog::init(plog::debug, &consoleAppender); 
	once = false;
	LOGD << "logger initialized ";
      }

      LOGD << "clang action " << this << " created " ;
    }

    virtual ~ClanAction(){
      LOGD << "clang action " << this << " destroyed ";
    }

    // Automatically run the plugin after the main AST action
    PluginASTAction::ActionType getActionType() override {
      return AddAfterMainAction;
    }

protected:

  CodeGenerationType emit_code_type = CodeGenerationType::ACC;
  bool write_cloog_file = false;
  bool keep_comments = false;
  bool print_guards = true;
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
    LOGD << "plugin: got the preprocessor" ;

    if ( CI.hasSourceManager() ) {
      auto& SM = CI.getSourceManager();

      std::unique_ptr<PPCallbacks> base_ptr( new PPEnterCallback(SM) );
      auto* ret = (PPEnterCallback*)base_ptr.get();
      pp.addPPCallbacks( std::move( base_ptr ) );
    
      return ret;
    }

    }else{
    LOGD << "ci does not have a preprocessor"  ;
  }
  return nullptr;
}

std::unique_ptr<ASTConsumer> 
ClanAction::CreateASTConsumer(CompilerInstance &CI, llvm::StringRef){


  if ( redirect_stdout_file != "" ) {
    LOGD << "redirect_stdout_file " << redirect_stdout_file;
    // TODO mutex
    if ( once_std_out ) {
      std::freopen(redirect_stdout_file.c_str(), "a", stdout);
      setvbuf ( stdout , NULL , _IOLBF , 1024 );
      once_std_out = false;
    }     
  }
  if ( redirect_stderr_file != "" ) {
    LOGD << "redirect_stderr_file " << redirect_stderr_file;
    // TODO mutex
    if ( once_std_err ) {
      std::freopen(redirect_stderr_file.c_str(), "a", stderr);
      setvbuf ( stderr , NULL , _IOLBF , 1024 );
      once_std_err = false;
    }     
  }
  LOGD << "makeing new Consumer object with compiler instance " << &CI ;
  auto enter_callback = setupCallbacks( CI );
  auto ret =  llvm::make_unique<ForLoopConsumer>(emit_code_type, write_cloog_file, enter_callback, keep_comments);
  ret->set_print_guards( print_guards );
  LOGD << "at load ci " << ret.get() << " instance " << &CI << " ast context " << &CI.getASTContext() << " SM " << &CI.getSourceManager() ;
  LOGD << "done with the new consumer object" ;

  // TODO find all header includs in the main file and pass them to the ForLoopConsumer

  return std::move(ret);
}

bool 
ClanAction::ParseArgs(const CompilerInstance &CI, const std::vector<std::string> &args)  {
  std::string* next_arg = nullptr;

  for (unsigned i = 0, e = args.size(); i != e; ++i) {
    LOGD << "Clan arg = " << args[i];

    if ( next_arg ) {
      *next_arg = args[i];
      next_arg = nullptr;
      continue;
    }

    if ( args[i] == "-emit-openacc" ) {
      LOGD << "emiting openacc" ;
      emit_code_type = CodeGenerationType::ACC;
    }

    if ( args[i] == "-emit-openmp" ) {
      LOGD << "emiting openmp" ;
      emit_code_type = CodeGenerationType::OMP;
    }

    if ( args[i] == "-emit-hpx" ) {
      LOGD << "emiting hpx" ;
      emit_code_type = CodeGenerationType::HPX;
    }

    if ( args[i] == "-emit-tbb" ) {
      LOGD << "emiting tbb" ;
      emit_code_type = CodeGenerationType::TBB;
    }

    if ( args[i] == "-emit-cilk" ) {
      LOGD << "emiting cilk" ;
      emit_code_type = CodeGenerationType::CILK;
    }

    if ( args[i] == "-emit-cuda" ) {
      LOGD << "emiting cuda" ;
      emit_code_type = CodeGenerationType::CUDA;
    }

    if ( args[i] == "-keep-comments" ) {
      LOGD << "keep comments on" ;
      keep_comments = true;
    }

    if ( args[i] == "-editor-compat" ) {
      LOGD << "editor compat mode" ;
      global_editor_compat = true;
      write_cloog_file = false;
    }

    if ( args[i] == "-print-guards" ) {
      LOGD << "print guards if needed" ;
      print_guards = true;
    }

    if ( args[i] == "-dont-print-guards" ) {
      LOGD << "dont print guards" ;
      print_guards = false;
    }

    // add new back-ends here 

    if ( args[i] == "-write-cloog-file" ) {
      LOGD << "writing cloog file" ;
      write_cloog_file = true;
    }

    if ( args[i] == "-redirect-stdout" ) {
      LOGD << "redirecting stdout" ;
      next_arg = &redirect_stdout_file;
    }

    if ( args[i] == "-redirect-stderr" ) {
      LOGD << "redirecting stderr" ;
      next_arg = &redirect_stderr_file;
    }

  }

  return true;
}


} // namespace end

// TODO change name
static FrontendPluginRegistry::Add<ClanAction>
X("clan", "run clan as part of the compiler");
