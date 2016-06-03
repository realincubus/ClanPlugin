
#include <ClangPetInterface.hpp>

#include "clang/AST/RecursiveASTVisitor.h"

// isl
#include <isl/options.h>
#include <isl/arg.h>
#include <isl/flow.h>
#include <isl/map.h>
#include <isl/set.h>
#include <isl/ctx.h>

#include "dependency_analysis.h"

#include <chrono>

using namespace clang;
using namespace std;

#include "pet.h"
#include "pet_cxx.h"

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
void ClangPetInterface::replace_with_placeholder( 
    pet_loc* loc, 
    std::vector<NamedDecl*>& parameters, 
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
std::vector<std::string> ClangPetInterface::get_statement_texts( pet_scop* scop )
{

  std::vector<std::string> statement_texts;
  // loop over all statements 
  for (int i = 0; i < scop->n_stmt; ++i){
    pet_stmt* stmt = scop->stmts[i];

    auto parameters = get_parameters_for_pet_stmt( stmt );
	
    pet_loc* loc = stmt->loc;
    // replace the iterator name in this string with a placeholder
    replace_with_placeholder( loc, parameters, statement_texts );
    
  } // loop over all statements

  return statement_texts;
}


pet_scop* ClangPetInterface::extract_scop( 
    const FunctionDecl* function_decl, 
    std::unique_ptr<std::map<std::string,std::string>>& call_texts
  ) 
{
  
  DiagnosticsEngine& diag = ctx_clang.getDiagnostics();

  std::cerr << "handling for_stmt " << ctr++ << std::endl;
  Pet pet_scanner( diag, &ctx_clang );
  std::cerr << "done creating the Pet scanner object" << std::endl;

  auto begin_pet = std::chrono::high_resolution_clock::now();
  std::cerr << "calling pet_scop_extract_from_clang_ast" << std::endl;
  // sets the instance variable scop
  pet_scanner.pet_scop_extract_from_clang_ast(&ctx_clang,(ForStmt*)for_stmt, (FunctionDecl*) function_decl, call_texts, &scop); 

  std::cerr << "done calling pet_scop_extract_from_clang_ast" << std::endl;
  auto end_pet = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> diff = end_pet-begin_pet;
  std::cerr << "pet time consumption " << diff.count() << " s" << std::endl;

  return scop;
}


clang::SourceLocation 
ClangPetInterface::getLocBeginOfScop( ) {
 pet_loc* loc = scop->loc;
 std::cerr << "at line " << pet_loc_get_line(loc) << std::endl;

 return sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
}

ClangPetInterface::ClangPetInterface(clang::ASTContext& _ctx, const clang::ForStmt* _for_stmt) : 
  ctx_clang(_ctx),
  SM(ctx_clang.getSourceManager()),
  for_stmt(_for_stmt)
{
   FileID fid = SM.getFileID( for_stmt->getLocStart() );
   sloc_file = SM.translateLineCol(fid,1,1);
}