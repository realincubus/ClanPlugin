
#include "ClangPetInterface.hpp"

#include "clang/AST/RecursiveASTVisitor.h"

// isl
#include <isl/options.h>
#include <isl/arg.h>
#include <isl/flow.h>
#include <isl/map.h>
#include <isl/set.h>
#include <isl/ctx.h>

#include "dependency_analysis.h"
#include "plog/Log.h"

#include <chrono>

using namespace clang;
using namespace std;

#include "pet.h"
#include "pet_cxx.h"

class DeclRefVisitor
  : public clang::RecursiveASTVisitor<DeclRefVisitor> {
public:

  DeclRefVisitor( std::vector<NamedDecl*>& _index_refs, SourceLocation _begin, SourceLocation _end, SourceManager& _SM ):
    index_refs(_index_refs),
    begin(_begin),
    end(_end),
    SM(_SM)
  {

  }

	bool isRecordTypeByName( const Type* type_ptr, std::string name ) {
		// check for beeing a record type
		if ( !type_ptr->isRecordType() ) return false;

		// get the declaration 
		auto* record_type = type_ptr->getAs<RecordType>();
		auto* record_decl = record_type->getDecl();

		if ( record_decl->getQualifiedNameAsString() == name ) return true;

		return false;
	}

	bool isRandomAccessStlType( const Type* type ) {
		return isRecordTypeByName( type, "std::array" ) || isRecordTypeByName( type, "std::vector" ) ||
					 isRecordTypeByName( type, "std::__cxx11::basic_string" ) || isRecordTypeByName( type, "std::basic_string" ) ||
		 isRecordTypeByName( type, "std::deque" );
	}

	bool isIteratorType( const Type* type_ptr ) {
		std::cerr <<  __PRETTY_FUNCTION__ << std::endl;
		
		if ( auto typedef_type = dyn_cast_or_null<TypedefType>( type_ptr ) ) {
			// call again with desugared type
			return isIteratorType( typedef_type->desugar().getTypePtr() );
		}

		if ( auto elaborated_type = dyn_cast_or_null<ElaboratedType>(type_ptr) ) {
			auto nested_name_specifier = elaborated_type->getQualifier();

			if ( nested_name_specifier->getKind() == NestedNameSpecifier::TypeSpec ) {
				auto type = nested_name_specifier->getAsType();
				if ( isRandomAccessStlType( type ) ) {

					// check the named_type_qt for its name
					auto named_type_qt = elaborated_type->getNamedType();
					auto type = named_type_qt.getTypePtr();

						if ( named_type_qt.getAsString() == "iterator" ) {
						return true;
					}else{
						return false;
					}
				}    
			}else{
				return false;
			}    
		}else{
			return false;
		}
		return true;
	}

	VarDecl* extract_container( const DeclRefExpr* decl_ref_expr_iterator ) {

		const Expr* init = nullptr;
		if ( auto var_decl = dyn_cast_or_null<VarDecl>(decl_ref_expr_iterator->getDecl()) ) {
			init = var_decl->getInit();
		}else{
			return nullptr;
		}	

		cerr << "dumping init" << endl;
		init->dump();
		
		// to catch containers referencd via container.begin();
		if ( auto expression_with_cleanups = dyn_cast_or_null<ExprWithCleanups>( init ) ){
			cerr  << " ewc  " << endl;
			if ( auto construct = dyn_cast_or_null<CXXConstructExpr>( expression_with_cleanups->getSubExpr() ) ) {
				cerr  << " ctor  " << endl;
				if ( auto temporary_expression = dyn_cast_or_null<MaterializeTemporaryExpr> ( construct->getArg(0) ) ) {
					cerr  << " te  " << endl;
					if ( auto member_call = dyn_cast_or_null<CXXMemberCallExpr>( temporary_expression->GetTemporaryExpr() ) ) {
						cerr << "container begin is referenced by a CXXMemberCallExpr" << endl;

						if ( auto instance = member_call->getImplicitObjectArgument() ) {
							cerr << " implicit object argument " << endl;
							if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>( instance ) ) {
								auto type = decl_ref_expr->getType().getTypePtr();

								auto fd = member_call->getDirectCallee();
								auto name = fd->getDeclName().getAsString();
								cerr << "function called is " << name << endl;

								// TODO if the function is one of the iterator functions and the instance 
								// called is a random access container return the containers decl
								if ( isRandomAccessStlType( type ) && name == "begin" ){
									cerr  << "is container and call to begin end rbegin ... " << endl;
									if ( auto var_decl = dyn_cast_or_null<VarDecl>( decl_ref_expr->getDecl() ) ) {
										return var_decl;
									}
								}
							}
						}
					}
				}
			}
		}

		// 
	}

	// check all operator calls for dereferences of iterators
	bool VisitCXXOperatorCallExpr( const CXXOperatorCallExpr* cxx_operator_call_expr ) {

		auto loc_start = cxx_operator_call_expr->getLocStart();
    if ( SM.isBeforeInTranslationUnit( loc_start , begin ) ) return true;
    if ( SM.isBeforeInTranslationUnit( end , loc_start ) ) return true;

    LOGD << "visited a node CXXOperatorCallExpr node" ;
		if ( cxx_operator_call_expr->getOperator() == OO_Star ) {
			LOGD << "operator is OO_Star" ;
			if ( auto arg0 = cxx_operator_call_expr->getArg(0) ) {
				arg0->dump();
				auto iterator = arg0->IgnoreParenImpCasts();
				if ( isIteratorType ( iterator->getType().getTypePtr() ) ) {
					LOGD << "found a iterator reference" ;
					if ( auto decl_ref_expr = dyn_cast_or_null<DeclRefExpr>(iterator) ) {
						// search this in the list of decls 
						for( int i = 0 ; i < index_refs.size() ; i++ ) {
							auto& index_ref = index_refs[i];
							if ( decl_ref_expr->getDecl() == index_ref ) {
								if ( auto var_decl = extract_container( decl_ref_expr ) ) {
									auto name = var_decl->getNameAsString();
									// take the source range from the operator to get the * character and the included DeclRefExpr
									exclude_ranges.push_back( make_pair( cxx_operator_call_expr->getSourceRange(), name + "["s + "..."s + std::to_string(i) + "..."s + "]"s  ));
									return false;
								}
							}
						}	
					}
				}
			}
		}	

		return true;
	}

  bool VisitDeclRefExpr( const DeclRefExpr* declRefExpr ) {

    auto decl_ref_loc_start = declRefExpr->getLocStart();
    if ( SM.isBeforeInTranslationUnit( decl_ref_loc_start , begin ) ) return true;
    if ( SM.isBeforeInTranslationUnit( end , decl_ref_loc_start ) ) return true;

    LOGD << "visited a node" ;
    for( auto i = 0 ; i < index_refs.size() ; i++ ){
      auto& index_ref = index_refs[i];
      if ( declRefExpr->getDecl() == index_ref ) {
				LOGD << "found a reference" ;
				// push_this occurence to the list of excludes for this index_ref
				exclude_ranges.push_back( make_pair( declRefExpr->getSourceRange(), "..."s + std::to_string(i) + "..."s ));
				return true;
      }
    }


    
    // everything that is not an index_ref passes this point
    return true;
  }
  std::vector<std::pair<SourceRange,std::string>> exclude_ranges;
private:
  std::vector<NamedDecl*>& index_refs;
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

    LOGD << "in_param " << in_param ;
    LOGD << "out_param " << out_param ;

    std::vector<NamedDecl*> parameters;

    if ( in_param > 0 && out_param > 0 ) {
      assert( 0 && "not implemented" );
    }

    // TODO loop over all paramters 
    if ( in_param > 0 ) {
      auto type = isl_dim_in;
      const char* name = isl_space_get_dim_name( space, type, 0 );
      LOGD << "dim in param " << name ;
      assert( 0 && "not implemented" );
    }

    // loop over all parameters 
    for (int i = 0; i < out_param; ++i){
      auto type = isl_dim_out;
      const char* name = isl_space_get_dim_name( space, type, i );
      isl_id* id = isl_space_get_dim_id( space, type, i );
      LOGD << "dim out param " << name ;
      if ( id ) {
	LOGD << "id " << id ;
	void* user_data = isl_id_get_user( id );
	if ( user_data ) {
	  NamedDecl* named_decl = (NamedDecl*) user_data ;
	  parameters.push_back( named_decl );
	}
      }else{
	LOGD << "no id" ;
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

    LOGD << "parsed: " << ret ;

    lexer_result += ret;
    lexer_result += exclude.second;
    
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

  LOGD << "parsed: " << ret ;

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

  LOGD << "lexer_result: " << lexer_result ;

  return lexer_result;

}

// search it by scanning this decl group for the source location // might be very slow
std::string ClangPetInterface::replace_with_placeholder( 
    pet_loc* loc, 
    std::vector<NamedDecl*>& parameters ) {

  // translate this to a source locations 
  LOGD << "statement at " << pet_loc_get_start(loc) << " to " << pet_loc_get_end( loc ) ;
  auto begin_stmt = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
  auto end_stmt = sloc_file.getLocWithOffset( pet_loc_get_end(loc)-1 );
  LOGD << "begin loc " << begin_stmt.printToString(SM) ;
  LOGD << "end loc " << end_stmt.printToString(SM) ;
  
  // TODO i believe it should be enought to do this once
  DeclRefVisitor visitor(parameters, begin_stmt, end_stmt, SM);
  visitor.TraverseStmt( (ForStmt*)for_stmt );

  return getSourceText(begin_stmt, visitor.exclude_ranges, end_stmt, SM );
}

// TODO this is not very save. replace this in the future 
// returns the statements with some placeholders so that the index_refs can be replaced with new index_ref names  
// all statements need to be sorted by their domain name S_0 S_1 S_2 ... 
std::vector<std::string> ClangPetInterface::get_statement_texts( pet_scop* scop )
{

  std::vector<std::pair<std::string, std::string>> domain_text_list;

  // TODO at the begin this has to be the brace of the enclosing block
  //clang::SourceLocation last_loc;
  // loop over all statements 
  for (int i = 0; i < scop->n_stmt; ++i){
    pet_stmt* stmt = scop->stmts[i];
    isl_set* domain = stmt->domain;

    auto parameters = get_parameters_for_pet_stmt( stmt );
	
    pet_loc* loc = stmt->loc;
    // replace the index_ref name in this string with a placeholder
    auto text = replace_with_placeholder( loc, parameters );

    LOGD << "isl_domain: "  ;
    isl_set_dump( domain );
    LOGD << "got text: " << text ;

    const char* tname = isl_set_get_tuple_name( domain );

    domain_text_list.emplace_back( tname, text );
    
  } // loop over all statements

  // sort by domain name
  std::vector<std::string> statement_texts;

  std::sort( begin(domain_text_list), end(domain_text_list), [](auto a , auto b){ return a.first < b.first; } );

  for( auto& element : domain_text_list ){
    statement_texts.push_back( element.second );
  }
  



  return statement_texts;
}


pet_scop* ClangPetInterface::extract_scop( 
    const FunctionDecl* function_decl, 
    std::unique_ptr<std::map<std::string,std::string>>& call_texts
  ) 
{
  
  DiagnosticsEngine& diag = ctx_clang.getDiagnostics();

  LOGD << "handling for_stmt " << ctr++ ;
  Pet pet_scanner( diag, &ctx_clang );
  LOGD << "done creating the Pet scanner object" ;

  auto begin_pet = std::chrono::high_resolution_clock::now();
  LOGD << "calling pet_scop_extract_from_clang_ast" ;
  // sets the instance variable scop
  pet_scanner.pet_scop_extract_from_clang_ast(&ctx_clang,(ForStmt*)for_stmt, (FunctionDecl*) function_decl, call_texts, &scop); 

  LOGD << "done calling pet_scop_extract_from_clang_ast" ;
  auto end_pet = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> diff = end_pet-begin_pet;
  LOGD << "pet time consumption " << diff.count() << " s" ;

  return scop;
}


clang::SourceLocation 
ClangPetInterface::getLocBeginOfScop( ) {
 pet_loc* loc = scop->loc;
 LOGD << "at line " << pet_loc_get_line(loc) ;

 return sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
}

clang::SourceLocation 
ClangPetInterface::getLocRelativeToFileBegin( unsigned int loc ){
 return sloc_file.getLocWithOffset( loc );
}


ClangPetInterface::ClangPetInterface(clang::ASTContext& _ctx, const clang::ForStmt* _for_stmt) : 
  ctx_clang(_ctx),
  SM(ctx_clang.getSourceManager()),
  for_stmt(_for_stmt)
{
   FileID fid = SM.getFileID( for_stmt->getLocStart() );
   sloc_file = SM.translateLineCol(fid,1,1);
}
