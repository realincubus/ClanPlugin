
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

#if 0
  // add a newline at the end if it does not exist
  if ( lexer_result.size() > 0 ) {
    if ( lexer_result.back() != '\n' ){
      lexer_result.push_back('\n');
    }
  }
#endif

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

class PetStmtVisitor
  : public clang::RecursiveASTVisitor<PetStmtVisitor> {
public:

  PetStmtVisitor( SourceLocation _begin, SourceLocation _end, SourceManager& _SM ):
    begin(_begin),
    end(_end),
    SM(_SM)
  {

  }

  bool VisitStmt( const Stmt* stmt ) {

    auto stmt_loc_start = stmt->getLocStart();
    if ( SM.isBeforeInTranslationUnit( stmt_loc_start , begin ) ) return true;
    if ( SM.isBeforeInTranslationUnit( end , stmt_loc_start ) ) return true;

    found = stmt;
    return false;
  }

  const Stmt* get_found() {
    return found;
  }

private:

  const Stmt* found = nullptr;
  SourceLocation begin;
  SourceLocation end;
  SourceManager& SM;

};

class ParentStmtVisitor
  : public clang::RecursiveASTVisitor<ParentStmtVisitor> {
public:

  ParentStmtVisitor( const Stmt* _child )
  {
    child = _child;
  }

  bool VisitCompoundStmt( const CompoundStmt* cstmt ) {
    cstmt->dump();
    for( auto& s : cstmt->body() ) {
      if ( child == s ) {
	found = cstmt;
      }
    }
    return false;
  }

  const CompoundStmt* get_parent( ) {
    return found;
  }

private:

  const Stmt* child = nullptr;
  const CompoundStmt* found = nullptr;

};

std::tuple<std::string,std::string,std::string> ClangPetInterface::get_comments( pet_loc* loc ){
  // TODO find the statement and its surrounding that coresponds to this location
  
  auto begin_stmt = sloc_file.getLocWithOffset( pet_loc_get_start(loc) );
  auto end_stmt = sloc_file.getLocWithOffset( pet_loc_get_end(loc)-1 );
  PetStmtVisitor visitor( begin_stmt, end_stmt, SM);

  cerr << "doing comment detection " << endl;
  cerr << "----------------------- " << endl;
  cerr << "----------------------- " << endl;
  cerr << "----------------------- " << endl;
  cerr << "----------------------- " << endl;

  // first find the statement itself
  visitor.TraverseStmt( (ForStmt*) for_stmt );

  std::string upper_comment_text;
  std::string right_comment_text;
  std::string lower_comment_text;

  if ( auto stmt = visitor.get_found() ) {
    // second find its direct parent
    ParentStmtVisitor parent_visitor( stmt );
    parent_visitor.TraverseStmt( (ForStmt*)for_stmt);
    if ( auto parent = parent_visitor.get_parent() ) {
      // get our position in this compound statement 
      int position = -1;
      for( auto i = parent->body_begin(), e = parent->body_end(); i != e ; i++ ) {
	if ( *i == stmt ) {
	  position = std::distance( i , parent->body_begin() );
	}
      }

      std::string previous_text;
      std::string following_text;
      bool starts_with_lbrace = false;
      bool ends_with_rbrace = false;

      {
	SourceLocation begin_previous_text;
	SourceLocation end_previous_text;

	if ( position == 0 )  {
	  // if we are the first in this compound statement 
	  // use LBracLoc
	  begin_previous_text = parent->getLBracLoc();
	  starts_with_lbrace = true;
	}else{
	  // get the previous statement and get its end
	  auto previous = *(parent->body_begin() + (position-1));
	  begin_previous_text = previous->getLocEnd();
	  // TODO correct this to be on the next line if we are not also on the same line as previous 
	}
	
	end_previous_text = stmt->getLocStart();
	previous_text = Lexer::getSourceText(
	  CharSourceRange::getCharRange(
	    SourceRange(
	      Lexer::getLocForEndOfToken(begin_previous_text,0,SM,LangOptions()), 
	      end_previous_text
	    )
	  ),
	  SM,
	  LangOptions()
	);

	cerr << "previous text " << previous_text << endl;
      }

      {
	SourceLocation begin_following_text = stmt->getLocEnd();
	SourceLocation end_following_text;

	if ( position == parent->size()-1 ) {
	  // if we are the last in this compound statement 
	  // use RBracLoc
	  end_following_text = parent->getRBracLoc();
	  ends_with_rbrace = true;
	}else{
	  // get the following statement and get its end
	  auto following = *(parent->body_begin() + (position+1));
	  end_following_text = following->getLocEnd();
	}
	
	following_text = Lexer::getSourceText(
	  CharSourceRange::getCharRange(
	    SourceRange(
	      Lexer::getLocForEndOfToken(begin_following_text,0,SM,LangOptions()), 
	      end_following_text
	    )
	  ),
	  SM,
	  LangOptions()
	);

	following_text = following_text.substr(1);
	cerr << "following text " << following_text << endl;
      }

      // TODO decompose previous and following text into upper right and lower text
      
      {
	stringstream prev_stream( previous_text );
	std::string line;

	std::vector<std::string> upper_comment;

	if ( starts_with_lbrace ) {
	  // handle the text after the '{' character
	  getline( prev_stream, line );
	  if ( !std::all_of(line.begin(),line.end(),::isspace) ) {
	    upper_comment.push_back(line);
	    cerr << "pushing " << line << endl;
	  }else{
	    cerr << "skipping " << line << endl;
	  }
	}
	// read the remaining text
	while( getline( prev_stream, line ) ){
	  upper_comment.push_back(line);
	  cerr << "pushing " << line << endl;
	}

	for( int i = 0 ; i < upper_comment.size()-1; i++ ) {
	  auto& s = upper_comment[i];
	  upper_comment_text += s + '\n';
	}

	cerr << "upper_comment_text " << upper_comment_text << endl;
      }

      {
	stringstream following_stream( following_text );
	std::string line;

	std::vector<std::string> following_comment;

	while( getline( following_stream, line ) ){
	  following_comment.push_back(line);
	  cerr << "pushing " << line << endl;
	}


	right_comment_text = following_comment.front();

	for( int i = 1 ; i < following_comment.size()-1; i++ ) {
	  auto& s = following_comment[i];
	  lower_comment_text += s + '\n';
	}

	cerr << "right_comment_text " << right_comment_text << endl;
	cerr << "lower_comment_text " << lower_comment_text << endl;
      }
	
    }
  }

  cerr << "----------------------- " << endl;
  cerr << "----------------------- " << endl;
  cerr << "----------------------- " << endl;
  cerr << "----------------------- " << endl;
  cerr << "done doing comment detection " << endl;
  return make_tuple( upper_comment_text,right_comment_text,lower_comment_text );
}

// TODO this is not very save. replace this in the future 
// returns the statements with some placeholders so that the index_refs can be replaced with new index_ref names  
// all statements need to be sorted by their domain name S_0 S_1 S_2 ... 
std::vector<std::string> ClangPetInterface::get_statement_texts( pet_scop* scop )
{

  std::vector<std::pair<int, std::string>> domain_text_list;

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

    if ( keep_comments ) {
      auto comments = get_comments( loc );
      auto upper_comment = std::get<0>( comments );
      auto right_comment = std::get<1>( comments );
      auto lower_comment = std::get<2>( comments );
      text = upper_comment + text + right_comment + '\n' + lower_comment;
    }else{
      if ( text[text.size()-1] != '\n' ){
	text += '\n';
      }
    }

    LOGD << "isl_domain: "  ;
    isl_set_dump( domain );
    LOGD << "got text: " << text ;

    const char* tname = isl_set_get_tuple_name( domain );

    if ( tname == nullptr ) {
#if 0
      // TODO means a map might have come into this domain ( sometimes representing a kill statement in a 
      //      special scope
      auto space = isl_set_get_space(domain);
      isl_space_dump( space );
      //tname = isl_space_get_tuple_name( space , isl_dim_in ); 
      //tname = isl_space_get_dim_name( space , isl_dim_in, 0 ); 
      cerr << "is set " << isl_space_is_set( space ) << endl;
      cerr << "has t name in " << isl_space_has_tuple_name( space, isl_dim_set ) << endl;
      cerr << "has t id " << isl_space_has_tuple_name( space, isl_dim_set ) << endl;
      cerr << "has t dim 0 set " << isl_space_has_dim_name( space, isl_dim_set, 0 ) << endl;
      cerr << "has t dim 1 set " << isl_space_has_dim_name( space, isl_dim_set, 1 ) << endl;
#if 1
      //tname = isl_space_get_dim_name( space, isl_dim_all, 1 );
      tname = isl_set_get_dim_name( domain, isl_dim_param, 1 );
#endif
#endif
      continue;
    }

    cerr << "tuple name is " << tname << endl;
    
    if (!isdigit(tname[2])) {
      cerr << "this is not a digit" << endl;
      // TODO care about this later and do proper error handling
      exit(-1);
    }
    int id = atoi(&tname[2]);

    domain_text_list.emplace_back( id, text );
    
  } // loop over all statements

  cerr << "before fill" << endl;
  for( auto pair : domain_text_list ) {
    cerr << pair.first << " " << pair.second << endl;
  }


  // sort by domain name
  std::vector<std::string> statement_texts;

  std::sort( begin(domain_text_list), end(domain_text_list), [](auto a , auto b){ return a.first < b.first; } );

  // fill in the gaps and push to the string vector
  int ctr = 0 ;
  //for( int i = 0; i < domain_text_list.size(); i++ ){
  for (int i = 0; i < scop->n_stmt; ++i){
    if ( i < domain_text_list.size() ) {
      auto& element = domain_text_list[i];
      if ( element.first == ctr ) {
	statement_texts.push_back( element.second );
      }else{
	statement_texts.push_back( "no text\n" );
	i--;
      }
    }else{
      statement_texts.push_back( "no text\n" );
    }
    ctr++;
  }


  cerr << "after fill" << endl;
  ctr = 0;
  for( auto s : statement_texts ) {
    cerr << ctr++ << " " << s << endl;
  }

#if 0
  for( auto& element : domain_text_list ){
    statement_texts.push_back( element.second );
  }
#endif

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
