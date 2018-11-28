

#include "stdlib_matchers.hpp"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"
#include <iostream>

using namespace std;
using namespace clang;
using namespace clang::ast_matchers;

namespace stdlib_matchers{ 

StatementMatcher inSingleLineCompoundStmt( StatementMatcher innerMatcher ){
    return anyOf(
	    compoundStmt(
		statementCountIs(1),
		hasAnySubstatement(
		    innerMatcher
		)
	    ).bind("is_in_compound"),
		innerMatcher
	    );

}

// TODO also match realFloatingPointType
StatementMatcher makeAccumulateMatcher(){
    return inSingleLineCompoundStmt( 
	binaryOperator(
	    hasOperatorName("+="),
	    hasLHS(
		ignoringParenImpCasts(
		    declRefExpr(
#if 1
		      hasType(
			  isInteger()
		      )
#endif
		    ).bind("reduction_variable")
		)
	    ),
	    hasRHS(
		ignoringParenImpCasts(
		    arraySubscriptExpr(
		      hasBase(
			ignoringParenImpCasts(
			  declRefExpr(
			    hasType(
			      type().bind("array_base_type")
			    )
			  )
			)
		      ),
#if 1
		      hasIndex(
			ignoringParenImpCasts(
			  declRefExpr().bind("iterator_decl_ref")
			)
		      )  
#endif
		    ).bind("array")
		)
	    )
	) 
    );
}

StatementMatcher makeLoopInitMatcher(){
    return inSingleLineCompoundStmt(
	    declStmt(
		hasSingleDecl(
		    varDecl(
			hasInitializer(
			    ignoringParenImpCasts(
				integerLiteral().bind("start_int")
			    )
			)
		    ).bind("iterator_decl")
		)
	    )
    );
}

StatementMatcher makeConditionMatcher() {
    return inSingleLineCompoundStmt(
	    binaryOperator(
		hasOperatorName("<"),
		hasRHS(
		    ignoringParenImpCasts(
			integerLiteral().bind("end_int")
		    )
		)
	    )
    );
}

// TODO this is missing an increment matcher
StatementMatcher makeUseAlgorithmsMatcher(){
    return  forStmt(
		hasLoopInit(
		  makeLoopInitMatcher() 
		),
		hasCondition(
		  makeConditionMatcher()
		),
		hasBody(
		  makeAccumulateMatcher()
		)
	    ).bind("for_stmt")
    ;
}

void search_parallel_algorithms( const clang::ForStmt* for_stmt, clang::SourceManager& SM, clang::ASTContext& ast_context ) {
    /* code */
}

inline std::string getString(const SourceRange sr, const SourceManager &SM) {
  return Lexer::getSourceText(CharSourceRange::getTokenRange(sr), SM,
                              LangOptions());
}

template <typename T>
inline std::string getString(const T *node, const SourceManager &SM) {
  SourceLocation expr_start = node->getBeginLoc();
  SourceLocation expr_end = node->getEndLoc();
  return Lexer::getSourceText(
      CharSourceRange::getTokenRange(SourceRange(expr_start, expr_end)), SM,
      LangOptions());
}

class SequentialAlgorithmCallback : public MatchFinder::MatchCallback {
  public:
    SequentialAlgorithmCallback ( ) 
    {

    }
    // is the function that is called if the matcher finds something
    virtual void run(const MatchFinder::MatchResult &Result){
     std::cout << "stdlib_matchers callback called " << std::endl;
     ASTContext& context = *Result.Context;
     SourceManager& SM = context.getSourceManager();

     called++;

     if ( auto* for_stmt = Result.Nodes.getNodeAs<ForStmt>("for_stmt") ) {

        // QUERY SECTION
	
	auto array_subscript = Result.Nodes.getNodeAs<ArraySubscriptExpr>("array");
	if ( !array_subscript ) {
	  std::cout << "array subscript not found" << std::endl;
	  return;
	}
	
	auto array_lb_node = Result.Nodes.getNodeAs<IntegerLiteral>("start_int");
	auto array_ub_node = Result.Nodes.getNodeAs<IntegerLiteral>("end_int");

	if ( !array_lb_node || !array_ub_node ) {
	  std::cout << "could not determin lb or ub node" << std::endl;
	  return;
	}
	
	// is the variable decl for the index of the loop
	auto iterator_decl = Result.Nodes.getNodeAs<Decl>("iterator_decl");
	// is the reference to possibly iterator_decl that was used to access the array
	auto iterator_decl_ref = Result.Nodes.getNodeAs<DeclRefExpr>("iterator_decl_ref");

	if ( !iterator_decl || ! iterator_decl_ref ) {
	  std::cout << "no iterator decl or decl_ref found" << std::endl;
	  return;
	}

	auto vd_iterator_decl_ref = iterator_decl_ref->getDecl();
	auto vd_iterator_decl = dyn_cast_or_null<ValueDecl>(iterator_decl);

	if ( ! vd_iterator_decl || !vd_iterator_decl_ref ) {
	  std::cout << "could not cast to value declare" << std::endl;
	  return;
	}	 
		
	if ( ! ( vd_iterator_decl == vd_iterator_decl_ref ) ) {
	  std::cout << "iterator access and iterator declaration don't match" << std::endl;
	  return;
	}

	auto reduction_variable = Result.Nodes.getNodeAs<DeclRefExpr>("reduction_variable");

	if ( !reduction_variable ) {
	  std::cout << "could not get the reduction variable" << std::endl;
	  return;
	}

	// if we can determin that the ranges of the loop are the full loop replace the lower and upper boundary with 
	// begin(array) and end(array)
	
	auto array_base_type = Result.Nodes.getNodeAs<Type>("array_base_type");
	if ( !array_base_type ) {
	  std::cout << "could not determin the type of the array" << std::endl;
	  return;
	}

	// END QUERY SECTION

	// be conservative 
	bool is_pointer = true;
	bool is_start_at_begin = false;
	bool is_end_at_end = false;

	if ( auto pointer = dyn_cast_or_null<PointerType>(array_base_type) ) {
	  is_pointer = true;
	  std::cout << "type of the array referenced is a pointer" << std::endl;
	}else{
	  // TODO perhaps check for everything we know that should work
	  is_pointer = false;
	  std::cout << "type of the array referenced is not a pointer" << std::endl;
	}

	auto array_low = getString( array_lb_node, SM );
	auto array_up = getString( array_ub_node, SM );
	auto array_name = getString( array_subscript->getBase(), SM );
	auto reduction_variable_name = getString( reduction_variable, SM );

	auto build_access_to_element = [](std::string name, std::string element) {
	  return string("&") + name + string("[") + element + string("]");
	};

	// all c++ arrays are 0 based
	if ( array_low == "0" ) {
	  is_start_at_begin = true;
	}

	if ( auto constant_array = dyn_cast_or_null<ConstantArrayType>(array_base_type) ) {
	  auto size_ca = constant_array->getSize().getSExtValue();
	  auto size_ub = array_ub_node->getValue().getSExtValue();
	  if ( size_ca == size_ub ) {
	    is_end_at_end = true;
	  }
	}

	// do the checks and add begin and end if you are sure that the loop loops over all elements
	auto lb_access = build_access_to_element(array_name, array_low);
	if ( !is_pointer && is_start_at_begin ) {
	  auto name = add_fqn ? string("std::") : string("") + string("begin");
	  lb_access = name + string("(") + array_name + string(")");
	}

	auto ub_access = build_access_to_element(array_name, array_up);
	if ( !is_pointer && is_end_at_end ) {
	  auto name = add_fqn ? string("std::") : string("") + string("end");
	  ub_access = name + string("(") + array_name + string(")");
	}


      	std::string replacement = string("std::accumulate( ") + 
	  lb_access + 
	  string(", ") + 
	  ub_access + 
	  string(", ") + 
	  reduction_variable_name +
	  string(" );")
	;

	// TODO make it include the <numeric> header // this is not just a funny feature but needed for automatic transformation 
	
	//std::string replacement = string("possible algorithm found ") + array_name + " " + array_low + " " + array_up;

	auto& diag = context.getDiagnostics();
	unsigned DiagID = diag.getCustomDiagID(DiagnosticsEngine::Warning, "this can be replaced with std::accumulate");
	diag.Report(for_stmt->getBeginLoc(), DiagID) 
	  << FixItHint::CreateReplacement(for_stmt->getSourceRange(), replacement.c_str() );

     }
    }

    int called = 0;
    bool add_fqn = true;
};



void search_sequential_algorithms( const clang::ForStmt* for_stmt, clang::SourceManager& SM, clang::ASTContext& ast_context ) {
  std::cout << "searching for sequential algorithms" << std::endl;
  MatchFinder Finder;
  SequentialAlgorithmCallback Fixer;
  Finder.addMatcher( makeUseAlgorithmsMatcher(), &Fixer);
  std::cout << __FILE__ << " " <<  __LINE__  << " running matcher" << std::endl;
  Finder.match(*for_stmt, ast_context);
  std::cout << "done searching for sequential algorithms called " << Fixer.called << std::endl;
}

void analyze( const clang::ForStmt* for_stmt, clang::SourceManager& SM, clang::ASTContext& ast_context, bool is_parallel ){
  if ( is_parallel ) {
    search_parallel_algorithms(for_stmt,SM, ast_context);
  }else{
    search_sequential_algorithms(for_stmt,SM, ast_context);
  }
}

} // stdlib_matchers











