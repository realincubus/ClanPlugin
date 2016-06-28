

#include "clang/AST/AST.h"

// interface between clang and pet
struct pet_scop;
struct pet_loc;

class ClangPetInterface {
public:
    ClangPetInterface (
	clang::ASTContext& _ctx, 
	const clang::ForStmt* _for_stmt
	);

    virtual ~ClangPetInterface () {}

    pet_scop* extract_scop( 
      const clang::FunctionDecl* function_decl,
      std::unique_ptr<std::map<std::string,std::string>>& call_texts
    ); 

    clang::SourceLocation getLocBeginOfScop( );
    clang::SourceLocation getLocRelativeToFileBegin( unsigned int loc );
    std::vector<std::string> get_statement_texts( pet_scop* scop );

private:


    std::string replace_with_placeholder( 
      pet_loc* loc, 
      std::vector<clang::NamedDecl*>& parameters
    );

    clang::ASTContext& ctx_clang;
    clang::SourceManager& SM;
    const clang::ForStmt* for_stmt;
    // pets source locations are all relative to the file begin
    // so i need to store the begin of the file the scop is in
    clang::SourceLocation sloc_file;

    pet_scop* scop;
    
};
