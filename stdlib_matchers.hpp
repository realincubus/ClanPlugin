
#pragma once

#include "clang/AST/AST.h"

namespace stdlib_matchers {
  void analyze( const clang::ForStmt* for_stmt, clang::SourceManager& SM, clang::ASTContext& ast_context, bool is_parallel );
}
