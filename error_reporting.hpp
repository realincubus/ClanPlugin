
#pragma once

#include <functional>

//void report_warning(SourceManager& SM, FileID fid, ASTContext& context, int line, int col, std::string message );

typedef std::function<void(unsigned int,std::string message)> reporter_function;
