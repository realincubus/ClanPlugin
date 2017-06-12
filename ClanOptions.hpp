
#pragma once

#include <string>

enum class CodeGenerationType {
    ACC,
    OMP,
    TBB,
    CILK,
    HPX,
    CUDA
};

struct ClanOptions{
  CodeGenerationType emit_code_type = CodeGenerationType::ACC;
  bool write_cloog_file = false;
  bool keep_comments = false;
  bool print_guards = true;
  std::string redirect_stdout_file = "";
  std::string redirect_stderr_file = "";

  bool use_profile_data = false;
  std::string perf_data_file = "";
  bool one_at_a_time = false;
};
