

#pragma once


#include <vector>
#include <string>
#include <map>
#include <memory>
#include "pet.h"
#include "pet_cxx.h"
#include "pluto_compat.h"
#include "pluto_codegen_cxx.hpp"
#include <libpluto.h>

struct isl_union_set;
struct pet_scop;


enum class CodeGenerationType {
    ACC,
    OMP,
    TBB,
    CILK,
    HPX
};

class PetPlutoInterface {
public:
    PetPlutoInterface (
	std::set<std::string>& _header_includes, 
	CodeGenerationType _emit_code_type, 
	bool _write_cloog_file
    ); 
    virtual ~PetPlutoInterface () {}

    bool create_scop_replacement(
      pet_scop* scop, 
      std::vector<std::string>& statement_texts,
      std::unique_ptr<std::map<std::string,std::string>>& call_texts
    );

    std::string getReplacement(){
      return replacement;
    }

protected:


  void build_rename_table( isl_union_set* domains, std::vector<int>& table );
  isl_union_set *collect_non_kill_domains(struct pet_scop *scop );
  PlutoProg* pet_to_pluto_prog( 
      pet_scop* scop, 
      PlutoOptions* pluto_options, 
      std::vector<std::string>& statement_texts, 
      std::unique_ptr<std::map<std::string,std::string>>& call_texts 
  );
  PlutoProg* compute_deps( 
    pet_scop* pscop, 
    PlutoOptions* options, 
    std::vector<std::string>& statement_texts,
    std::unique_ptr<std::map<std::string,std::string>>& call_texts 
  );


  std::set<std::string>& header_includes;
  CodeGenerationType emit_code_type;
  bool write_cloog_file;

  std::string replacement;

};
