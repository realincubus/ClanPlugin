

#pragma once


#include <vector>
#include <string>
#include <map>
#include <memory>
#include "pluto_codegen_cxx.hpp"
#include <libpluto.h>
#include "ClanOptions.hpp"

#include "error_reporting.hpp"

struct isl_union_set;
struct pet_scop;


enum class DependencyAnalysisType {
    PollyLike,
    Pluto
};

class PetPlutoInterface {
public:
    PetPlutoInterface (
	std::set<std::string>& _header_includes, 
        ClanOptions& _clan_options,
	reporter_function warning_reporter,
	reporter_function error_reporter
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

    std::vector<std::tuple<int,int,std::string>> pet_expanations;

    void set_print_guards( bool val ) {
      clan_options.print_guards = val;
    }

protected:


  bool build_rename_table( isl_union_set* domains, std::vector<int>& table );
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

  std::string replacement;

  DependencyAnalysisType dependency_analysis_style = DependencyAnalysisType::PollyLike;

  reporter_function warning_reporter;
  reporter_function error_reporter;

  ClanOptions& clan_options;

};
