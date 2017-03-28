
#include <isl/space.h>
#include <isl/map.h>
#include <isl/set.h>
#include <isl/union_map.h>
#include <isl/union_set.h>
#include <isl/ctx.h>

#include "pluto_compat.h"
#include "plog/Log.h"

#include <pluto_codegen_cxx.hpp>

#include <cassert>

#include <iostream>

// disable logging for this file
#undef LOGD
#define LOGD LOGD_IF(false)

using namespace std;

using namespace pluto_codegen_cxx;

struct union_set_rename_data {
    isl_union_set* new_set;
    std::vector<int>* rename_table;
};

struct map_rename_data {
    isl_union_map* new_map;
    std::vector<int>* rename_table;
};

isl_set* rename_set( isl_set* set, std::vector<int>& rename_table ) {
  const char *name = isl_set_get_tuple_name(set);
  char *new_name = (char*)malloc(sizeof(const char) * 10 );

  // extract name and change it with the rename table
  assert(isdigit(name[2]));
  int id = atoi(&name[2]);

  sprintf( new_name, "S_%d", rename_table[id] );

  LOGD << "renaming from " << name << " to " << new_name ;    

  auto new_isl_set = isl_set_set_tuple_name(set, new_name );
  isl_set_dump( new_isl_set );
  const char *set_name = isl_set_get_tuple_name(new_isl_set);
  LOGD << "done renaming new name is " << set_name ;    

  return new_isl_set;
}

// TODO use the rename_set function
// let the domain names be in accending order without gaps
isl_union_set* linearize_union_set( isl_space* space, isl_union_set* domains, std::vector<int>& rename_table ) {

  cerr << "dumping rename table" << endl;
  int ctr = 0;
  for( auto& i : rename_table ) {
    cerr << ctr++ << " " << i << endl;
  }

  union_set_rename_data user_data;
  // start with 0 
  isl_union_set* new_domain = isl_union_set_empty( space );

  user_data.new_set = new_domain; 
  user_data.rename_table = &rename_table;

  isl_union_set_foreach_set(domains, 
      []( __isl_take isl_set* set, void* user ){
	  union_set_rename_data* user_data = (union_set_rename_data*)(user);

	  const char *name = isl_set_get_tuple_name(set);
	  char *new_name = (char*)malloc(sizeof(const char) * 10 );

	  // TODO do this with std::string and strdup
	  
	  // extract name and change it with the rename table
	  assert(isdigit(name[2]));
	  int numeric_id = atoi(&name[2]);

	  std::vector<int>& rename_table = (*user_data->rename_table);
	  int new_numeric_id = rename_table[numeric_id];

	  if ( new_numeric_id < 0 || new_numeric_id >= rename_table.size() ) { 
	    cerr << "plugin: element was filtered" << endl;
	    return (isl_stat)0;
	  }

	  sprintf( new_name, "S_%d", new_numeric_id );
	  cerr << "renaming from " << name << " to " << new_name << endl;    

	  isl_id* id = isl_set_get_tuple_id( set );
	  void* id_user_data = isl_id_get_user( id );
	  if ( id_user_data ) {
	    StatementInformation* sinfo = (StatementInformation*)id_user_data;
	    cerr << "text" << sinfo->statement_text << endl ;
	  }
	  cerr << "old user data " << id_user_data << endl;

	  isl_ctx* ctx = isl_id_get_ctx( id ) ;
	  isl_id* new_id = isl_id_alloc( ctx, new_name, id_user_data );
	  auto new_isl_set = isl_set_set_tuple_id( set, new_id );

	  const char *set_name = isl_set_get_tuple_name(new_isl_set);
	  cerr << "done renaming new name is " << set_name << endl;    

	  isl_union_set_add_set( user_data->new_set, new_isl_set );

	  {
	    isl_id* new_id = isl_set_get_tuple_id( new_isl_set );
	    void* new_user_data = isl_id_get_user( new_id );
	    cerr << "new user data " << new_user_data << endl;
	  }
	  return (isl_stat)0;    
      }, 
      &user_data
  );
  return new_domain;
}

isl_stat rename_map( isl_map* map, void* user ) { 
  map_rename_data* user_data = (map_rename_data*)(user);
  LOGD << __FILE__ << " " << __LINE__ ;

  auto rename = [&](isl_map* map, isl_dim_type t){
    LOGD << __FILE__ << " " << __LINE__ ;
    const char *name = isl_map_get_tuple_name(map,t);
    if ( name == nullptr ) {
      LOGD << "pluto compat: could not get the name for dim type " << t ;
      return (isl_map*)nullptr;
    }
    LOGD << "tuple name is " << name ;

    char *new_name = (char*)malloc(sizeof(const char) * 10 );

    assert(isdigit(name[2]));
    int numeric_id = atoi(&name[2]);

    std::vector<int>& rename_table = (*user_data->rename_table);
    int new_numeric_id = rename_table[numeric_id];

    if ( new_numeric_id < 0 || new_numeric_id >= rename_table.size() ) { 
      LOGD << "plugin: element was filtered" ;
      return (isl_map*)nullptr;
    }

    sprintf( new_name, "S_%d", new_numeric_id );
    LOGD << "renaming from " <<  name << " to " << new_name ;    

    isl_id* id = isl_map_get_tuple_id( map, t  );
    void* id_user_data = isl_id_get_user( id );
    if ( id_user_data ) {
      StatementInformation* sinfo = (StatementInformation*)id_user_data;
      LOGD << "text" << sinfo->statement_text ;
    }
    LOGD << "old user data " << id_user_data ;

    isl_ctx* ctx = isl_id_get_ctx( id ) ;
    isl_id* new_id = isl_id_alloc( ctx, new_name, id_user_data );
    auto new_isl_map = isl_map_set_tuple_id( map, t, new_id );
    
    isl_map_dump( map );
#if 0
    auto new_isl_map = isl_map_set_tuple_name(map,t, new_name );
    isl_map_dump( new_isl_map );
#endif
    const char *set_name = isl_map_get_tuple_name(new_isl_map, t );
    LOGD << "done renaming" ;    
    return new_isl_map;
  };

  if ( auto new_map = rename( map, isl_dim_in ) ){
    if ( auto new_new_map = rename( new_map, isl_dim_out ) ) {
      isl_union_map_add_map( user_data->new_map, new_new_map );
      return (isl_stat)0;
    }
    isl_union_map_add_map( user_data->new_map, new_map );
    return (isl_stat)0;
  }

  LOGD << __FILE__ << " " << __LINE__ ;
  return (isl_stat)0;    
}

isl_union_map* linearize_union_map( isl_space* space, isl_union_map* map, std::vector<int>& rename_table){
  LOGD << __FILE__ << " " << __LINE__ ;
  map_rename_data user_data;
  isl_union_map* new_map = isl_union_map_empty( space );
  user_data.new_map = new_map; 
  user_data.rename_table = &rename_table;

  isl_union_map_foreach_map(map, 
      rename_map, 
      &user_data
  ); 

  LOGD << __FILE__ << " " << __LINE__ ;
  return new_map;
}


