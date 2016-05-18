#pragma once

struct union_set_rename_data {
    isl_union_set* new_set;
    std::vector<int>* rename_table;
};

struct map_rename_data {
    isl_union_map* new_map;
    std::vector<int>* rename_table;
};

inline isl_set* rename_set( isl_set* set, std::vector<int>& rename_table ) {
  const char *name = isl_set_get_tuple_name(set);
  char *new_name = (char*)malloc(sizeof(const char) * 10 );

  // extract name and change it with the rename table
  assert(isdigit(name[2]));
  int id = atoi(&name[2]);

  sprintf( new_name, "S_%d", rename_table[id] );

  std::cerr << "renaming from " << name << " to " << new_name << std::endl;    

  auto new_isl_set = isl_set_set_tuple_name(set, new_name );
  isl_set_dump( new_isl_set );
  const char *set_name = isl_set_get_tuple_name(new_isl_set);
  std::cerr << "done renaming new name is " << set_name << std::endl;    

  return new_isl_set;
}

inline isl_map* rename_map( isl_map* map, std::vector<int>& rename_table ) {
  isl_dim_type t = isl_dim_in;
  const char *name = isl_map_get_tuple_name(map,t);
  char *new_name = (char*)malloc(sizeof(const char) * 10 );

  // extract name and change it with the rename table
  assert(isdigit(name[2]));
  int id = atoi(&name[2]);

  sprintf( new_name, "S_%d", rename_table[id] );

  std::cerr << "renaming from " << name << " to " << new_name << std::endl;    

  auto new_isl_map = isl_map_set_tuple_name(map, t, new_name );
  isl_map_dump( new_isl_map );
  const char *map_name = isl_map_get_tuple_name(new_isl_map, t);
  std::cerr << "done renaming new name is " << map_name << std::endl;    

  return new_isl_map;
}


// TODO use the rename_set function
// let the domain names be in accending order without gaps
inline isl_union_set* linearize_union_set( isl_space* space, isl_union_set* domains, std::vector<int>& rename_table ) {
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

	  // extract name and change it with the rename table
	  assert(isdigit(name[2]));
	  int id = atoi(&name[2]);

	  sprintf( new_name, "S_%d", (*user_data->rename_table)[id] );

	  std::cerr << "renaming from " << name << " to " << new_name << std::endl;    

	  auto new_isl_set = isl_set_set_tuple_name(set, new_name );
	  isl_set_dump( new_isl_set );
	  const char *set_name = isl_set_get_tuple_name(new_isl_set);
	  std::cerr << "done renaming new name is " << set_name << std::endl;    

	  isl_union_set_add_set( user_data->new_set, new_isl_set );

	  return (isl_stat)0;    
      }, 
      &user_data
  );
  return new_domain;
}

inline isl_union_map* linearize_union_map( isl_space* space, isl_union_map* schedule, std::vector<int>& rename_table){
  map_rename_data user_data;
  isl_union_map* new_map = isl_union_map_empty( space );
  user_data.new_map = new_map; 
  user_data.rename_table = &rename_table;

  isl_union_map_foreach_map(schedule, 
      []( __isl_take isl_map* map, void* user ) {
	map_rename_data* user_data = (map_rename_data*)(user);

	isl_dim_type t = isl_dim_in;
	const char *name = isl_map_get_tuple_name(map,t);
	char *new_name = (char*)malloc(sizeof(const char) * 10 );

	assert(isdigit(name[2]));
	int id = atoi(&name[2]);

	std::vector<int>& rename_table = (*user_data->rename_table);
	int new_id = rename_table[id];

	if ( new_id < 0 || new_id >= rename_table.size() ) { 
	  std::cerr << "plugin: element was filtered" << std::endl;
	  return (isl_stat)0;
	}

	sprintf( new_name, "S_%d", new_id );
	std::cerr << "renaming from " <<  name << " to " << new_name << std::endl;    
	
	isl_map_dump( map );
	auto new_isl_map = isl_map_set_tuple_name(map,t, new_name );
	isl_map_dump( new_isl_map );
	const char *set_name = isl_map_get_tuple_name(new_isl_map, t );
	std::cerr << "done renaming" << std::endl;    

	isl_union_map_add_map( user_data->new_map, new_isl_map );

	return (isl_stat)0;    
      }, 
      &user_data
  ); 

  return new_map;
}


