

#include "ScopStmt.hpp"
#include <iostream>
#include "pet.h"
#include "pet_cxx.h"

#include <isl/union_set.h>

using namespace std;

static int helper( pet_expr* expr, void* user ){
  std::vector<MemoryAccess>* memory_accesses = (std::vector<MemoryAccess>*) user;
  memory_accesses->emplace_back( expr );
  return 0;
}

ScopStmt::ScopStmt (pet_stmt* _s, isl_union_map* _schedule) :
  stmt(_s),
  schedule( _schedule )
{
  std::cerr << "dep analysis: new stmt with " << " x accesses " << std::endl;
  pet_tree_foreach_access_expr( 
      stmt->body, &helper ,
      &memory_accesses
  );
  
}


isl_set* ScopStmt::getDomain(){
  return isl_set_copy(stmt->domain);    
}


isl_space* ScopStmt::getDomainSpace() const {
  return isl_set_get_space(stmt->domain);
}

isl_map* ScopStmt::getSchedule(){
  isl_set *Domain = getDomain();
  if (isl_set_is_empty(Domain)) {
    isl_set_free(Domain);
    return isl_map_from_aff(
	isl_aff_zero_on_domain(isl_local_space_from_space(getDomainSpace())));
  }
  auto *Schedule = isl_union_map_copy(schedule);
  Schedule = isl_union_map_intersect_domain(
      Schedule, isl_union_set_from_set(isl_set_copy(Domain)));
  if (isl_union_map_is_empty(Schedule)) {
    isl_set_free(Domain);
    isl_union_map_free(Schedule);
    return isl_map_from_aff(
	isl_aff_zero_on_domain(isl_local_space_from_space(getDomainSpace())));
  }
  auto *M = isl_map_from_union_map(Schedule);
  M = isl_map_coalesce(M);
  M = isl_map_gist_domain(M, Domain);
  M = isl_map_coalesce(M);
  return M;

}

std::string ScopStmt::getTupleName(){
  auto domain = getDomain();
  const char* name = isl_set_get_tuple_name( domain );
  isl_set_free( domain );
  return name;
}

unsigned int 
ScopStmt::getSourceLocation(){
  auto loc = stmt->loc;
  return pet_loc_get_start(loc);
}

unsigned int 
ScopStmt::getSourceLocationEnd(){
  auto loc = stmt->loc;
  return pet_loc_get_end(loc);
}

struct isl_space {
        int ref;

        struct isl_ctx *ctx;

        unsigned nparam;
        unsigned n_in;          /* zero for sets */
        unsigned n_out;         /* dim for sets */

        isl_id *tuple_id[2];
        isl_space *nested[2];

        unsigned n_id;
        isl_id **ids;
};

isl_set* 
ScopStmt::ignoreTrueOrFalseBranch( isl_set* set, isl_set* domain_parent ) {
 cerr << __PRETTY_FUNCTION__ << endl;
#if 0
 auto space = isl_set_get_space( set ); 
 auto local_space = isl_local_space_from_space( space );

 isl_space_dump( space );

 isl_local_space_dump( local_space );

 if ( isl_local_space_dim(local_space, isl_dim_param) > 0 ) {
  cerr << "multiple params " << endl;
 }

 auto n_div = isl_local_space_dim(local_space, isl_dim_div);
 if ( n_div ) {
  cerr << "got n_div " << endl;
 }else if ( isl_space_is_params(isl_local_space_get_space(local_space)) ) {
  cerr << "got params " << endl;
 }

 if ( isl_space_is_params(space) ) {
    cerr << "false branch" << endl;
 }else{
    cerr << "true branch" << endl;
    if ( isl_space_is_set( space ) ){
      cerr << "is set " << endl;
      for ( int i = 0 ; i < isl_space_dim(space,isl_dim_set); ++i ){
	cerr << "i " << i << endl;
      }	
    }
 }

 cerr << "my ptr " << space << endl;
 cerr << "in " << isl_space_dim( space, isl_dim_in ) << endl;
 cerr << "out " << isl_space_dim( space, isl_dim_out ) << endl;
 cerr << "set " << isl_space_dim( space, isl_dim_set ) << endl;
 cerr << "nested[0] " << space->nested[0] << endl;
 cerr << "nested[1] " << space->nested[1] << endl;

 cerr << "tuple[0] " << space->tuple_id[0] << endl;
 cerr << "tuple[1] " << space->tuple_id[1] << endl;


 auto nested_space = space->nested[1];

 cerr << "nested->tuple[0] " << nested_space->tuple_id[0] << endl;
 cerr << "nested->tuple[1] " << nested_space->tuple_id[1] << endl;

 isl_space_dump( nested_space );

 auto print_name = [&](isl_space* space, auto type) {
   cerr << "printing tuple name for " << type << endl;
   if ( isl_space_has_tuple_name( space, type ) ) {
     auto name = isl_space_get_tuple_name( space, type );
     if ( name ) {
       cerr << "name: " << name << endl;
     }
   }
 };

 cerr << "for space " << endl;
 print_name( space,isl_dim_in );
 print_name( space,isl_dim_out );
#if 0
 print_name( space,isl_dim_set );
 print_name( space,isl_dim_param );
 print_name( space,isl_dim_cst );
 print_name( space,isl_dim_div );
#endif

 cerr << "for nested space " << endl;
 print_name( nested_space,isl_dim_in );
#if 1
 print_name( nested_space,isl_dim_out );
 print_name( nested_space,isl_dim_set );
 print_name( nested_space,isl_dim_param );
 print_name( nested_space,isl_dim_cst );
 print_name( nested_space,isl_dim_div );
#endif

 auto print_id = [&](auto space, auto type) {
   cerr << "printing tuple id for " << type << endl;
   if ( isl_space_has_tuple_id( space, type ) ) {
     auto id = isl_space_get_tuple_id( space, type );
     if ( id ) {
       isl_id_dump(id);
     }
   }
 };


 print_id( nested_space, isl_dim_in );
 print_id( nested_space, isl_dim_out );
 print_id( nested_space, isl_dim_set );
 print_id( nested_space, isl_dim_param );
 print_id( nested_space, isl_dim_cst );
 print_id( nested_space, isl_dim_div );

  auto print_dim = [&](auto space, auto type, int dim ) {
   cerr << "printing dim name for " << type << " and dim " << dim << endl;
   if ( isl_space_has_dim_name( space, type, dim ) ) {
     auto name = isl_space_get_dim_name( space, type, dim );
     if ( name ) {
      cerr << "name: " << name << endl;
     }
   }
 };

 for( int i = 0; i < 2 ; i++ ) {
   print_dim( nested_space, isl_dim_in, i );
   print_dim( nested_space, isl_dim_out, i );
   print_dim( nested_space, isl_dim_set , i);
   print_dim( nested_space, isl_dim_param, i );
   print_dim( nested_space, isl_dim_cst, i );
   print_dim( nested_space, isl_dim_div, i );
 }

 isl_set_dump( domain_parent );
#endif

#if 0
 auto print_dim = [&](auto type, int dim ) {
   cerr << "printing dim name for " << type << " and dim " << dim << endl;
   if ( isl_space_has_dim_name( space, type, dim ) ) {
     auto name = isl_space_get_dim_name( space, type, dim );
     if ( name ) {
      cerr << "name: " << name << endl;
     }
   }
 };

 for( int i = 0; i < 2 ; i++ ) {
   print_dim( isl_dim_in, i );
   print_dim( isl_dim_out, i );
   print_dim( isl_dim_set , i);
   print_dim( isl_dim_param, i );
   print_dim( isl_dim_cst, i );
   print_dim( isl_dim_div, i );
 }

 auto print_dim_id = [&](auto type, int dim ) {
   cerr << "printing dim id for " << type << " and dim " << dim << endl;
   if ( isl_space_has_dim_id( space, type, dim ) ) {
     auto id = isl_space_get_dim_id( space, type, dim );
     if ( id ) {
      isl_id_dump( id );
     }
   }
 };

 for( int i = 0; i < 2 ; i++ ) {
   print_dim_id( isl_dim_in, i );
   print_dim_id( isl_dim_out, i );
   print_dim_id( isl_dim_set , i);
   print_dim_id( isl_dim_param, i );
   print_dim_id( isl_dim_cst, i );
   print_dim_id( isl_dim_div, i );
 }
#endif

 //auto new_set = isl_set_reset_space( set, access_domain_space );
 cerr << "done " << __PRETTY_FUNCTION__ << endl;
 return domain_parent; 
}

int isl_map_compatible_domain(struct isl_map *map, struct isl_set *set)
{
        int m;
        if (!map || !set)
                return -1;
	auto map_dim = isl_map_get_space( map );	
	auto set_dim = isl_set_get_space( set );	
        m = isl_space_match(map_dim, isl_dim_param, set_dim, isl_dim_param);
        if (m < 0 || !m)
                return m;
        return isl_space_tuple_is_equal(map_dim, isl_dim_in,
                                        set_dim, isl_dim_set);
}

// TODO extract this mehtod

isl_map* rename(isl_map* map, isl_dim_type t, int rename_to ){
  cerr << __FILE__ << " " << __LINE__ << endl ;
  const char *name = isl_map_get_tuple_name(map,t);
  if ( name == nullptr ) {
    cerr << "pluto compat: could not get the name for dim type " << t ;
    return (isl_map*)nullptr;
  }
  cerr << "tuple name is " << name << endl;

  char *new_name = (char*)malloc(sizeof(const char) * 10 );

  assert(isdigit(name[2]));
  int numeric_id = atoi(&name[2]);

  int new_numeric_id = rename_to;

  sprintf( new_name, "S_%d", new_numeric_id );
  cerr << "renaming from " <<  name << " to " << new_name  << endl;    

  isl_id* id = isl_map_get_tuple_id( map, t  );
  void* id_user_data = isl_id_get_user( id );
#if 0
  if ( id_user_data ) {
    StatementInformation* sinfo = (StatementInformation*)id_user_data;
    LOGD << "text" << sinfo->statement_text ;
  }
  cerr << "old user data " << id_user_data ;
#endif

  isl_ctx* ctx = isl_id_get_ctx( id ) ;
  isl_id* new_id = isl_id_alloc( ctx, new_name, id_user_data );
  auto new_isl_map = isl_map_set_tuple_id( map, t, new_id );
  
  isl_map_dump( map );

  const char *set_name = isl_map_get_tuple_name(new_isl_map, t );
  cerr << "done renaming"  << endl;    
  return new_isl_map;
};


__isl_give isl_union_map* 
ScopStmt::getAccessesOfType(
    std::function<bool(MemoryAccess &)> Predicate, 
    isl_union_map* Accesses,
    isl_set* DomainParent, 
    AllowedAccessTypes allowed_access_type 
){

  cerr << __PRETTY_FUNCTION__ << endl;

#if 1
  for( auto& sub_statement : sub_statements ) {
    auto domain = sub_statement->getDomain() ;
    cerr << "has substatements: " << endl; 
    isl_set_dump(domain );

    // TODO under the assumption that we can not determin which 
    // branch of a condition will be taken i need to assume both will be
    // domains are represented like { [S_4[i] -> [1]] : i >= 0 and i <= 9 }
    // which tells me that this will be excuted in the true branch [1] (false branch [0])
    // this information has to be evaluated
    
    //Domain = ignoreTrueOrFalseBranch( Domain, isl_map_get_space(AccessDomain) );
    
    cerr << "recursing to substatement" << endl;
    // if we have a parent take the parent and pass it to the getAccessType function
    isl_set* parent = nullptr;
    if ( DomainParent ) {
      parent = DomainParent;
      cerr << "this is a node in the recursion tree passing " << parent << endl;
    }else{
      parent = getDomain();
      cerr << "this is the root of the recursion " << parent << endl;
    }
    // TODO transfer the writes and reads of the sub statements to this statement
    if( auto sub_statement_accesses = sub_statement->getAccessesOfType( Predicate, Accesses, parent, IntersectParent ) ) {
      Accesses = sub_statement_accesses;
      cerr << "write accesses" << endl;
      isl_union_map_dump( Accesses );
    }else{
      cerr << "error in write access detection of substatements" << endl;
      exit(-1);
    }
  }
#endif 

  for (MemoryAccess& MA : *this) {
      if (!Predicate(MA))
        continue;

      isl_set *Domain = this->getDomain();
      cerr << "depana: domain:" << endl;
      isl_set_dump( Domain );
      isl_map *AccessDomain = MA.getAccessRelation();
      cerr << "depana: accessrelation:" << endl;
      isl_map_dump( AccessDomain );

      if ( !AccessDomain ) 
	continue;

      // TODO issue a warning that tells the user that we are doing something
      //      very crazy here

      if ( allowed_access_type == IntersectParent ) {
	auto intersec_with = DomainParent ;
	cerr << "before rename" << endl;
	isl_map_dump( AccessDomain );
	cerr << "after rename" << endl;

	if ( !DomainParent ) {
	  cerr << "dont have a domain parent " << endl;
	  return nullptr;
	}

	cerr << "trying to get the tuple name from " << DomainParent << endl;
	if ( isl_set_has_tuple_name( DomainParent ) ) {
	  cerr << "has tuple name " << DomainParent << endl;
	}else{
	  cerr << "does not have a tuple name " << DomainParent << endl;
	  // TODO dont return a nullptr. this means there was nothing found and not that there was an error
	  //
	  return isl_union_map_coalesce(Accesses);
	}
	const char *name = isl_set_get_tuple_name(DomainParent);
	if ( name && !isdigit(name[2]) ){
	  cerr << "parent has no normal statement name" << endl;
	  return isl_union_map_coalesce(Accesses);
	}
	int numeric_id = atoi(&name[2]);
	AccessDomain = rename( AccessDomain, isl_dim_in, numeric_id );
	isl_map_dump( AccessDomain );

	if ( isl_map_compatible_domain( AccessDomain, intersec_with ) ) {
	  cerr << "intersecting domain with accessdomain" << endl;
	  AccessDomain = isl_map_intersect_domain(AccessDomain, intersec_with);
	  isl_map_dump( AccessDomain );
	  cerr << "done intersecting domain with accessdomain" << endl;
	  Accesses = isl_union_map_add_map(Accesses, AccessDomain);
	}
      }else{
	if ( isl_map_compatible_domain( AccessDomain, Domain ) ) {
	  cerr << "intersecting domain with accessdomain" << endl;
	  AccessDomain = isl_map_intersect_domain(AccessDomain, Domain);
	  isl_map_dump( AccessDomain );
	  cerr << "done intersecting domain with accessdomain" << endl;
	  Accesses = isl_union_map_add_map(Accesses, AccessDomain);
	}
      }


  }

  auto ret =  isl_union_map_coalesce(Accesses);
  isl_union_map_dump( ret );

  return ret;
}
