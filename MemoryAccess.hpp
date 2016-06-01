

#pragma once

// forward declare 
struct pet_expr;
struct isl_map;
struct isl_id;

// Adapter class that uses pet_expr to provide information
class MemoryAccess {
public:
  MemoryAccess (pet_expr* _expr);
  virtual ~MemoryAccess () {}

  bool isReductionLike();
  isl_map* getAccessRelation();

  isl_id* getBaseAddr();

  bool isRead();
  bool isWrite();
  bool isMayWrite();
  bool isMustWrite();

  int getReductionType();

  isl_id* getId();
  isl_id* getArrayId();

private:
  
  pet_expr* expr = nullptr;  

};

