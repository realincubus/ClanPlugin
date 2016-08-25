CMAKE_MINIMUM_REQUIRED(VERSION 2.6)
PROJECT(OptimizerPlugin)

SET( CMAKE_BUILD_TYPE RELEASE )
SET( CMAKE_EXPORT_COMPILATION_DATABASE on )

SET( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DCLANG_ENABLE_ARCMT -DCLANG_ENABLE_OBJC_REWRITER -DCLANG_ENABLE_STATIC_ANALYZER -std=c++14 -fvisibility-inlines-hidden -ffunction-sections -fdata-sections -fno-common -fno-strict-aliasing -Wl,--version-script,${CMAKE_SOURCE_DIR}/ClanPlugin.exports")

# if enabled tries to build everything with module support # seams to be buggy
# does not work with anything else than clang
if ( USE_MODULES )
  SET(  CMAKE_CXX_FLAGS 
    ${CMAKE_CXX_FLAGS} 
    -fmodules 
    -fno-implicit-module-maps 
    -fmodule-map-file=${CMAKE_SOURCE_DIR}/module.modulemap 
    -fmodules-cache-path=${CMAKE_SOURCE_DIR}/cache 
    -fmodules-decluse 
  )
endif()

# put all libraries into a lib folder
SET(LIBRARY_OUTPUT_PATH ${PROJECT_BINARY_DIR}/lib)

SET( PLUTO_LIBRARY PLUTO_LIBRARY-NOTFOUND )
SET( PLUTO_CODEGEN_CXX_LIBRARY PLUTO_CODEGEN_CXX_LIBRARY-NOTFOUND )
SET( PET_LIBRARY PET_LIBRARY-NOTFOUND )

# search for clang and libclang
find_package(Clang REQUIRED )

if ( Clang_FOUND ) 
  message ( "-- Clang Targets Found" )
endif()

find_package(LLVM REQUIRED)

if ( LLVM_FOUND ) 
  message ( "-- LLVM Targets Found" )
endif()

# for add_llvm_loadable_module
message( "-- Adding LLVM macros" ) 
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)

# search for lib pluto
find_package(pluto)
# search for pluto_codegen_cxx
find_package(pluto_codegen_cxx)
# search for pet and pets isl version
find_package(pet)

include_directories( ${PET_INCLUDE_DIR} )
include_directories( ${PET_ISL_INCLUDE_DIR} )
include_directories( ${PLUTO_INCLUDE_DIR}  )
include_directories( ${PLUTO_CODEGEN_CXX_INCLUDE_DIR} )
include_directories( plog/include )

# llvm and clang definitions and include dirs
include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})
include_directories(${Clang_INCLUDE_DIRS})
add_definitions(${Clang_DEFINITIONS})

# build the loadable module for the clang compiler
add_llvm_loadable_module( 
  ClanPlugin 
  ClanPlugin.cpp 
  dependency_analysis.cpp
  stdlib_matchers.cpp 
  MemoryAccess.cpp
  Scop.cpp
  ScopStmt.cpp
  PetPlutoInterface.cpp
  pluto_compat.cpp
  ClangPetInterface.cpp
)

target_link_libraries( 
  ClanPlugin 
  clangASTMatchers 
  #libclang 
  ${PLUTO_CODEGEN_CXX_LIBRARY} 
  ${PET_LIBRARY} 
  ${PET_ISL_LIBRARY} 
  /root/pluto_install/lib/libcloog-isl.a
  /root/pluto_install/lib/libpluto.a
  /root/pluto_install/lib/libisl.a
  clangSema 
)

install ( TARGETS ClanPlugin 
  RUNTIME DESTINATION bin
  LIBRARY DESTINATION lib
)
