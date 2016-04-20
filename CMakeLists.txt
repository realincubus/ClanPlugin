# If we don't need RTTI or EH, there's no reason to export anything
# from the plugin.
if( NOT MSVC ) # MSVC mangles symbols differently, and
                # ClangPlugin.export contains C++ symbols.
  if( NOT LLVM_REQUIRES_RTTI )
    if( NOT LLVM_REQUIRES_EH )
      set(LLVM_EXPORTED_SYMBOL_FILE ${CMAKE_CURRENT_SOURCE_DIR}/ClanPlugin.exports)
    endif()
  endif()
endif()

SET( PLUTO_LIBRARY PLUTO_LIBRARY-NOTFOUND )
SET( PLUTO_CODEGEN_CXX_LIBRARY PLUTO_CODEGEN_CXX_LIBRARY-NOTFOUND )
SET( PET_LIBRARY PET_LIBRARY-NOTFOUND )
SET( ISL15_LIBRARY ISL15_LIBRARY-NOTFOUND )
SET( ISL15_INCLUDE_DIR ISL15_INCLUDE_DIR-NOTFOUND )

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

add_llvm_loadable_module(ClanPlugin ClanPlugin.cpp stdlib_matchers.cpp )
target_link_libraries( ClanPlugin clangASTMatchers libclang ${PLUTO_CODEGEN_CXX_LIBRARY} ${PET_LIBRARY} ${PET_ISL_LIBRARY} clangSema )

if(LLVM_ENABLE_PLUGINS AND (WIN32 OR CYGWIN))
  target_link_libraries(ClangPlugin ${cmake_2_8_12_PRIVATE}
    clangAST
    clangBasic
    clangFrontend
    LLVMSupport
    )
endif()


