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

add_library( osl SHARED IMPORTED)
set_property(TARGET osl PROPERTY IMPORTED_LOCATION ${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/openscop/.libs/libosl.so)


add_library( cloog-isl SHARED IMPORTED)
set_property(TARGET cloog-isl PROPERTY IMPORTED_LOCATION ${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/cloog-isl/.libs/libcloog-isl.so)


include_directories( pluto_src/cloog-isl/include )
include_directories( pluto_src/openscop/include )
include_directories( pluto_src/candl/include )
include_directories( pluto_src/piplib/include )
include_directories( pluto_src/include )

add_subdirectory( clan )
add_subdirectory( pluto_codegen_clang )

include_directories( pluto_codegen_clang )
include_directories( pluto_src/src )

include(ExternalProject)

ExternalProject_Add( pluto_clang
  PREFIX	    ${CMAKE_CURRENT_SOURCE_DIR}
  TMP_DIR           ${CMAKE_CURRENT_SOURCE_DIR}/temp
  STAMP_DIR         ${CMAKE_CURRENT_SOURCE_DIR}/stamp
  BINARY_DIR        ${CMAKE_CURRENT_SOURCE_DIR}/build
  SOURCE_DIR	    ${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/
 CONFIGURE_COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/local_install.sh"
 BUILD_COMMAND make -j 8 -C ${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/
 INSTALL_COMMAND make install -C ${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/
)

ExternalProject_Get_Property( pluto_clang install_dir)


add_llvm_loadable_module(ClanPlugin ClanPlugin.cpp)
target_link_libraries( ClanPlugin clangASTMatchers clan-clang_static plutocore libclang pluto_codegen_clang )

if(LLVM_ENABLE_PLUGINS AND (WIN32 OR CYGWIN))
  target_link_libraries(ClangPlugin ${cmake_2_8_12_PRIVATE}
    clangAST
    clangBasic
    clangFrontend
    LLVMSupport
    )
endif()

add_dependencies(ClanPlugin pluto_clang)
add_library( pluto SHARED IMPORTED)
set_property(TARGET pluto PROPERTY IMPORTED_LOCATION ${CMAKE_CURRENT_SOURCE_DIR}/pluto_src/install/lib/libpluto.so)

#needed includes for my superset library


# TODO move this into a separate project
# this is needed to get some functions from pluto that are not build with the normal libpluto
SET( CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fPIC -fno-exceptions -fno-rtti -fPIC -fvisibility-inlines-hidden -fno-omit-frame-pointer -DCLOOG_INT_GMP=1" )

add_library ( plutocore SHARED 
  pluto_src/src/ast_transform.c 
  pluto_src/src/pluto_codegen_if.c
)

target_link_libraries( plutocore pluto clast-clang_acc )


