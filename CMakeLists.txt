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

add_subdirectory( clan )
add_subdirectory( pluto_codegen_clang )

include_directories( pluto_codegen_clang )

add_llvm_loadable_module(ClanPlugin ClanPlugin.cpp)
target_link_libraries( ClanPlugin clangASTMatchers clan-clang_static pluto polylib64 libclang pluto_codegen_clang )

if(LLVM_ENABLE_PLUGINS AND (WIN32 OR CYGWIN))
  target_link_libraries(ClangPlugin ${cmake_2_8_12_PRIVATE}
    clangAST
    clangBasic
    clangFrontend
    LLVMSupport
    )
endif()
