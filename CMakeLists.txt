cmake_minimum_required(VERSION 3.28)

project(ProyectoCompi2Aux)

set(CMAKE_CXX_STANDARD 17)

add_executable(IMP test_imp_fun.cpp imp.cpp imp_parser.cpp imp_printer.cpp imp_interpreter.cpp imp_value.cpp imp_typechecker.cpp imp_type.cpp imp_codegen.cpp)

add_executable(SVM svm_run.cpp svm_parser.cpp svm.cpp)

