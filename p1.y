%{
#include <cstdio>
#include <list>
#include <vector>
#include <map>
#include <iostream>
#include <string>
#include <memory>
#include <stdexcept>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/FileSystem.h"

using namespace llvm;
using namespace std;

// Need for parser and scanner
extern FILE *yyin;
int yylex();
void yyerror(const char*);
int yyparse();
 
// Needed for LLVM
string funName;
Module *M;
LLVMContext TheContext;
IRBuilder<> Builder(TheContext);
 
%}

%union {
  vector<string> *params_list;
  int val;
  int imm;
}

/*%define parse.trace*/

%type <params_list> params_list

%token IN FINAL
%token ERROR
%token <imm> NUMBER
%token <reg> ID 
%token BINV INV PLUS MINUS XOR AND OR MUL DIV MOD
%token COMMA ENDLINE ASSIGN LBRACKET RBRACKET LPAREN RPAREN NONE COLON
%token REDUCE EXPAND

%precedence BINV
%precedence INV
%left PLUS MINUS OR
%left MUL DIV AND XOR MOD

%type <val> expr
%type <val> ensemble

%start program

%%

program: inputs statements_opt final
{
  YYACCEPT;
}
;

inputs:   IN params_list ENDLINE
{  
  std::vector<Type*> param_types;
  for(auto s: *$2)
    {
      param_types.push_back(Builder.getInt32Ty());
    }
  ArrayRef<Type*> Params (param_types);
  
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getInt32Ty(),Params,false);

  // Create a main function
  Function *Function = Function::Create(FunType,GlobalValue::ExternalLinkage,funName,M);

  int arg_no=0;
  for(auto &a: Function->args()) {
    // iterate over arguments of function
    // match name to position
  }
  
  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));

}
| IN NONE ENDLINE
{ 
  // Create int function type with no arguments
  FunctionType *FunType = 
    FunctionType::get(Builder.getInt32Ty(),false);

  // Create a main function
  Function *Function = Function::Create(FunType,  
         GlobalValue::ExternalLinkage,funName,M);

  //Add a basic block to main to hold instructions, and set Builder
  //to insert there
  Builder.SetInsertPoint(BasicBlock::Create(TheContext, "entry", Function));
}
;

params_list: ID
{
  $$ = new vector<string>;
  // add ID to vector
}
| params_list COMMA ID
{
  // add ID to $1
}
;

final: FINAL ensemble endline_opt
{
  // FIX ME, ALWAYS RETURNS 0
  Builder.CreateRet(Builder.getInt32(0));
}
;

endline_opt: %empty | ENDLINE;
            

statements_opt: %empty
            | statements;

statements:   statement 
            | statements statement 
;

statement: ID ASSIGN ensemble ENDLINE
| ID NUMBER ASSIGN ensemble ENDLINE
| ID LBRACKET ensemble RBRACKET ASSIGN ensemble ENDLINE
;

ensemble:  expr
| expr COLON NUMBER                  // 566 only
| ensemble COMMA expr
| ensemble COMMA expr COLON NUMBER   // 566 only
;

expr:   ID{
  $$ = params_list[$1];
}
| ID NUMBER{
  $3 = 1;
  $$ = Builder.CreateAnd(Builder.CreateLShr($1,$2),$3);
}
| NUMBER{
  $$ = Builder.getInt32($1);
}
| expr PLUS expr{
  $$ = Builder.CreateAdd($1,$3);
}
| expr MINUS expr{
  $$ = Builder.CreateSub($1,$3);
}
| expr XOR expr{
  $$ = Builder.CreateXor($1,$3);
}
| expr AND expr{
  $$ = Builder.CreateAnd($1,$3);
}
| expr OR expr{
  $$ = Builder.CreateOr($1,$3);
}
| INV expr{
  $$ = Builder.CreateNot($2);
}
| BINV expr{
  //Value* one;
  //*one = 1;
  $$ = Builder.CreateNot(Builder.CreateAnd($2,1));
}
| expr MUL expr{  
  $$ = Builder.CreateMul($1,$3);
}
| expr DIV expr{
  $$ = Builder.CreateUDiv($1,$3);
}
| expr MOD expr{
  $$ = Builder.CreateSRem($1,$3);
}
| ID LBRACKET ensemble RBRACKET{
  //Value* one;
  //*one = 1;
  $$ = Builder.CreateAnd(Builder.CreateLShr($3,$1),%{1%});
}
| LPAREN ensemble RPAREN{
  $$ = $2;
}
/* 566 only */
| LPAREN ensemble RPAREN LBRACKET ensemble RBRACKET{
  //Value* one;
  //*one = 1;
  $$ = Builder.CreateAnd(Builder.CreateLShr($2,$5),%{1%});
}
| REDUCE AND LPAREN ensemble RPAREN{
  Value * val;
  *val = 1;
  Value* mask = $4;
  //Value* one;
  //*one = 1;
  for(int i = 0;i<32;++i){
    val = Builder.CreateAnd(val,Builder.CreateAnd(mask,%{1%}));
    mask = Builder.CreateLShr(mask,%{1%});
  }
  $$ = val;
}
| REDUCE OR LPAREN ensemble RPAREN{
  Value * val;
  *val = 0;
  Value* mask = $4;
  //Value* one;
  //*one = 1;
  for(int i = 0;i<32;++i){
    val = Builder.CreateOr(val,Builder.CreateAnd(mask,%{1%}));
    mask = Builder.CreateLShr(mask,one);
  }
  $$ = val;
}
| REDUCE XOR LPAREN ensemble RPAREN{
  Value * val;
  *val = 0;
  Value* mask = $4;
  //Value* one;
  //*one = 1;
  for(int i = 0;i<32;++i){
    val = Builder.CreateXor(val,Builder.CreateAnd(mask,%{1%}));
    mask = Builder.CreateLShr(mask,one);
  }
  $$ = val;
}
| REDUCE PLUS LPAREN ensemble RPAREN{
  Value * val;
  *val = 0;
  Value* mask = $4;
  //Value* one;
  //*one = 1;
  for(int i = 0;i<32;++i){
    val = Builder.CreateAdd(val,Builder.CreateAnd(mask,%{1%}));
    mask = Builder.CreateLShr(mask,one);
  }
  $$ = val;
}
| EXPAND  LPAREN ensemble RPAREN{
  Value * tmp = Builder.CreateAnd($3,%{1%});
  Value * val;
  *val = 0;
  //Value* one;
  //*one = 1;
  for(int i = 0;i<32;++i){
    val = Builder.CreateOr(Builder.CreateShl(val,%{1%}),tmp);
  }
  $$ = val;
}
;

%%

unique_ptr<Module> parseP1File(const string &InputFilename)
{
  funName = InputFilename;
  if (funName.find_last_of('/') != string::npos)
    funName = funName.substr(funName.find_last_of('/')+1);
  if (funName.find_last_of('.') != string::npos)
    funName.resize(funName.find_last_of('.'));
    
  //errs() << "Function will be called " << funName << ".\n";
  
  // unique_ptr will clean up after us, call destructor, etc.
  unique_ptr<Module> Mptr(new Module(funName.c_str(), TheContext));

  // set global module
  M = Mptr.get();
  
  /* this is the name of the file to generate, you can also use
     this string to figure out the name of the generated function */
  yyin = fopen(InputFilename.c_str(),"r");

  //yydebug = 1;
  if (yyparse() != 0)
    // errors, so discard module
    Mptr.reset();
  else
    // Dump LLVM IR to the screen for debugging
    M->print(errs(),nullptr,false,true);
  
  return Mptr;
}

void yyerror(const char* msg)
{
  printf("%s\n",msg);
}
