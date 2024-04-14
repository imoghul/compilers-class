#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <unistd.h>
#include <set>
#include <vector>
#include <utility>
#include <unordered_map>
#include "llvm-c/Core.h"
#include <stdint.h>
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/CFG.h"


#define BB_TO_ID(BB)    ((unsigned int)(((uintptr_t)BB)))


using std::unordered_map;
using namespace llvm;
unordered_map<BasicBlock*,std::vector<BasicBlock*>> BBsuccessors = unordered_map<BasicBlock*,std::vector<BasicBlock*>>();
unordered_map<BasicBlock*,std::vector<BasicBlock*>> BBsuccessors_real = unordered_map<BasicBlock*,std::vector<BasicBlock*>>();

unordered_map<BasicBlock*,PHINode*> BBDiffPhis = unordered_map<BasicBlock*,PHINode*>();
unordered_map<BasicBlock*,PHINode*> BBDestPhis = unordered_map<BasicBlock*,PHINode*>();

unordered_map<BasicBlock*,Value*> destMap = unordered_map<BasicBlock*,Value*>();
unordered_map<BasicBlock*,Value*> diffMap = unordered_map<BasicBlock*,Value*>();

static LLVMContext Context;

LLVMContext &getGlobalContext()
{
  return Context;
}
static BasicBlock::iterator findNextBranch(BasicBlock::iterator bb, BasicBlock::iterator end);
static void InsertXorInEntry(BasicBlock* BB);
static void InsertControlFlowVerification(Module* M, BasicBlock* BB);
static void InsertConclusionInEnd(BasicBlock* BB);
static void SoftwareFaultTolerance(Module *);

static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
    InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
    OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
    NoSWFT("no-swft",
           cl::desc("Do not perform SWFT."),
           cl::init(false));

static cl::opt<bool>
    Verbose("verbose",
            cl::desc("Verbose stats."),
            cl::init(false));

static cl::opt<bool>
    NoCheck("no",
            cl::desc("Do not check for valid IR."),
            cl::init(false));

// Use this to enable your bonus code
static cl::opt<bool>
    Bonus("bonus",
          cl::desc("Run the bonus code."),
          cl::init(false));

// Use these to control whether or not parts of your pass run
static cl::opt<bool>
    NoReplicate("no-replicate",
                cl::desc("Do not perform code replication."),
                cl::init(false));

static cl::opt<bool>
    NoControlProtection("no-control-protection",
                        cl::desc("Do not perform control flow protection."),
                        cl::init(false));

void RunO2(Module *M);
void BuildHelperFunctions(Module *);
void summarize(Module *M);
FunctionCallee AssertFT;
FunctionCallee AssertCFG;

int main(int argc, char **argv)
{
  // Parse command line arguments
  cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

  // Handle creating output files and shutting down properly
  llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

  // LLVM idiom for constructing output file.
  std::unique_ptr<ToolOutputFile> Out;
  std::string ErrorInfo;
  std::error_code EC;
  Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                               sys::fs::OF_None));

  EnableStatistics();

  // Read in module
  SMDiagnostic Err;
  std::unique_ptr<Module> M;
  M = parseIRFile(InputFilename, Err, Context);

  // If errors, fail
  if (M.get() == 0)
  {
    Err.print(argv[0], errs());
    return 1;
  }

  // Run O2 optimizations
  RunO2(M.get());

  if (!NoSWFT)
  {
    BuildHelperFunctions(M.get());
    SoftwareFaultTolerance(M.get());
  }

  // Collect statistics on Module
  summarize(M.get());
  print_csv_file(OutputFilename);

  if (Verbose)
    PrintStatistics(errs());

  // Verify integrity of Module, do this by default
  if (!NoCheck)
  {
    legacy::PassManager Passes;
    Passes.add(createVerifierPass());
    Passes.run(*M.get());
  }

  // Write final bitcode
  WriteBitcodeToFile(*M.get(), Out->os());
  Out->keep();

  return 0;
}

static void print_csv_file(std::string outputfile)
{
  std::ofstream stats(outputfile + ".stats");
  auto a = GetStatistics();
  for (auto p : a)
  {
    stats << p.first.str() << "," << p.second << std::endl;
  }
  stats.close();
}

// Collect this statistic; increment for each instruction you add.
static llvm::Statistic SWFTAdded = {"", "SWFTadd", "SWFT added instructions"};

static bool toReplicate(const Instruction &i)
{

  if(dyn_cast<BranchInst>(&i))return false;

  switch (i.getOpcode())
  {
    case Instruction::Alloca:
    case Instruction::Call:
    case Instruction::Store:
    case Instruction::ICmp:
    case Instruction::FCmp:
    case Instruction::Ret:
      // branch
      return false;
    case Instruction::Add:
    case Instruction::FNeg:
    case Instruction::FAdd:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::FDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::FRem:
    case Instruction::Shl:
    case Instruction::Load:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
    case Instruction::GetElementPtr:
    case Instruction::Trunc:
    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::FPToUI:
    case Instruction::FPToSI:
    case Instruction::UIToFP:
    case Instruction::SIToFP:
    case Instruction::FPTrunc:
    case Instruction::FPExt:
    case Instruction::PtrToInt:
    case Instruction::IntToPtr:
    case Instruction::BitCast:
    case Instruction::AddrSpaceCast:
    case Instruction::ExtractElement:
    case Instruction::InsertElement:
    case Instruction::ShuffleVector:
    case Instruction::ExtractValue:
    case Instruction::InsertValue:
      return true;
  }
  return false;
}

static void replicateCode(Function *F)
{
  for (auto BB = F->begin(); BB != F->end(); BB++)
  {
    unordered_map<Instruction*,Instruction*> cloneMap = unordered_map<Instruction*,Instruction*>();
    
    for (auto inst = BB->begin(); inst != BB->end(); inst++)
    {

      if (toReplicate(*inst))
      {
        auto c = inst->clone();
        c->insertBefore(&(*inst));
        SWFTAdded++;
        cloneMap[&(*inst)] = c;
      }
    }
    for (auto c = cloneMap.begin(); c != cloneMap.end(); c++)
    {
      for (int i = 0; i < c->first->getNumOperands(); ++i)
      {
        if (cloneMap.find((Instruction* const)(c->first->getOperand(i))) != cloneMap.end())
        {
          c->first->setOperand(i, cloneMap.find((Instruction* const)(c->first->getOperand(i)))->second );
        }
      }
    }
  }
}

static BasicBlock::iterator findNextBranch(BasicBlock::iterator bb, BasicBlock::iterator end){
  for(auto it = bb;it!=end;++it){
    if(dyn_cast<BranchInst>(&(*it))){return it;}
    if(dyn_cast<SwitchInst>(&(*it))){return it;}
  }
  return end;
}


static void InsertXorInEntry(BasicBlock* BB){
  if(!BB) return;
  IRBuilder<> Builder(BB);
  BranchInst* branch = nullptr;
  SwitchInst* switchInst = nullptr;
  auto inst = findNextBranch(BB->begin(),BB->end());
  auto branch_inst=  inst;
  for(;inst!=BB->end();inst = findNextBranch(++inst,BB->end())){
    branch = dyn_cast<BranchInst>(&(*inst));
    switchInst = dyn_cast<SwitchInst>(&(*inst));
    
    branch_inst = inst;
  }
  inst = branch_inst;
  
  if(!branch && !switchInst) return;


  Builder.SetInsertPoint(&(*(inst)));

  BasicBlock* bb1 = BB;
  BasicBlock* bb2 = branch ? branch->getSuccessor(0) : switchInst->getSuccessor(0);
  Value* bb4 = Builder.getInt32(BB_TO_ID(bb2));

  if(switchInst) {
    // switchInst->print(errs());
    printf("\nswitch has %d\n",switchInst->getNumSuccessors());
  }

  if(branch && branch->isConditional()){
    // make select between bb2 and bb3
    assert(branch->getNumSuccessors()>1);
    BasicBlock* bb3 = branch->getSuccessor(1);
    bb4 = Builder.CreateSelect(branch->getCondition(),Builder.getInt32(BB_TO_ID(bb2)),Builder.getInt32(BB_TO_ID(bb3)));
    SWFTAdded++;
  }
  // make xor between bb1 and bb4
  Value* xorInst = Builder.CreateXor(Builder.getInt32(BB_TO_ID(bb1)),bb4);
  SWFTAdded++;
  assert(xorInst);
  // add to diff map
  diffMap[BB] = xorInst;
  return;
}
static void InsertControlFlowVerification(Module* M, BasicBlock* BB){
  if(!BB) return;
  
  
  auto inst = BB->begin();
  for(;inst!=BB->end();++inst){
    if(!dyn_cast<PHINode>(&(*inst)))break;
  }


  IRBuilder<> Builder(BB);
  // BranchInst* branch = nullptr;
  Builder.SetInsertPoint(&(*(inst)));

  Value* v = Builder.getInt32(0);
  auto * type = v->getType();
  // delete v;

  // insert phi to get previous diff (ie use the diffMap to fill in phi)
  std::string phi_name = (BB->hasName() ? BB->getName().str() : std::to_string(BB_TO_ID(BB)))+"_diff_phi";
  PHINode* diff_phi = Builder.CreatePHI(type,BBsuccessors[BB].size(),phi_name);
  SWFTAdded++;
  BBDiffPhis[BB] = diff_phi;
  // diff_phi->addIncoming();

  // insert phi to get previous dest (ie use the destMap to fill in phi)
  phi_name = (BB->hasName() ? BB->getName().str() : std::to_string(BB_TO_ID(BB)))+"_dest_phi";
  PHINode* dest_phi = Builder.CreatePHI(type,BBsuccessors[BB].size(),phi_name);
  SWFTAdded++;
  BBDestPhis[BB] = dest_phi;

  // insert xor and store in this bb's dest 
  Value* comp_dest = Builder.CreateXor(diff_phi,dest_phi);
  SWFTAdded++;
  destMap[BB] = comp_dest;
  // do the compare
  Value* cmp = Builder.CreateICmpEQ(comp_dest,Builder.getInt32(BB_TO_ID(BB)));
  SWFTAdded++;
  // do the zext
  Value* zext = Builder.CreateZExt(cmp,type);
  SWFTAdded++;
  // call assert
  std::vector<Value*> args;
  args.push_back(zext); // boolean
  args.push_back(Builder.getInt32(BB_TO_ID(BB))); // unique id
  Function *F = M->getFunction("assert_ft");
  Builder.CreateCall(F->getFunctionType(),F, args);
  SWFTAdded++;

  // add xor before final br
  // InsertXorInEntry(BB);

  // inst = findNextBranch(inst,BB->end());
  // for(;inst!=BB->end();inst = findNextBranch(++inst,BB->end())){
  //   branch = dyn_cast<BranchInst>(&(*inst));

  // }
  // if(!branch) return;
  // delete type;
}
static void InsertConclusionInEnd(BasicBlock* BB){
  // for(auto inst = findNextBranch(BB->begin(),BB->end()) ;inst!=BB->end();inst = findNextBranch(++inst,BB->end())){
  //   auto* branch = dyn_cast<BranchInst>(&(*inst));
  // }
  // return;
}

static void SoftwareFaultTolerance(Module *M)
{
  Module::FunctionListType &list = M->getFunctionList();

  std::vector<Function *> flist;
  // FIND THE ASSERT FUNCTIONS AND DO NOT INSTRUMENT THEM
  for (Module::FunctionListType::iterator it = list.begin(); it != list.end(); it++)
  {
    Function *fptr = &*it;
    if (fptr->size() > 0 && fptr != AssertFT.getCallee() && fptr != AssertCFG.getCallee())
      flist.push_back(fptr);
  }
 
  // PROTECT CODE IN EACH FUNCTION
  for (std::vector<Function *>::iterator it = flist.begin(); it != flist.end(); it++)
  {
    // CALL A FUNCTION TO REPLICATE CODE in *it
    // replicateCode(*it);
  }

  // fill in all successors
  for (std::vector<Function *>::iterator it = flist.begin(); it != flist.end(); it++){
    for (auto BB = (*it)->begin(); BB != (*it)->end(); BB++){
      for(auto inst = findNextBranch(BB->begin(),BB->end()) ;inst!=BB->end();inst = findNextBranch(++inst,BB->end())){
        auto* branch = dyn_cast<BranchInst>(&(*inst));
        auto* switchInst = dyn_cast<SwitchInst>(&(*inst));
        assert(branch || switchInst);
        if(branch){
          for(uint i = 0;i<branch->getNumSuccessors();++i){
            BBsuccessors[(branch->getSuccessor(i))].push_back((&(*BB)));  
          }
        }else if (switchInst){
          for(uint i = 0;i<switchInst->getNumSuccessors();++i){
            BBsuccessors[(switchInst->getSuccessor(i))].push_back((&(*BB)));  
          }
        }
      }
      for(BasicBlock* pred:predecessors(&(*BB))){
        BBsuccessors_real[pred].push_back(&(*BB));
      }
    }
  }

  // perform control flow validation
  for (std::vector<Function *>::iterator it = flist.begin(); it != flist.end(); it++)
  {

    for (auto BB = (*it)->begin(); BB != (*it)->end(); BB++)
    {
        auto next = BB;
        next++;
        
        if(BB == (*it)->begin()){
          InsertXorInEntry(&(*BB));
          IRBuilder<> Builder(&(*BB));
          destMap[&(*BB)] = Builder.getInt32(BB_TO_ID(&(*BB)));
        }
        else if (next == (*it)->end()){
          // InsertXorInEntry(&(*BB));
          InsertControlFlowVerification(M,&(*BB));//InsertConclusionInEnd(&(*BB));
          InsertXorInEntry(&(*BB));
        }
        else {
          // InsertXorInEntry(&(*BB));
          InsertControlFlowVerification(M,&(*BB));
          InsertXorInEntry(&(*BB));
        }
    }
    // break;
  }

  // Clean up Phis
  for (std::vector<Function *>::iterator it = flist.begin(); it != flist.end(); it++)
  {

    for (auto BB = (*it)->begin(); BB != (*it)->end(); BB++)
    {
      // iterate over all of BB's successors
      // insert into phi for them, with their destMap/diffMap counterpart
      for(auto i = BBsuccessors[&(*BB)].begin();i!=BBsuccessors[&(*BB)].end();++i){
        if(!destMap[*i])continue;
        if(BBDiffPhis[&(*BB)]) BBDiffPhis[&(*BB)]->addIncoming(diffMap[*i],*i);
        if(BBDestPhis[&(*BB)]) BBDestPhis[&(*BB)]->addIncoming(destMap[*i],*i);
      }
    }
  }
}