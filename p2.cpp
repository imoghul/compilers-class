#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
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
// #include "dominance.h"
// #include "transform.h"

using namespace llvm;

bool isDead(Instruction &I)
{

    int opcode = I.getOpcode();
    switch (opcode)
    {
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
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
    case Instruction::Alloca:
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
    case Instruction::ICmp:
    case Instruction::FCmp:
    case Instruction::PHI:
    case Instruction::Select:
    case Instruction::ExtractElement:
    case Instruction::InsertElement:
    case Instruction::ShuffleVector:
    case Instruction::ExtractValue:
    case Instruction::InsertValue:
        if (I.use_begin() == I.use_end())
        {
            return true;
        }
        break;

    case Instruction::Load:
    {
        LoadInst *li = dyn_cast<LoadInst>(&I);
        if (li && li->isVolatile())
            return false;
        if (I.use_begin() == I.use_end())
            return true;
        break;
    }

    default:
        // any other opcode fails
        return false;
    }

    if (I.use_begin() == I.use_end())
    {
        return true; // dead, but this is not enough
    }

    return 0;
}

static void CommonSubexpressionElimination(Module *);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
    InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
    OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
    Mem2Reg("mem2reg",
            cl::desc("Perform memory to register promotion before CSE."),
            cl::init(false));

static cl::opt<bool>
    NoCSE("no-cse",
          cl::desc("Do not perform CSE Optimization."),
          cl::init(false));

static cl::opt<bool>
    Verbose("verbose",
            cl::desc("Verbose stats."),
            cl::init(false));

static cl::opt<bool>
    NoCheck("no",
            cl::desc("Do not check for valid IR."),
            cl::init(false));

int main(int argc, char **argv)
{
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.
    LLVMContext Context;

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

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (!NoCSE)
    {
        CommonSubexpressionElimination(M.get());
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

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M)
{
    for (auto i = M->begin(); i != M->end(); i++)
    {
        if (i->begin() != i->end())
        {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++)
        {
            for (auto k = j->begin(); k != j->end(); k++)
            {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I))
                {
                    nLoads++;
                }
                else if (isa<StoreInst>(&I))
                {
                    nStores++;
                }
            }
        }
    }
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

static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};

static bool isCSE(Instruction &i1, Instruction &i2)
{
    if (i1.getOpcode() != i2.getOpcode())
        return false;
    if (i1.getOpcode() == Instruction::Load || i1.getOpcode() == Instruction::Store)
        return false;

    return false;
}

static int cseSupports(Instruction *I)
{
    // return !(LLVMIsALoadInst(I) ||
    //          LLVMIsAStoreInst(I) ||
    //          LLVMIsAPHINode(I) ||
    //          LLVMIsACallInst(I) ||
    //          LLVMIsAAllocaInst(I) ||
    //          LLVMIsAFCmpInst(I) ||
    //          LLVMIsATerminatorInst(I) ||
    //          LLVMIsAVAArgInst(I) ||
    //          LLVMIsAExtractValueInst(I));

    int opcode = I->getOpcode();
    switch (opcode)
    {

    case Instruction::Load:
    case Instruction::Store:
        // TODO: add rest
        return false;
    }
    return true;
}

static void doCSE(BasicBlock *BB, Value *I)
{
    if (!cseSupports((Instruction *)I))
        return;

    for (auto i = BB->begin(); i != BB->end(); ++i)
        ; // points to each instruction
    {
        if (isCSE(*I, **i))
        {
            auto &inst = *i;
            i++;
            if (isCSE(*i, inst))
            {
                // replace uses and stuff
                inst.replaceAllUsesWith(I);
                inst.eraseFromParent();
            }
        }
    }

    auto DT = new DominatorTreeBase<BasicBlock, false>(); // make a new one
    DT->recalculate(*F);                                  // calculate for a new function F

    DomTreeNodeBase<BasicBlock> *Node = DT->getNode(&*BB); // get node for BB

    for (DomTreeNodeBase<BasicBlock> **child = Node->begin(); child != Node->end(); child++)
    {
        processInst((*child)->getBlock(), I);
    }
}

static void CommonSubexpressionElimination(Module *M)
{
    // Implement this function

    // Optimization 0&1
    int numInstr = 0;
    int CSESimplify = 0;
    for (auto f = M->begin(); f != M->end(); f++)
    {
        for (auto bb = f->begin(); bb != f->end(); bb++)
        {
            for (auto i = bb->begin(); i != bb->end();)
            {
                numInstr++;
                auto &inst = *i;
                i++;

                if (isDead(inst))
                {
                    inst.eraseFromParent();
                    continue;
                }

                Value *val = simplifyInstruction(&inst, M->getDataLayout());
                if (val)
                {
                    inst.replaceAllUsesWith(val);
                    CSESimplify++;
                }
            }
        }
    }

    // CSE

    for (auto F = M->begin(); F != M->end(); F++)
    {
        for (auto BB = F->begin(); BB != F->end(); BB++)
        {

            for (auto i = BB->begin(); i != BB->end(); i++)
            {
                for (auto j = i; j != BB->end();)
                {
                    if (&(*i) == &(*j))
                        continue;

                    auto &inst = *j;
                    j++;
                    if (isCSE(*i, inst))
                    {
                        // replace uses and stuff
                        inst.replaceAllUsesWith((Value *)(&(*i)));
                        inst.eraseFromParent();
                    }
                    break;
                }

                // iterate over each child of BB
                BasicBlock *bb = (*child)->getBlock();
                auto DT = new DominatorTreeBase<BasicBlock, false>(); // make a new one
                DT->recalculate(*F);                                  // calculate for a new function F

                DomTreeNodeBase<BasicBlock> *Node = DT->getNode(&*BB); // get node for BB
                for (DomTreeNodeBase<BasicBlock> **child = Node->begin(); child != Node->end(); child++)
                {
                    doCSE((*child)->getBlock(), *i);
                }

                break;
            }
            break;
        }
        delete DT;
    }
    printf("NUM INSTR:%d\n", numInstr);
}

