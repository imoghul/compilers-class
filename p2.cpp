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
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/BasicBlock.h"
#include <set>
#include "llvm/IR/InstIterator.h"
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
#include "llvm/IR/Module.h"
#include "llvm/PassRegistry.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/DataTypes.h"
#include "llvm-c/Core.h"
// #include "dominance.h"
// #include "transform.h"
#include "llvm-c/Core.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/GlobalVariable.h"
// #include "llvm/PassManager.h"
#include "llvm/IR/Dominators.h"
// #include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Type.h"

using namespace llvm;

extern "C"
{
    LLVMBool LLVMDominates(LLVMValueRef Fun, LLVMBasicBlockRef a, LLVMBasicBlockRef b);
    LLVMBool LLVMPostDominates(LLVMValueRef Fun, LLVMBasicBlockRef a, LLVMBasicBlockRef b);

    LLVMBasicBlockRef LLVMImmDom(LLVMBasicBlockRef BB);
    LLVMBasicBlockRef LLVMImmPostDom(LLVMBasicBlockRef BB);

    LLVMBasicBlockRef LLVMNearestCommonDominator(LLVMBasicBlockRef A, LLVMBasicBlockRef B);
    unsigned LLVMGetLoopNestingDepth(LLVMBasicBlockRef BB);

    LLVMBasicBlockRef LLVMFirstDomChild(LLVMBasicBlockRef BB);
    LLVMBasicBlockRef LLVMNextDomChild(LLVMBasicBlockRef BB, LLVMBasicBlockRef Child);
    LLVMBool LLVMIsReachableFromEntry(LLVMValueRef Fun, LLVMBasicBlockRef bb);
    static bool isCSE(Instruction &i1, Instruction &i2);
    static int cseSupports(Instruction *i);
    static void CommonSubexpressionElimination(Module *M);
    static void redundantStore(Module *M);
    static void cse(Module *M);
    static void processInst(LLVMBasicBlockRef BB, LLVMValueRef I);
}
Function *Current = NULL;
DominatorTreeBase<BasicBlock, false> *DT = NULL;
DominatorTreeBase<BasicBlock, true> *PDT = NULL;

LoopInfoBase<BasicBlock, Loop> *LI = NULL;

void UpdateDominators(Function *F)
{
    if (Current != F)
    {
        Current = F;

        if (DT == NULL)
        {
            DT = new DominatorTreeBase<BasicBlock, false>();
            PDT = new DominatorTreeBase<BasicBlock, true>();
            if (LI == NULL)
                LI = new LoopInfoBase<BasicBlock, Loop>();
        }

        DT->recalculate(*F);
        PDT->recalculate(*F);

        LI->analyze(*DT);
    }
}

// Test if a dom b
LLVMBool LLVMDominates(LLVMValueRef Fun, LLVMBasicBlockRef a, LLVMBasicBlockRef b)
{
    UpdateDominators((Function *)unwrap(Fun));
    return DT->dominates(unwrap(a), unwrap(b));
}

// Test if a pdom b
LLVMBool LLVMPostDominates(LLVMValueRef Fun, LLVMBasicBlockRef a, LLVMBasicBlockRef b)
{
    UpdateDominators((Function *)unwrap(Fun));
    return PDT->dominates(unwrap(a), unwrap(b));
}

LLVMBool LLVMIsReachableFromEntry(LLVMValueRef Fun, LLVMBasicBlockRef bb)
{
    UpdateDominators((Function *)unwrap(Fun));
    return DT->isReachableFromEntry(unwrap(bb));
}

LLVMBasicBlockRef LLVMImmDom(LLVMBasicBlockRef BB)
{
    UpdateDominators(unwrap(BB)->getParent());

    if (DT->getNode((BasicBlock *)unwrap(BB)) == NULL)
        return NULL;

    if (DT->getNode((BasicBlock *)unwrap(BB))->getIDom() == NULL)
        return NULL;

    return wrap(DT->getNode(unwrap(BB))->getIDom()->getBlock());
}

LLVMBasicBlockRef LLVMImmPostDom(LLVMBasicBlockRef BB)
{
    UpdateDominators(unwrap(BB)->getParent());

    if (PDT->getNode(unwrap(BB))->getIDom() == NULL)
        return NULL;

    return wrap((BasicBlock *)PDT->getNode(unwrap(BB))->getIDom()->getBlock());
}

LLVMBasicBlockRef LLVMFirstDomChild(LLVMBasicBlockRef BB)
{
    UpdateDominators(unwrap(BB)->getParent());
    DomTreeNodeBase<BasicBlock> *Node = DT->getNode(unwrap(BB));

    if (Node == NULL)
        return NULL;

    DomTreeNodeBase<BasicBlock>::iterator it = Node->begin();
    if (it != Node->end())
        return wrap((*it)->getBlock());
    return NULL;
}

LLVMBasicBlockRef LLVMNextDomChild(LLVMBasicBlockRef BB, LLVMBasicBlockRef Child)
{
    UpdateDominators(unwrap(BB)->getParent());
    DomTreeNodeBase<BasicBlock> *Node = DT->getNode(unwrap(BB));
    DomTreeNodeBase<BasicBlock>::iterator it, end;

    bool next = false;
    for (it = Node->begin(), end = Node->end(); it != end; it++)
        if (next)
            return wrap((*it)->getBlock());
        else if (*it == DT->getNode(unwrap(Child)))
            next = true;

    return NULL;
}

LLVMBasicBlockRef LLVMNearestCommonDominator(LLVMBasicBlockRef A, LLVMBasicBlockRef B)
{
    UpdateDominators(unwrap(A)->getParent());
    return wrap(DT->findNearestCommonDominator(unwrap(A), unwrap(B)));
}

unsigned LLVMGetLoopNestingDepth(LLVMBasicBlockRef BB)
{
    if (LI == NULL)
        UpdateDominators(unwrap(BB)->getParent());

    return LI->getLoopDepth(unwrap(BB));
}

LLVMBasicBlockRef LLVMDominanceFrontierLocal(LLVMBasicBlockRef BB)
{
    return NULL;
}

LLVMBasicBlockRef LLVMDominanceFrontierClosure(LLVMBasicBlockRef BB)
{
    return NULL;
}

LLVMBasicBlockRef LLVMPostDominanceFrontierLocal(LLVMBasicBlockRef BB)
{
    return NULL;
}

LLVMBasicBlockRef LLVMPostDominanceFrontierClosure(LLVMBasicBlockRef BB)
{
    return NULL;
}

bool isDead(Instruction &I)
{

    if (I.use_begin() != I.use_end())
    {
        return false; // dead, but this is not enough
    }

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

    return false;
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


static int canHandle(LLVMValueRef I)
{
    return !(LLVMIsALoadInst(I) ||
             LLVMIsAStoreInst(I) ||
             LLVMIsACallInst(I) ||
             LLVMIsAPHINode(I) ||
             LLVMIsAExtractValueInst(I) ||
             LLVMIsAFCmpInst(I) ||
             LLVMIsAAllocaInst(I) ||
             LLVMIsAVAArgInst(I) ||
             LLVMIsATerminatorInst(I));
}

static bool commonSubexpression(LLVMValueRef I, LLVMValueRef J)
{

    int ret = false;

    if ((LLVMIsAICmpInst(I) && LLVMGetICmpPredicate(I) != LLVMGetICmpPredicate(J)) ||  (LLVMIsAFCmpInst(I) && LLVMGetFCmpPredicate(I) != LLVMGetFCmpPredicate(J)))
    {
            ret = false;
        
    }
    if (LLVMGetInstructionOpcode(I) == LLVMGetInstructionOpcode(J) && LLVMTypeOf(I) == LLVMTypeOf(J) && LLVMGetNumOperands(I) == LLVMGetNumOperands(J))
    {
                int oper_iter;
                for (oper_iter = 0; oper_iter < LLVMGetNumOperands(I); oper_iter++)
                {
                    ret = (LLVMGetOperand(I, oper_iter) == LLVMGetOperand(J, oper_iter));
                        
                    if(!ret)
                    {
                        return false;
                    }
                }
    }
    return ret;
}

static void processInst(LLVMBasicBlockRef BB, LLVMValueRef I)
{

    if (!canHandle(I))
    {
        return;
    }
    LLVMValueRef inst = LLVMGetFirstInstruction(BB);
    while (inst != NULL)
    {
        LLVMValueRef temp = inst;
        inst = LLVMGetNextInstruction(inst);
        if (commonSubexpression(I, temp))
        {   
            LLVMReplaceAllUsesWith(temp, I);
            LLVMInstructionEraseFromParent(temp);
            CSEElim++;
            continue;
        }
    }

    LLVMBasicBlockRef domBB;
    for (domBB = LLVMFirstDomChild(BB); domBB != NULL; domBB = LLVMNextDomChild(BB, domBB))
    {
        processInst(domBB, I);
    } 
}

static void simplify(Module *M)
{
    for (auto f = M->begin(); f != M->end(); f++)
    {
        for (auto bb = f->begin(); bb != f->end(); bb++)
        {
            for (auto i = bb->begin(); i != bb->end();)
            {
                auto &inst = *i;
                i++;

                Value *val = simplifyInstruction(&inst, M->getDataLayout());
                if (val)
                {
                    inst.replaceAllUsesWith(val);
                    inst.eraseFromParent();
                    CSESimplify++;
                }
            }
        }
    }
}

static void removeDead(Module *M)
{
    for (auto f = M->begin(); f != M->end(); f++)
    {
        for (auto bb = f->begin(); bb != f->end(); bb++)
        {
            for (auto i = bb->begin(); i != bb->end();)
            {
                auto &inst = *i;
                i++;

                if (isDead(inst))
                {
                    inst.eraseFromParent();
                    CSEDead++;
                }
            }
        }
    }
}

static void cse(Module *M)
{
    for (auto F = M->begin(); F != M->end(); F++)
    {
        for (auto BB = F->begin(); BB != F->end(); BB++)
        {

            for (auto i = BB->begin(); i != BB->end(); i++)
            {
                if (!canHandle(wrap(&(*i)))) continue;
                
                LLVMValueRef inst = LLVMGetNextInstruction(wrap(&(*i)));
                while (inst != NULL)
                {
                    LLVMValueRef temp = inst;
                    inst = LLVMGetNextInstruction(inst);
                    if (commonSubexpression(wrap(&(*i)), temp))
                    {
                        
                        LLVMReplaceAllUsesWith(temp, wrap(&(*i)));
                        LLVMInstructionEraseFromParent(temp);
                        CSEElim++;
                        continue;
                    }
                }

                LLVMBasicBlockRef domBB;
                for (domBB = LLVMFirstDomChild(wrap(&(*BB))); domBB != NULL; domBB = LLVMNextDomChild(wrap(&(*BB)), domBB))
                {
                    processInst(domBB, wrap(&(*i)));
                }
            }
        }
    }
}

static void redundantLoad(Module *M)
{
    for (auto F = M->begin(); F != M->end(); F++)
    {
        for (auto BB = F->begin(); BB != F->end(); BB++)
        {

            for (auto i = BB->begin(); i != BB->end(); i++)
            {
                if (i->getOpcode() == Instruction::Load)
                {
                    auto j = i;
                    if (j == BB->end())
                        break;
                    j++;
                    if (j == BB->end())
                        break;
                    for (; j != BB->end();)
                    {
                        auto &inst = *j;
                        j++;
                        if (inst.getOpcode() == Instruction::Load && !inst.isVolatile() && i->getAccessType() == inst.getAccessType() && i->getOperand(0) == inst.getOperand(0))
                        {
                            CSELdElim++;
                            inst.replaceAllUsesWith((Value *)(&(*i)));
                            inst.eraseFromParent();
                        }
                        if (inst.getOpcode() == Instruction::Store)
                            break;
                    }
                }
            }
        }
    }
}

static void redundantStore(Module *M)
{
    static int move_to_next_store = 0;
    for (auto F = M->begin(); F != M->end(); F++)
    {
        LLVMValueRef Function = wrap(&(*F));
        LLVMBasicBlockRef BB;
        for (BB = LLVMGetFirstBasicBlock(Function); BB != NULL; BB = LLVMGetNextBasicBlock(BB))
        {
            LLVMValueRef i;
            i = LLVMGetFirstInstruction(BB);
            while (i != NULL)
            {
                if (LLVMGetInstructionOpcode(i) == LLVMStore)
                {
                    LLVMValueRef j;
                    j = LLVMGetNextInstruction(i);
                    while (j != NULL)
                    {

                        LLVMValueRef temp_j = j;
                        j = LLVMGetNextInstruction(j);

                        if ((LLVMGetInstructionOpcode(temp_j) == LLVMLoad) &&
                            (!(LLVMGetVolatile(temp_j))) &&
                            (LLVMGetOperand(i, 1) == LLVMGetOperand(temp_j, 0)) &&
                            (LLVMTypeOf(temp_j) == LLVMTypeOf(LLVMGetOperand(i, 0))))
                        {
                            LLVMReplaceAllUsesWith(temp_j, LLVMGetOperand(i, 0));
                            LLVMInstructionEraseFromParent(temp_j);
                            CSEStore2Load++;
                            continue;
                        }

                        if ((LLVMGetInstructionOpcode(temp_j) == LLVMStore) &&
                                 (!(LLVMGetVolatile(i))) &&
                                 (LLVMGetOperand(i, 1) == LLVMGetOperand(temp_j, 1)) &&
                                 (LLVMTypeOf(LLVMGetOperand(temp_j, 0)) == LLVMTypeOf(LLVMGetOperand(i, 0))))
                        {
                            LLVMValueRef rm = i;
                            i = LLVMGetNextInstruction(i);
                            LLVMInstructionEraseFromParent(rm);
                            CSEStElim++;

                            move_to_next_store = 1;
                            break;
                        }
                        if (LLVMGetInstructionOpcode(temp_j) == LLVMStore ||
                                 LLVMGetInstructionOpcode(temp_j) == LLVMCall ||
                                 LLVMGetInstructionOpcode(temp_j) == LLVMLoad)
                        {
                            break;
                        }

                        // j = LLVMGetNextInstruction(j);
                    }

                    if (move_to_next_store == 1)
                    {
                        move_to_next_store = 0;
                        continue;
                    }
                }

                i = LLVMGetNextInstruction(i);
            }
        }
    }
}

static void CommonSubexpressionElimination(Module *M)
{
    // Implement this function

    simplify(M);
    removeDead(M);
    cse(M);
    redundantLoad(M);
    redundantStore(M);
    cse(M);
    simplify(M);
    removeDead(M);
}
