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
    static void processInst(LLVMBasicBlockRef BB, LLVMValueRef I, int flag);
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

static bool isCSE(Instruction &i1, Instruction &i2)
{
    if (&i1 == &i2)
        return false;

    LLVMValueRef I1 = wrap(&i1);
    LLVMValueRef I2 = wrap(&i2);

    bool ret = false;
    if ((LLVMIsAICmpInst(I1) && (LLVMGetICmpPredicate(I1) != LLVMGetICmpPredicate(I2))) || (LLVMIsAFCmpInst(I1) && LLVMGetFCmpPredicate(I1) != LLVMGetFCmpPredicate(I2)))
    {
        ret = false;
    }
    if (LLVMGetInstructionOpcode(I1) == LLVMGetInstructionOpcode(I2) && LLVMTypeOf(I1) == LLVMTypeOf(I2) && LLVMGetNumOperands(I1) == LLVMGetNumOperands(I2))
    {
        
        for (int i = 0; i < LLVMGetNumOperands(I1); i++)
        {
            LLVMValueRef a = LLVMGetOperand(I1, i);
            LLVMValueRef b = LLVMGetOperand(I2, i);
            ret = a == b;
            if(!ret) return false;
        }
            
    }
    return ret;
}

static int cseSupports(Instruction *i)
{
    LLVMValueRef I = wrap(i);
    return !(LLVMIsALoadInst(I) ||
             LLVMIsAStoreInst(I) ||
             LLVMIsAPHINode(I) ||
             LLVMIsACallInst(I) ||
             LLVMIsAAllocaInst(I) ||
             LLVMIsAFCmpInst(I) ||
             LLVMIsATerminatorInst(I) ||
             LLVMIsAVAArgInst(I) ||
             LLVMIsAExtractValueInst(I));
}

static void doCSE(Function *F, BasicBlock *BB, Instruction *I)
{
    if (!cseSupports((Instruction *)I))
        return;

    for (auto i = BB->begin(); i != BB->end();)
    {
        Instruction &inst = *i;
        i++;
        if (isCSE(*((Instruction *)I), (*i)))
        {
            inst.replaceAllUsesWith(I);
            inst.eraseFromParent();
            CSEElim++;
        }
    }

    auto DT = new DominatorTreeBase<BasicBlock, false>(); 
    DT->recalculate(*F);                                  

    DomTreeNodeBase<BasicBlock> *Node = DT->getNode(&*BB);

    for (DomTreeNodeBase<BasicBlock> **child = Node->begin(); child != Node->end(); child++)
    {
        doCSE(F, (*child)->getBlock(), I);
    }
}

static int canHandle(LLVMValueRef I)
{
    return !(LLVMIsALoadInst(I) ||
             LLVMIsAStoreInst(I) ||
             LLVMIsATerminatorInst(I) ||
             LLVMIsACallInst(I) ||
             LLVMIsAPHINode(I) ||
             LLVMIsAAllocaInst(I) ||
             LLVMIsAFCmpInst(I) ||
             LLVMIsAVAArgInst(I) ||
             LLVMIsAExtractValueInst(I));
}

static int commonSubexpression(LLVMValueRef I, LLVMValueRef J)
{

    int flag = 0;

    if (LLVMIsAICmpInst(I))
    {
        if (LLVMGetICmpPredicate(I) != LLVMGetICmpPredicate(J))
        {
            flag = 0;
        }
    }

    if (LLVMIsAFCmpInst(I))
    {
        if (LLVMGetFCmpPredicate(I) != LLVMGetFCmpPredicate(J))
        {
            flag = 0;
        }
    }
    if (LLVMGetInstructionOpcode(I) == LLVMGetInstructionOpcode(J))
    {
        if (LLVMTypeOf(I) == LLVMTypeOf(J)) 
        {
            if (LLVMGetNumOperands(I) == LLVMGetNumOperands(J))
            {
                int oper_iter;
                for (oper_iter = 0; oper_iter < LLVMGetNumOperands(I); oper_iter++)
                {
                    LLVMValueRef op_I = LLVMGetOperand(I, oper_iter);
                    LLVMValueRef op_J = LLVMGetOperand(J, oper_iter);
                    if (op_I == op_J) 
                        flag = 1;
                    else
                    {
                        flag = 0;
                        break;
                    }
                }
            }
        }
    }
    return flag;
}

static void processInst(LLVMBasicBlockRef BB, LLVMValueRef I, int flag)
{

    if (!canHandle(I))
    {
        return;
    }
    else 
    {
        if (flag == 0)
        {
            LLVMValueRef inst_iter = LLVMGetNextInstruction(I); 
            while (inst_iter != NULL)
            {
                if (commonSubexpression(I, inst_iter))
                {
                    LLVMValueRef rm = inst_iter;
                    inst_iter = LLVMGetNextInstruction(inst_iter);
                    LLVMReplaceAllUsesWith(rm, I);
                    LLVMInstructionEraseFromParent(rm);
                    CSEElim++;
                    continue;
                }
                inst_iter = LLVMGetNextInstruction(inst_iter);
            }

            LLVMBasicBlockRef child_BB;
            for (child_BB = LLVMFirstDomChild(BB); child_BB != NULL; child_BB = LLVMNextDomChild(BB, child_BB))
            {
                processInst(child_BB, I, 1);
            }
        }

        else if (flag == 1)

        {
            LLVMValueRef insn_child = LLVMGetFirstInstruction(BB);
            while (insn_child != NULL)
            {
                if (commonSubexpression(I, insn_child))
                {
                    LLVMValueRef rm = insn_child;
                    insn_child = LLVMGetNextInstruction(insn_child);
                    LLVMReplaceAllUsesWith(rm, I);
                    LLVMInstructionEraseFromParent(rm);
                    CSEElim++;
                    continue;
                }
                insn_child = LLVMGetNextInstruction(insn_child);
            }

            LLVMBasicBlockRef child_BB;
            for (child_BB = LLVMFirstDomChild(BB); child_BB != NULL; child_BB = LLVMNextDomChild(BB, child_BB))
            {
                processInst(child_BB, I, 1);
            }
        }
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
                LLVMValueRef inst_iter = LLVMGetNextInstruction(wrap(&(*i))); 
                while (inst_iter != NULL)
                {
                    if (commonSubexpression(wrap(&(*i)), inst_iter))
                    {
                        LLVMValueRef rm = inst_iter;
                        inst_iter = LLVMGetNextInstruction(inst_iter);
                        LLVMReplaceAllUsesWith(rm, I);
                        LLVMInstructionEraseFromParent(rm);
                        CSEElim++;
                        continue;
                    }
                    inst_iter = LLVMGetNextInstruction(inst_iter);
                }

                LLVMBasicBlockRef child_BB;
                for (child_BB = LLVMFirstDomChild(wrap(&(*BB))); child_BB != NULL; child_BB = LLVMNextDomChild(wrap(&(*BB)), child_BB))
                {
                    processInst(child_BB, wrap(&(*i)), 1);
                }
                // processInst(BB, inst_iter, 0);
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
            LLVMValueRef inst_iter;
            inst_iter = LLVMGetFirstInstruction(BB);
            while (inst_iter != NULL)
            {
                if (LLVMGetInstructionOpcode(inst_iter) == LLVMStore)
                {
                    LLVMValueRef inst_iter2;
                    inst_iter2 = LLVMGetNextInstruction(inst_iter);
                    while (inst_iter2 != NULL)
                    {
                        if ((LLVMGetInstructionOpcode(inst_iter2) == LLVMLoad) &&
                            (!(LLVMGetVolatile(inst_iter2))) &&
                            (LLVMTypeOf(inst_iter2) == LLVMTypeOf(LLVMGetOperand(inst_iter, 0))) &&
                            (LLVMGetOperand(inst_iter, 1) == LLVMGetOperand(inst_iter2, 0))) 
                        {
                            LLVMValueRef rm = inst_iter2;
                            inst_iter2 = LLVMGetNextInstruction(inst_iter2);
                            LLVMReplaceAllUsesWith(rm, LLVMGetOperand(inst_iter, 0));
                            LLVMInstructionEraseFromParent(rm);
                            CSEStore2Load++;
                            continue; 
                        }

                        else if ((LLVMGetInstructionOpcode(inst_iter2) == LLVMStore) &&
                                 (!(LLVMGetVolatile(inst_iter))) &&
                                 (LLVMTypeOf(LLVMGetOperand(inst_iter2, 0)) == LLVMTypeOf(LLVMGetOperand(inst_iter, 0))) &&
                                 (LLVMGetOperand(inst_iter, 1) == LLVMGetOperand(inst_iter2, 1)))
                        {
                            LLVMValueRef rm = inst_iter;
                            inst_iter = LLVMGetNextInstruction(inst_iter);
                            LLVMInstructionEraseFromParent(rm);
                            CSEStElim++;
                            
                            move_to_next_store = 1;
                            break;
                        }
                        else if (LLVMGetInstructionOpcode(inst_iter2) == LLVMStore ||
                                 LLVMGetInstructionOpcode(inst_iter2) == LLVMCall ||
                                 LLVMGetInstructionOpcode(inst_iter2) == LLVMLoad)
                        {
                            break;
                        }

                        inst_iter2 = LLVMGetNextInstruction(inst_iter2);
                    }

                    if (move_to_next_store == 1)
                    {
                        move_to_next_store = 0;
                        continue;
                    }
                }

                inst_iter = LLVMGetNextInstruction(inst_iter);
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
