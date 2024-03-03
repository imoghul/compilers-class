/*
 * File: CSE.c
 *
 * Description:
 *   This is where you implement the C version of project 2 support.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"

/* Header file global to this project */
#include "cfg.h"
#include "cse.h"
#include "dominance.h"
#include "transform.h"
#include "stats.h"

LLVMStatisticsRef CSEDead;
LLVMStatisticsRef CSEElim;
LLVMStatisticsRef CSESimplify;
LLVMStatisticsRef CSELdElim;
LLVMStatisticsRef CSEStore2Load;
LLVMStatisticsRef CSEStElim;

int isDead(LLVMValueRef I)
{
    if (LLVMGetFirstUse(I) == NULL)
        return 1;
    LLVMOpcode opcode = LLVMGetInstructionOpcode(I);
    switch (opcode)
    {
    // when in doubt, keep it! add opcode here to remove:
    case LLVMFNeg:
    case LLVMAdd:
    case LLVMFAdd:
    case LLVMSub:
    case LLVMFSub:
    case LLVMMul:
    case LLVMFMul:
    case LLVMUDiv:
    case LLVMSDiv:
    case LLVMFDiv:
    case LLVMURem:
    case LLVMSRem:
    case LLVMFRem:
    case LLVMShl:
    case LLVMLShr:
    case LLVMAShr:
    case LLVMAnd:
    case LLVMOr:
    case LLVMXor:
    case LLVMAlloca:
    case LLVMGetElementPtr:
    case LLVMTrunc:
    case LLVMZExt:
    case LLVMSExt:
    case LLVMFPToUI:
    case LLVMFPToSI:
    case LLVMUIToFP:
    case LLVMSIToFP:
    case LLVMFPTrunc:
    case LLVMFPExt:
    case LLVMPtrToInt:
    case LLVMIntToPtr:
    case LLVMBitCast:
    case LLVMAddrSpaceCast:
    case LLVMICmp:
    case LLVMFCmp:
    case LLVMPHI:
    case LLVMSelect:
    case LLVMExtractElement:
    case LLVMInsertElement:
    case LLVMShuffleVector:
    case LLVMExtractValue:
    case LLVMInsertValue:
        // Success!
        return 1;

    case LLVMLoad:
        if (!LLVMGetVolatile(I))
            return 1; // Success

    // all others must be kept
    default:
        break;
    }

    return 0;
}

void CommonSubexpressionElimination(LLVMModuleRef Module)
{
    CSEDead = LLVMStatisticsCreate("CSEDead", "CSE found dead instructions");
    CSEElim = LLVMStatisticsCreate("CSEElim", "CSE redundant instructions");
    CSESimplify = LLVMStatisticsCreate("CSESimplify", "CSE simplified instructions");
    CSELdElim = LLVMStatisticsCreate("CSELdElim", "CSE redundant loads");
    CSEStore2Load = LLVMStatisticsCreate("CSEStore2Load", "CSE forwarded store to load");
    CSEStElim = LLVMStatisticsCreate("CSEStElim", "CSE redundant stores");

    /* Implement here! */
    // LLVMPassManagerRef PM = LLVMCreatePassManager();
    // LLVMAddScalarReplAggregatesPass(PM);
    // LLVMRunPassManager(PM, Module);

    LLVMValueRef F=NULL;
    for (F = LLVMGetFirstFunction(Module); F != NULL; F = LLVMGetNextFunction(F))
    {
        LLVMBasicBlockRef BB = NULL;
        for (BB = LLVMGetFirstBasicBlock(F); BB != NULL; BB = LLVMGetNextBasicBlock(BB))
        {
            LLVMValueRef inst_iter = LLVMGetFirstInstruction(BB);
            while (inst_iter != NULL)
            {
                // update iterator first, before erasing
                if (isDead(inst_iter))
                { 
                    LLVMInstructionEraseFromParent(inst_iter);
                    printf("Found a dead instruction to delete !\n");
                }
                else
                    inst_iter = LLVMGetNextInstruction(inst_iter);
            }
        }
    }

    LLVMStatisticsInc(CSEDead);
}
