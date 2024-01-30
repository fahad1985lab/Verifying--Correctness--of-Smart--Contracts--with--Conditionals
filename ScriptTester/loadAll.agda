open import basicBitcoinDataType

module loadAll (param : GlobalParameters) where




open import libraries.andLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.equalityLib
open import libraries.listLib
open import libraries.maybeLib
open import libraries.natLib


----------------------
-- Root Directory   --
----------------------


open import instruction
open import instructionBasic
open import ledger param
open import semanticBasicOperations param
open import stack
open import stackPredicate



----------------------------------------
-- Directory verificationWithIfStack --
-----------------------------------------
open import verificationWithIfStack.equalitiesIfThenElse param
open import verificationWithIfStack.hoareTriple 
open import verificationWithIfStack.hoareTripleStack2HoareTriple param
open import verificationWithIfStack.hoareTripleStackNonActiveIfStack param
open import verificationWithIfStack.hoareTripleStackScript param
open import verificationWithIfStack.ifStack
open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param
open import verificationWithIfStack.ifThenElseTheoremPart4 param
open import verificationWithIfStack.ifThenElseTheoremPart5 param
open import verificationWithIfStack.ifThenElseTheoremPart6 param
open import verificationWithIfStack.ifThenElseTheoremPart7 param
open import verificationWithIfStack.ifThenElseTheoremPart8nonActive param
open import verificationWithIfStack.ifThenElseTheoremVariant1 param
open import verificationWithIfStack.ifThenElseTheoremVariant2 param 
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.stackSemanticsInstructionsLemma param
open import verificationWithIfStack.state
open import verificationWithIfStack.verificationDoubleIfThenElseP2PKH param
open import verificationWithIfStack.verificationifThenElseP2PKHPart1 param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.verificationP2PKH param
open import verificationWithIfStack.verificationP2PKHindexed param
open import verificationWithIfStack.verificationP2PKHwithIfStack param
open import verificationWithIfStack.verificationP2PKHwithIfStackindexed param
open import verificationWithIfStack.verificationP2PKHwithIfStackindexedPart2 param


