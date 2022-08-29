open import basicBitcoinDataType

module loadAll (param : GlobalParameters) where

-- Loads all files by directory in alphabetic order
-- Alphabetic order is used so that we can easily check that it is complete
-- and therefore by typechecking this file we can guarantee that the complete
-- code is type correct.


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

open import verificationBitcoinScripts.hoareTriple param
open import verificationBitcoinScripts.ifStack
open import verificationBitcoinScripts.predicate
open import verificationBitcoinScripts.semanticsInstructions param
open import verificationBitcoinScripts.state

