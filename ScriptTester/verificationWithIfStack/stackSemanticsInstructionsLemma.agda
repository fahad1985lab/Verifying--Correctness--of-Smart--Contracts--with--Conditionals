open import basicBitcoinDataType

module verificationWithIfStack.stackSemanticsInstructionsLemma (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
-- open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite


open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib

open import libraries.maybeLib

open import stack
open import instruction
open import semanticBasicOperations param
open import stackSemanticsInstructions param

open import verificationWithIfStack.state
open import verificationWithIfStack.semanticsInstructions param

-- we show that for nonIf instructios indeep they are defined using ⟦_⟧s
-- this lemma is not needed but good for illustration purposes
lemmaStackSemIsSemantics : (op : InstructionAll) (nonIf : NonIfInstr op)
                          → ⟦ op ⟧s  ≡ stackTransform2StateTransform ⟦ [ op ] ⟧stack
lemmaStackSemIsSemantics opEqual nonif = refl
lemmaStackSemIsSemantics opAdd nonif = refl
lemmaStackSemIsSemantics (opPush x) nonif =  refl
lemmaStackSemIsSemantics opSub nonif = refl
lemmaStackSemIsSemantics opVerify nonif = refl
lemmaStackSemIsSemantics opCheckSig nonif = refl
lemmaStackSemIsSemantics opEqualVerify nonif = refl
lemmaStackSemIsSemantics opDup nonif = refl
lemmaStackSemIsSemantics opDrop nonif = refl
lemmaStackSemIsSemantics opSwap nonif = refl
lemmaStackSemIsSemantics opHash nonif = refl
lemmaStackSemIsSemantics opCHECKLOCKTIMEVERIFY nonif = refl
lemmaStackSemIsSemantics opCheckSig3 nonif = refl
lemmaStackSemIsSemantics opMultiSig nonif = refl




