open import basicBitcoinDataType

module verificationWithIfStack.ifThenElseTheoremPart2 (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base hiding (_++_)
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head)
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite
-- open import verificationWithIfStack.verificationP2PKH

open import libraries.andLib

open import libraries.maybeLib

open import stack
open import stackPredicate
open import instruction
-- open import ledger param

open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.ifStack
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.ifThenElseTheoremPart1 param



opIfCorrectness3test : ( ψ :  StackPredicate ) (ifStack₁  : IfStack)
        (active : IsActiveIfStack ifStack₁)
          → < ⊥p >ⁱᶠᶠ  ( opIf ∷ [])
         < liftStackPred2Pred ψ (ifIgnore ∷ ifStack₁) >
opIfCorrectness3test  ψ ifStack₁ active =
  ⊥p
   <><>⟨ opIf ∷ [] ⟩⟨ (opIfCorrectness3  ψ ifStack₁ active)  ⟩
   (liftStackPred2Pred ψ  (ifIgnore ∷ ifStack₁))
  ∎p


opIfCorrectness3test2 : (φ ψ :  StackPredicate ) (ifStack₁  : IfStack)
                        (active : IsActiveIfStack ifStack₁) 
                        → < ⊥p >ⁱᶠᶠ  ( opIf ∷ [])
                           < liftStackPred2Pred ψ  (ifIgnore ∷ ifStack₁) >
opIfCorrectness3test2 φ ψ ifStack₁ active =
   ⊥p
     <=>⟨ refl<=> ⊥p  ⟩
   ⊥p
    <><>⟨ opIf ∷ [] ⟩⟨  (opIfCorrectness3  ψ ifStack₁ active)  ⟩
    (liftStackPred2Pred ψ  (ifIgnore ∷ ifStack₁))
   ∎p


