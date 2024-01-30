open import basicBitcoinDataType
module verificationWithIfStack.ifThenElseTheoremPart1 (param : GlobalParameters) where

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
open import Relation.Nullary hiding (True)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite

open import libraries.listLib
open import libraries.natLib
open import libraries.emptyLib
open import libraries.boolLib
open import libraries.andLib

open import libraries.maybeLib

open import stack
open import stackPredicate
open import instruction
-- open import ledger param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param
-- open import verificationWithIfStack.verificationP2PKH
-- open import verificationWithIfStack.verificationP2PKHindexed






-- first top element of IfStack afterwards is ifCase
opIfCorrectness1 : (φ :  StackPredicate ) (ifStack  : IfStack)
                   (active : IsActiveIfStack ifStack) --IsActiveIfStack ifStack) --IsActiveIfStack ifStack)
                    → < truePred φ  ∧p ifStackPredicate ifStack >ⁱᶠᶠ
                      ( opIf ∷ [])
                       < liftStackPred2Pred φ (ifCase ∷ ifStack) >
opIfCorrectness1 φ [] active .==> ⟨ time , msg₁ , suc x ∷ stack₁ , .[] , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness1 φ (ifCase ∷ ifStack₁) active .==> ⟨ time , msg₁ , suc x₁ ∷ stack₁ , .(ifCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness1 φ (elseCase ∷ ifStack₁) active .==> ⟨ time , msg₁ , suc x₁ ∷ stack₁ , .(elseCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (ifCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifCase ∷ .ifStack₂ , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness1 φ (elseCase ∷ ifStack₂) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ (conj and4 refl) = conj and4 refl

-- top element of IfStack afterwards is ifSkip
opIfCorrectness2 : (φ :  StackPredicate ) (ifStack  : IfStack)
                   (active : IsActiveIfStack ifStack) --IsActiveIfStack ifStack) --IsActiveIfStack ifStack)
                    → < falsePred φ  ∧p ifStackPredicate ifStack >ⁱᶠᶠ
                      ( opIf ∷ [])
                       < liftStackPred2Pred φ (ifSkip ∷ ifStack) >
opIfCorrectness2 φ [] active .==> ⟨ time , msg₁ , zero ∷ stack₁ , .[] , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .==> ⟨ time , msg₁ , zero ∷ stack₁ , .(ifCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .==> ⟨ time , msg₁ , zero ∷ stack₁ , .(elseCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , [] , ifCase ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , [] , ifSkip ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , [] , elseCase ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , [] , elseSkip ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x1 ∷ stack₁ , ifCase ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x1 ∷ stack₁ , ifSkip ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x1 ∷ stack₁ , elseCase ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x1 ∷ stack₁ , elseSkip ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x1 ∷ stack₁ , ifIgnore ∷ [] , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifCase ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifSkip ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseCase ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseSkip ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifIgnore ∷ x₁ ∷ ifStack₁ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = conj and4 refl
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness2 φ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()


opIfCorrectness3 : (ψ :  StackPredicate ) (ifStack₁  : IfStack)
                   (active : IsActiveIfStack ifStack₁)
                    → < ⊥p >ⁱᶠᶠ  ( opIf ∷ [])
                       < liftStackPred2Pred ψ  (ifIgnore ∷ ifStack₁) >
opIfCorrectness3  ψ ifStack₁ active .==> s ()
opIfCorrectness3  ψ ifStack₁ active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness3  ψ ifStack₁ active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness3  ψ (.ifSkip ∷ ifStack₁) () .<== ⟨ time , msg₁ , [] , ifSkip ∷ .ifStack₁ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(elseSkip ∷ ifStack₂) () .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(ifIgnore ∷ ifStack₂) () .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(ifSkip ∷ ifStack₂) () .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(elseSkip ∷ ifStack₂) () .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(ifIgnore ∷ ifStack₂) () .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(ifSkip ∷ ifStack₂) () .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(elseSkip ∷ ifStack₂) () .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ (conj and4 refl)
opIfCorrectness3  ψ .(ifIgnore ∷ ifStack₂) () .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ (conj and4 refl)





-- not directly needed but useful
-- top element of IfStack afterwards is elseCase (impossible case)
opIfCorrectness4 : (φ ψ :  StackPredicate ) (ifStack₁  : IfStack)
                   (active : IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁)
                    → < ⊥p >ⁱᶠᶠ  ( opIf ∷ [])
                       < liftStackPred2Pred ψ (elseCase ∷ ifStack₁) >
opIfCorrectness4 φ ψ [] active .==> s ()
opIfCorrectness4 φ ψ (x ∷ ifStack₁) active .==> s ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness4 φ ψ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()


-- top element of IfStack afterwards is elseSkip (impossible case)
opIfCorrectness5 : (φ ψ :  StackPredicate ) (ifStack₁  : IfStack)
                   (active : IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁)
                    → < ⊥p >ⁱᶠᶠ  ( opIf ∷ [])
                       < liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) >
opIfCorrectness5 φ ψ [] active .==> s ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .==> s ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , suc x ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , elseSkip ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ [] active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₁ ∷ stack₁ , [] , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , [] , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , zero ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₂ ∷ stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₂ ∷ stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₂ ∷ stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₂ ∷ stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opIfCorrectness5 φ ψ (x ∷ ifStack₁) active .<== ⟨ time , msg₁ , suc x₂ ∷ stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()



opElseCorrectness1withoutActiveCond  : (ρ :  StackPredicate ) (ifStack₁  : IfStack)
                    → < liftStackPred2PredIgnoreIfStack ρ ∧p  (ifStackPredicate (ifCase ∷ ifStack₁) ⊎p
                                                           ifStackPredicate (ifIgnore ∷ ifStack₁)) >ⁱᶠᶠ
                        (opElse ∷ [])
                       < liftStackPred2Pred ρ  (elseSkip ∷ ifStack₁) >
opElseCorrectness1withoutActiveCond  ρ ifStack₁ .==> ⟨ time , msg₁ , stack₁ , .(ifCase ∷ ifStack₁) , c ⟩ (conj and4 (inj₁ refl)) = conj and4 refl
opElseCorrectness1withoutActiveCond  ρ ifStack₁ .==> ⟨ time , msg₁ , stack₁ , .(ifIgnore ∷ ifStack₁) , c ⟩ (conj and4 (inj₂ refl)) = conj and4 refl
opElseCorrectness1withoutActiveCond  ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = conj and4 (inj₁ refl)
opElseCorrectness1withoutActiveCond  ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , c ⟩ (conj and4 refl) = conj and4 (inj₂ refl)


opElseCorrectness1 : (ρ :  StackPredicate ) (ifStack₁  : IfStack)
                      (active : IsActiveIfStack ifStack₁)
                    → < liftStackPred2Pred ρ  (ifCase ∷ ifStack₁) >ⁱᶠᶠ
                        (opElse ∷ [])
                       < liftStackPred2Pred ρ  (elseSkip ∷ ifStack₁) >
opElseCorrectness1 ρ ifStack₁ active .==> ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (conj and4 refl) = conj and4 refl
opElseCorrectness1 ρ ifStack₁ active .<== ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (conj and4 refl) = conj and4 refl
opElseCorrectness1 ρ ifStack₁ active .<== ⟨ time , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , consis₁ ⟩ (conj and4 refl) =
     let
          a : True (not (isActiveIfStack ifStack₁) ∧b ifStackConsis ifStack₁)
          a = consis₁

          b : True (not (isActiveIfStack ifStack₁))
          b = ∧bproj₁ a

          c = ¬ (True (isActiveIfStack ifStack₁) )
          c = ¬bLem b
      in efq (c active)


opElseCorrectness2 : (ρ  :  StackPredicate ) (ifStack₁  : IfStack)
                    → < liftStackPred2Pred ρ  (ifSkip ∷ ifStack₁) >ⁱᶠᶠ
                        (opElse ∷ [])
                      < liftStackPred2Pred ρ  (elseCase ∷ ifStack₁) >
opElseCorrectness2 ρ   ifStack₁ .==> ⟨ time , msg₁ , stack₁ , .(ifSkip ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opElseCorrectness2 ρ   ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , c ⟩ (conj and4 refl) = conj and4 refl



opElseCorrectness3 : (ρ :  StackPredicate )  (ifStack₁  : IfStack)
                    → < ⊥p >ⁱᶠᶠ
                        (opElse ∷ [])
                       < liftStackPred2Pred ρ  (ifCase ∷ ifStack₁) >
opElseCorrectness3 ρ ifStack₁ .==> p ()
opElseCorrectness3 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opElseCorrectness3 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opElseCorrectness3 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opElseCorrectness3 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opElseCorrectness3 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()







opElseCorrectness4 : (ρ :  StackPredicate )  (ifStack₁  : IfStack)
                    → < ⊥p >ⁱᶠᶠ
                        (opElse ∷ [])
                       < liftStackPred2Pred ρ  (ifSkip ∷ ifStack₁) >
opElseCorrectness4 ρ ifStack₁ .==> s ()
opElseCorrectness4 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opElseCorrectness4 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opElseCorrectness4 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opElseCorrectness4 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opElseCorrectness4 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()


opElseCorrectness5 : (ρ :  StackPredicate )  (ifStack₁  : IfStack)
                    → < ⊥p >ⁱᶠᶠ
                        (opElse ∷ [])
                       < liftStackPred2Pred ρ  (ifIgnore ∷ ifStack₁) >
opElseCorrectness5 ρ ifStack₁ .==> s ()
opElseCorrectness5 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₂ , c ⟩ ()
opElseCorrectness5 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₂ , c ⟩ ()
opElseCorrectness5 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₂ , c ⟩ ()
opElseCorrectness5 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₂ , c ⟩ ()
opElseCorrectness5 ρ ifStack₁ .<== ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ ()




opEndIfCorrectness : (ρ :  StackPredicate )  (ifStack₁  : IfStack)
                    → (active : IsActiveIfStack ifStack₁)
                    → < liftStackPred2PredIgnoreIfStack ρ ∧p  ifStackPredicateAnyTop  ifStack₁ >ⁱᶠᶠ
                        (opEndIf ∷ [])
                       < liftStackPred2Pred ρ ifStack₁  >
opEndIfCorrectness ρ [] active .==> ⟨ time , msg₁ , stack₁ , x ∷ .[] , c ⟩ (conj and4 refl) = conj and4 refl
opEndIfCorrectness ρ (ifCase ∷ ifStack₁) active .==> ⟨ time , msg₁ , stack₁ , x₁ ∷ .(ifCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opEndIfCorrectness ρ (elseCase ∷ ifStack₁) active .==> ⟨ time , msg₁ , stack₁ , x₁ ∷ .(elseCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opEndIfCorrectness ρ [] active .<== ⟨ time , msg₁ , stack₁ , x ∷ .[] , c ⟩ (conj and4 refl) = conj and4 refl
opEndIfCorrectness ρ (ifCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , stack₁ , x ∷ .(ifCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl
opEndIfCorrectness ρ (elseCase ∷ ifStack₁) active .<== ⟨ time , msg₁ , stack₁ , x ∷ .(elseCase ∷ ifStack₁) , c ⟩ (conj and4 refl) = conj and4 refl

opEndIfCorrectness'' : (ρ :  StackPredicate )  (ifStack₁  : IfStack)
                    → (active : IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁)
                    → < liftStackPred2PredIgnoreIfStack ρ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁ >ⁱᶠᶠ
                        (opEndIf ∷ [])
                       < liftStackPred2Pred ρ ifStack₁  >
opEndIfCorrectness'' ρ [] active .==> ⟨ time , msg₁ , stack₁ , x ∷ [] , consis₁ ⟩ (conj and4 and5) = conj and4 refl
opEndIfCorrectness'' ρ (x ∷ i) active .==> ⟨ time , msg₁ , stack₁ , x₁ ∷ .x ∷ .i , consis₁ ⟩ (conj and4 (conj refl and6)) = conj and4 refl
opEndIfCorrectness'' ρ i active .<== ⟨ time , msg₁ , stack₁ , x ∷ .i , consis₁ ⟩ (conj and4 refl) = conj and4 (conj refl (lemmaIfStackIsNonIfIgnore x i consis₁ active))
