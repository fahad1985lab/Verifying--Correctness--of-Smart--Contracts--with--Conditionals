open import basicBitcoinDataType

module verificationWithIfStack.ifThenElseTheoremPart7 (param : GlobalParameters) where
-- was verificationP2PKHwithIfStackindexedPart3

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
-- open import Data.List.NonEmpty hiding (head)
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

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param
open import verificationWithIfStack.ifThenElseTheoremPart4 param
open import verificationWithIfStack.ifThenElseTheoremPart5 param
open import verificationWithIfStack.ifThenElseTheoremPart6 param

ifThenElseProg : (ifCaseProg elseCaseProg : BitcoinScript)
                 →   BitcoinScript
ifThenElseProg ifCaseProg elseCaseProg
   = [ opIf ]  ++ ifCaseProg ++ [ opElse ] ++ elseCaseProg ++ [ opEndIf ]


ConclusionIfThenElseTheoImproved : (ifStack₁ : IfStack)
             (φtrue φfalse ψ : StackPredicate)
             (ifCaseProg elseCaseProg : BitcoinScript)
             → Set
ConclusionIfThenElseTheoImproved ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
      =   < liftStackPred2Pred  (truePredaux φtrue ⊎sp falsePredaux φfalse) ifStack₁ >ⁱᶠᶠ
                 ifThenElseProg ifCaseProg elseCaseProg
          <  liftStackPred2Pred ψ ifStack₁   >


conclusionIfThenElse<=> : (ifStack₁ : IfStack)
             (φtrue φfalse : StackPredicate)
             (ifCaseProg elseCaseProg : BitcoinScript)
          →  ((liftStackPred2Pred (truePredaux φtrue ⊎sp falsePredaux φfalse))
                   ifStack₁)
              <=>ᵖ
             ((truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
              (falsePred φfalse ∧p ifStackPredicate ifStack₁))
conclusionIfThenElse<=> .(ifStack s) φtrue φfalse ifCaseProg elseCaseProg .==>e s (conj (inj₁ x) refl)
         = inj₁ (conj x refl)
conclusionIfThenElse<=> .(ifStack s) φtrue φfalse ifCaseProg elseCaseProg .==>e s (conj (inj₂ y) refl)
         = inj₂ (conj y refl)
conclusionIfThenElse<=> .(ifStack s) φtrue φfalse ifCaseProg elseCaseProg .<==e s (inj₁ (conj and3 refl))
         = conj (inj₁ and3) refl
conclusionIfThenElse<=> .(ifStack s) φtrue φfalse ifCaseProg elseCaseProg .<==e s (inj₂ (conj and3 refl))
         = conj (inj₂ and3) refl


ifThenElseTheorem2 : (ifStack₁ : IfStack)
                     (φtrue φfalse ψ : StackPredicate)
                    (ifCaseProg elseCaseProg : BitcoinScript)
                     →  AssumptionIfThenElse ifStack₁  φtrue φfalse ψ ifCaseProg elseCaseProg
                     → ConclusionIfThenElseTheoImproved ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
ifThenElseTheorem2 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assu =
              (liftStackPred2Pred (truePredaux φtrue ⊎sp falsePredaux φfalse)
                 ifStack₁)
                    <=>⟨ conclusionIfThenElse<=> ifStack₁ φtrue φfalse ifCaseProg elseCaseProg ⟩
              ((truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
              (falsePred φfalse ∧p ifStackPredicate ifStack₁))
                     <><>⟨ ifThenElseProg ifCaseProg elseCaseProg
                        ⟩⟨ proofIfThenElseTheorem1 ifStack₁ φtrue φfalse ψ
                          ifCaseProg elseCaseProg assu ⟩ᵉ
               liftStackPred2Pred ψ  ifStack₁
               ∎p


IfThenElseTheorem1SimplifiedImprovedStm : Set₁
IfThenElseTheorem1SimplifiedImprovedStm = (ifStack₁ : IfStack)
                   (φtrue φfalse ψ : StackPredicate)
                   (ifCaseProg elseCaseProg : BitcoinScript)
                   → AssumptionIfThenElseSimplified ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
                   → ConclusionIfThenElseTheoImproved ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg

ifThenElseTheorem1SimplifiedImproved : IfThenElseTheorem1SimplifiedImprovedStm
ifThenElseTheorem1SimplifiedImproved ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assu =
              (liftStackPred2Pred (truePredaux φtrue ⊎sp falsePredaux φfalse)
                 ifStack₁)
                    <=>⟨ conclusionIfThenElse<=> ifStack₁ φtrue φfalse ifCaseProg elseCaseProg ⟩
              ((truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
              (falsePred φfalse ∧p ifStackPredicate ifStack₁))
                     <><>⟨ ifThenElseProg ifCaseProg elseCaseProg
                        ⟩⟨ proofIfThenElseTheorem1Simplified ifStack₁ φtrue φfalse ψ
                          ifCaseProg elseCaseProg assu ⟩ᵉ
               liftStackPred2Pred ψ  ifStack₁
               ∎p
