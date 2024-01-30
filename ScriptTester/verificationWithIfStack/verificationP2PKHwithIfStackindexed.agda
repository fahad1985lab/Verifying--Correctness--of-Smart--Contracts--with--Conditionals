
open import basicBitcoinDataType

module verificationWithIfStack.verificationP2PKHwithIfStackindexed (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding   (_≤_ ; _<_ ; if_then_else_ )
                       renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.List.NonEmpty hiding (head )
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite

open import libraries.andLib
open import libraries.maybeLib
open import libraries.boolLib
open import libraries.listLib
open import libraries.natLib

open import stack
open import instruction
-- open import ledger param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param

open import verificationP2PKHbasic param

open import verificationWithIfStack.verificationP2PKH param
open import verificationWithIfStack.verificationP2PKHindexed param
open import verificationWithIfStack.verificationP2PKHwithIfStack param


conditionWithStack : (pubKeyHash : ℕ)(ifStack₁ : IfStack) (n : ℕ) → n ≤ 6 → (s : State) → Set
conditionWithStack pubKeyHash ifStack₁ n p
      = liftStackPred2Pred (conditionBasic pubKeyHash n p) ifStack₁


correctStepWithIfStack-to  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 5)
  (s : State)
  → conditionWithStack pubKeyHash ifStack₁ (suc n) p s
  → ((conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p)) ⁺)
                    (⟦ instructions pubKeyHash n p ⟧s s)
correctStepWithIfStack-to pubKeyHash ifStack₁ active  0 _ = correctWithIfStack-1-to ifStack₁ active
correctStepWithIfStack-to pubKeyHash ifStack₁ active  1 _ = correctWithIfStack-2-to ifStack₁ active
correctStepWithIfStack-to pubKeyHash ifStack₁ active  2 _ = correctWithIfStack-3-to ifStack₁ active
correctStepWithIfStack-to pubKeyHash ifStack₁ active  3 _ = correctWithIfStack-4-to pubKeyHash ifStack₁ active
correctStepWithIfStack-to pubKeyHash ifStack₁ active  4 _ = correctWithIfStack-5-to pubKeyHash ifStack₁ active
correctStepWithIfStack-to pubKeyHash ifStack₁ active  5 _ = correctWithIfStack-6-to pubKeyHash ifStack₁ active



correctStepWithIfStack-from  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 5)
  (s : State)
  → ((conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p)) ⁺)
                    (⟦ instructions pubKeyHash n p ⟧s s)
  → conditionWithStack pubKeyHash ifStack₁ (suc n) p s
correctStepWithIfStack-from pubKeyHash ifStack₁ active  0 _ = correctWithIfStack-1-from ifStack₁ active
correctStepWithIfStack-from pubKeyHash ifStack₁ active  1 _ = correctWithIfStack-2-from ifStack₁ active
correctStepWithIfStack-from pubKeyHash ifStack₁ active  2 _ = correctWithIfStack-3-from ifStack₁ active
correctStepWithIfStack-from pubKeyHash ifStack₁ active  3 _ = correctWithIfStack-4-from pubKeyHash ifStack₁ active
correctStepWithIfStack-from pubKeyHash ifStack₁ active  4 _ = correctWithIfStack-5-from pubKeyHash ifStack₁ active
correctStepWithIfStack-from pubKeyHash ifStack₁ active  5 _ = correctWithIfStack-6-from pubKeyHash ifStack₁ active


correctStepWithIfStack-to'  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 5)
  (s : State)
  → conditionWithStack pubKeyHash ifStack₁ (suc n) p s
  → ((conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p)) ⁺)
                    (⟦ instructions pubKeyHash n p ∷ [] ⟧ s)
correctStepWithIfStack-to'  pubKeyHash ifStack₁ active n p s c =
    liftCondOperation2Program-to-simple
      (conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p))
      (instructions pubKeyHash n p)  s
      (correctStepWithIfStack-to pubKeyHash ifStack₁ active n p s c)


correctStepWithIfStack-from'  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 5)
  (s : State)
  → ((conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p)) ⁺)
                    (⟦ instructions pubKeyHash n p ∷ [] ⟧ s)
  → conditionWithStack pubKeyHash ifStack₁ (suc n) p s
correctStepWithIfStack-from'  pubKeyHash ifStack₁ active n p s c =
  correctStepWithIfStack-from pubKeyHash ifStack₁ active n p s
       (liftCondOperation2Program-from-simple
          (conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p))
          (instructions pubKeyHash n p) s c)



correctStepWithIfStack  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 5)
  (s : State)
  →   < conditionWithStack pubKeyHash ifStack₁ (suc n) p  >ⁱᶠᶠ
           (instructions pubKeyHash n p ∷ [])
       < conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p) >
correctStepWithIfStack  pubKeyHash ifStack₁ active n p s  .==>
      = correctStepWithIfStack-to' pubKeyHash ifStack₁ active n p
correctStepWithIfStack  pubKeyHash ifStack₁ active n p s  .<==
      = correctStepWithIfStack-from' pubKeyHash ifStack₁ active n p

correctSeqWithIfStack  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 6)
  (s : State)
  →   < conditionWithStack pubKeyHash ifStack₁ n p  >ⁱᶠᶠ
           (script' pubKeyHash n p)
       < liftStackPred2Pred accept-0Basic ifStack₁  >
correctSeqWithIfStack pubKeyHash ifStack₁ active 0 p s
   = lemmaHoare[]
correctSeqWithIfStack pubKeyHash ifStack₁ active (suc n) p s
  =  conditionWithStack pubKeyHash ifStack₁ (suc n) p
           <><>⟨ instructions pubKeyHash n p ∷ [] ⟩⟨ correctStepWithIfStack pubKeyHash ifStack₁ active n p s  ⟩
     conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p)
           <><>⟨ script' pubKeyHash n (leqSucLemma n 5 p) ⟩⟨ correctSeqWithIfStack pubKeyHash ifStack₁ active n (leqSucLemma n 5 p) s  ⟩ᵉ
     liftStackPred2Pred accept-0Basic ifStack₁
     ∎p

lemmaP2PKHwithStack : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 5)
  (s : State)
  → <  liftStackPred2Pred (wPreCondP2PKHˢ pubKeyHash) ifStack₁  >ⁱᶠᶠ
        scriptP2PKH pubKeyHash
    <  liftStackPred2Pred accept-0Basic ifStack₁   >
lemmaP2PKHwithStack pubKeyHash ifStack₁ active n p s
   = correctSeqWithIfStack pubKeyHash ifStack₁ active 6 tt s
