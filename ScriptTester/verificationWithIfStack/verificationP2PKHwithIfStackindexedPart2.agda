open import basicBitcoinDataType

module verificationWithIfStack.verificationP2PKHwithIfStackindexedPart2 (param : GlobalParameters) where

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
open import stackPredicate
open import instruction
-- open import ledger param
open import hoareTripleStack param
open import semanticBasicOperations param


open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.hoareTripleStack2HoareTriple param
open import verificationWithIfStack.verificationLemmas param

open import verificationWithIfStack.semanticsInstructions param

open import verificationP2PKHbasic param

open import verificationWithIfStack.verificationP2PKH param
open import verificationWithIfStack.verificationP2PKHindexed param
open import verificationWithIfStack.verificationP2PKHwithIfStack param
open import verificationWithIfStack.verificationP2PKHwithIfStackindexed param








-----------------------------------------------------------------------------------------------------
--  Proof of correctness for P2PKH  with stack
------------------------------------------------------------------------------------------------




correctnessStackPart-1  : < accept₁ˢ >stack [ opCheckSig ] < accept-0Basic >
correctnessStackPart-1 .==>stg time msg₁ (pubKey ∷ sig ∷ st) p = boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) p
correctnessStackPart-1 .<==stg time msg₁ (pubKey ∷ sig ∷ st) p = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) p

correctnessStackPart-2  : <  accept₂ˢ >stack  [ opVerify ] < accept₁ˢ > -- CorrectnessStackPartOfInstr opVerify accept₂ˢ accept₁ˢ
correctnessStackPart-2 .==>stg time msg₁ (suc x ∷ x₁ ∷ x₂ ∷ st) p = p
correctnessStackPart-2 .<==stg time msg₁ (suc x ∷ x₁ ∷ x₂ ∷ st) p = p

correctnessStackPart-3  : < accept₃ˢ >stack [ opEqual ] < accept₂ˢ > -- CorrectnessStackPartOfInstr
correctnessStackPart-3 .==>stg time msg₁ (x₁ ∷ .x₁ ∷ pbk ∷ sig ∷ s) (conj refl and4) rewrite ( lemmaCompareNat x₁ )  = and4
correctnessStackPart-3 .<==stg time msg₁ (x₁ ∷ x₂ ∷ pbk ∷ sig ∷ s) x rewrite ( lemmaCorrect3From x₁ x₂ pbk sig time msg₁ x )
    = let
        q : True (isSigned  msg₁ sig pbk)
        q = correct3Aux2 (compareNaturals x₁ x₂) pbk sig s time msg₁ x
      in (conj refl q)



correctnessStackPart-4 : (pubKey : ℕ)
                        →  < accept₄ˢ pubKey >stack [ opPush pubKey ] <  accept₃ˢ >
correctnessStackPart-4 pubKey .==>stg time msg₁ (.pubKey ∷ x₁ ∷ x₂ ∷ st) (conj refl and4) = conj refl and4
correctnessStackPart-4 pubKey .<==stg time msg₁ (.pubKey ∷ x₁ ∷ x₂ ∷ st) (conj refl and4) = conj refl and4

correctnessStackPart-5 : (pubKey : ℕ)
                        → <  accept₅ˢ pubKey >stack [ opHash ] < accept₄ˢ pubKey >
correctnessStackPart-5 .(hashFun x) .==>stg time msg₁ (x ∷ x₁ ∷ x₂ ∷ st) (conj refl checkSig) = conj refl checkSig
correctnessStackPart-5 .(hashFun x) .<==stg time msg₁ (x ∷ x₁ ∷ x₂ ∷ st) (conj refl checkSig) = conj refl checkSig

correctnessStackPart-6 : (pubKey : ℕ)
                        → < wPreCondP2PKHˢ pubKey >stack [ opDup ] < accept₅ˢ pubKey >
correctnessStackPart-6 pubKeyHash .==>stg time msg₁ (x ∷ x₁ ∷ st) p = p
correctnessStackPart-6 pubKeyHash .<==stg time msg₁ (x ∷ x₁ ∷ st) p = p


corrrectnessStackPart :  (pubKey : ℕ)(n : ℕ)(p : n ≤ 5)
                         → < conditionBasic pubKey (suc n) p >stack [ instructions pubKey n p ]
                            < conditionBasic pubKey n (leqSucLemma n 5 p) >
corrrectnessStackPart pubKey 0 p = correctnessStackPart-1
corrrectnessStackPart pubKey 1 p = correctnessStackPart-2
corrrectnessStackPart pubKey 2 p = correctnessStackPart-3
corrrectnessStackPart pubKey 3 p = correctnessStackPart-4 pubKey
corrrectnessStackPart pubKey 4 p = correctnessStackPart-5 pubKey
corrrectnessStackPart pubKey 5 p = correctnessStackPart-6 pubKey


p2pkhInstrIsNonIf : (pubKey : ℕ)(n : ℕ)(p : n ≤ 5) → NonIfInstr (instructions pubKey n p)
p2pkhInstrIsNonIf pubKey 0 p = tt
p2pkhInstrIsNonIf pubKey 1 p = tt
p2pkhInstrIsNonIf pubKey 2 p = tt
p2pkhInstrIsNonIf pubKey 3 p = tt
p2pkhInstrIsNonIf pubKey 4 p = tt
p2pkhInstrIsNonIf pubKey 5 p = tt


-- new version now referring to the generic lemma
correctStepWithIfStack-new :  (pubKey : ℕ)(ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                        (n : ℕ)(p : n ≤ 5)
                        → < conditionWithStack pubKey ifStack₁ (suc n) p  >ⁱᶠᶠ
                                 [ instructions pubKey n p ]
                            < conditionWithStack pubKey ifStack₁ n (leqSucLemma n 5 p) >
correctStepWithIfStack-new pubKey ifStack₁ active n p =
           hoartTripleStackPartImpliesHoareTriple ifStack₁ active (instructions pubKey n p)
              (p2pkhInstrIsNonIf pubKey n p)
              (conditionBasic pubKey (suc n) p )
              (conditionBasic pubKey n (leqSucLemma n 5 p))
              (corrrectnessStackPart pubKey n p)

-- copy of the proof from verificationP2PKHwithIfStackindexed.agda
correctSeqWithIfStack-new  : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 6)
  →   < conditionWithStack pubKeyHash ifStack₁ n p  >ⁱᶠᶠ
           (script' pubKeyHash n p)
       < liftStackPred2Pred accept-0Basic ifStack₁  >
correctSeqWithIfStack-new pubKeyHash ifStack₁ active 0 p
   = lemmaHoare[]
correctSeqWithIfStack-new pubKeyHash ifStack₁ active (suc n) p
  =  conditionWithStack pubKeyHash ifStack₁ (suc n) p
           <><>⟨ [ instructions pubKeyHash n p ] ⟩⟨ correctStepWithIfStack-new pubKeyHash ifStack₁ active n p   ⟩
     conditionWithStack pubKeyHash ifStack₁ n (leqSucLemma n 5 p)
           <><>⟨ script' pubKeyHash n (leqSucLemma n 5 p) ⟩⟨ correctSeqWithIfStack-new pubKeyHash ifStack₁ active n (leqSucLemma n 5 p)  ⟩ᵉ
     liftStackPred2Pred accept-0Basic ifStack₁
     ∎p





-- copy of the proof from verificationP2PKHwithIfStackindexed.agda
lemmaP2PKHwithStack-new : (pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (active : IsActiveIfStack ifStack₁)
  →   <  liftStackPred2Pred (weakestPreConditionP2PKHˢ pubKeyHash)  ifStack₁ >ⁱᶠᶠ
        scriptP2PKH pubKeyHash
    < liftStackPred2Pred acceptStateˢ  ifStack₁ >
lemmaP2PKHwithStack-new pubKeyHash ifStack₁ active
   = correctSeqWithIfStack-new pubKeyHash ifStack₁ active 6 tt
