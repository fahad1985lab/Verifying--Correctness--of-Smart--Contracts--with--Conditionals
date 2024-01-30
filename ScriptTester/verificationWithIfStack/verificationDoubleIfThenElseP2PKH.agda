

open import basicBitcoinDataType
module verificationWithIfStack.verificationDoubleIfThenElseP2PKH (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Sum
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite

open import libraries.listLib
open import libraries.equalityLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import instruction


-- open import ledger param
open import verificationP2PKHbasic param


open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.equalitiesIfThenElse param

open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationP2PKH param
open import verificationWithIfStack.verificationP2PKHindexed param
open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param
open import verificationWithIfStack.ifThenElseTheoremPart6 param
open import verificationWithIfStack.ifThenElseTheoremPart7 param
open import verificationWithIfStack.verificationP2PKHwithIfStackindexedPart2 param
open import verificationWithIfStack.hoareTripleStackNonActiveIfStack param
open import verificationWithIfStack.verificationifThenElseP2PKHPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart8nonActive param


-------------------------------------------------------------------------------------
--  First show that P2PKH does nothing on nonactive If stack
------------------------------------------------------------------------------------------
P2PKHdoesNothingOnNonActiveIfStackass : (pubKeyHash₁ pubKeyHash₂ : ℕ )
                             (ifStack₁ : IfStack)
                             (nonActive : IsNonActiveIfStack ifStack₁)
                             (φ :  StackPredicate )
                             → AssumptionIfThenElseNonActIfSt ifStack₁ φ
                                (scriptP2PKH pubKeyHash₁)
                                (scriptP2PKH pubKeyHash₂)
P2PKHdoesNothingOnNonActiveIfStackass pubKeyHash₁ pubKeyHash₂ ifStack₁ nonActive₁ φ .nonActive
         = nonActive₁
P2PKHdoesNothingOnNonActiveIfStackass pubKeyHash₁ pubKeyHash₂ ifStack₁ nonActive₁ φ .ifCaseIfIgnore
         = lemmaP2PKHwithNonActiveIfStack φ pubKeyHash₁ (ifIgnore ∷ ifStack₁) tt
P2PKHdoesNothingOnNonActiveIfStackass pubKeyHash₁ pubKeyHash₂ ifStack₁ nonActive₁ φ .elseCaseSkip elseSkip p
     = lemmaP2PKHwithNonActiveIfStack φ pubKeyHash₂ (elseSkip ∷ ifStack₁) tt
P2PKHdoesNothingOnNonActiveIfStackass pubKeyHash₁ pubKeyHash₂ ifStack₁ nonActive₁ φ .elseCaseSkip ifIgnore p
     = lemmaP2PKHwithNonActiveIfStack φ pubKeyHash₂ (ifIgnore ∷ ifStack₁) tt



correctnessIfThenElseP2PKHNonActiveIfStack : (pubKeyHash₁ pubKeyHash₂ : ℕ )
                             (ifStack₁ : IfStack)
                             (nonActive : IsNonActiveIfStack ifStack₁)
                             (φ :  StackPredicate )
     → <  (liftStackPred2Pred φ  ifStack₁) >ⁱᶠᶠ
          ifThenElseP2PKH pubKeyHash₁ pubKeyHash₂
        < (liftStackPred2Pred φ  ifStack₁ )>
correctnessIfThenElseP2PKHNonActiveIfStack pubKeyHash₁ pubKeyHash₂ ifStack₁ nonActive₁ φ
    = theoremIfThenElseNonActiveStack
      ifStack₁ φ (scriptP2PKH pubKeyHash₁) (scriptP2PKH pubKeyHash₂)
      (P2PKHdoesNothingOnNonActiveIfStackass pubKeyHash₁ pubKeyHash₂ ifStack₁ nonActive₁ φ)



----------------------------------------------------------------------------------------------------
-- Correctness of a twice nested if then else PSPKH script
-----------------------------------------------------------------------------------------------------

p2pkhDoubleIfThenScriptIfCase : (pubKeyHash₁ pubKeyHash₂ :  ℕ ) → BitcoinScript
p2pkhDoubleIfThenScriptIfCase pubKeyHash₁ pubKeyHash₂ = ifThenElseP2PKH pubKeyHash₁ pubKeyHash₂

p2pkhDoubleIfThenScriptElseCase : (pubKeyHash₃ pubKeyHash₄ :  ℕ ) → BitcoinScript
p2pkhDoubleIfThenScriptElseCase pubKeyHash₃ pubKeyHash₄ = ifThenElseP2PKH pubKeyHash₃ pubKeyHash₄

p2pkhDoubleIfThenScript :
         (pubKeyHash₁ pubKeyHash₂ pubKeyHash₃ pubKeyHash₄ : ℕ )
         → BitcoinScript
p2pkhDoubleIfThenScript pubKeyHash₁ pubKeyHash₂ pubKeyHash₃ pubKeyHash₄
     = ifThenElseProg (ifThenElseP2PKH pubKeyHash₁ pubKeyHash₂) (ifThenElseP2PKH pubKeyHash₃ pubKeyHash₄)


weakestPreCondDoubleIfThenElseP2PKHStackForm
    : (pbkh₁ pbkh₂ pbkh₃ pbkh₄ : ℕ ) → StackPredicate
weakestPreCondDoubleIfThenElseP2PKHStackForm pbkh₁ pbkh₂ pbkh₃ pbkh₄
    = truePredaux (weakestPreCondIfThenElseP2PKHStackPred pbkh₁ pbkh₂)  ⊎sp
      falsePredaux (weakestPreCondIfThenElseP2PKHStackPred pbkh₃ pbkh₄)


weakestPreCondDoubleIfThenElseP2PKH : (pbkh₁ pbkh₂ pbkh₃ pbkh₄ : ℕ )
                                      (ifStack₁ : IfStack)
                                     → Predicate
weakestPreCondDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁
    =  liftStackPred2Pred (weakestPreCondDoubleIfThenElseP2PKHStackForm pbkh₁ pbkh₂ pbkh₃ pbkh₄) ifStack₁




assumptionDoubleIfThenElseP2PKH
    : (pbkh₁ pbkh₂ pbkh₃ pbkh₄ : ℕ )
      (ifStack₁ : IfStack)
      (active : IsActiveIfStack ifStack₁)
      →  AssumptionIfThenElse ifStack₁
          (weakestPreCondIfThenElseP2PKHStackPred pbkh₁ pbkh₂)
          (weakestPreCondIfThenElseP2PKHStackPred pbkh₃ pbkh₄)
          acceptStateˢ
          (ifThenElseP2PKH pbkh₁ pbkh₂)
          (ifThenElseP2PKH pbkh₃ pbkh₄)
assumptionDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active .activeIfStack = active
assumptionDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active .ifCaseDo
    = correctnessIfThenElseP2PKH2 pbkh₁ pbkh₂ (ifCase ∷ ifStack₁) tt
assumptionDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active .ifCaseSkip
   = correctnessIfThenElseP2PKHNonActiveIfStack pbkh₁ pbkh₂ (ifSkip ∷ ifStack₁) tt
     (weakestPreCondIfThenElseP2PKHStackPred pbkh₃ pbkh₄)
assumptionDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active .elseCaseDo stackEl activeEl
   = correctnessIfThenElseP2PKH2 pbkh₃ pbkh₄ (stackEl ∷ ifStack₁) activeEl
assumptionDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active .elseCaseSkip stackEl activeEl
   = correctnessIfThenElseP2PKHNonActiveIfStack pbkh₃ pbkh₄ (stackEl ∷ ifStack₁)
     (lemmaIfStackElIsIfSkipOrElseSkip2IsSkip stackEl activeEl) acceptStateˢ


correctnessDoubleIfThenElseP2PKH : (pbkh₁ pbkh₂ pbkh₃ pbkh₄ : ℕ )
                                   (ifStack₁ : IfStack)
                                   (active : IsActiveIfStack ifStack₁)
    → <  weakestPreCondDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ >ⁱᶠᶠ
          p2pkhDoubleIfThenScript pbkh₁ pbkh₂ pbkh₃ pbkh₄
        < liftStackPred2Pred acceptStateˢ ifStack₁  >
correctnessDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active
   = ifThenElseTheorem2 ifStack₁
       (weakestPreCondIfThenElseP2PKHStackPred pbkh₁ pbkh₂)
       (weakestPreCondIfThenElseP2PKHStackPred pbkh₃ pbkh₄)
       acceptStateˢ 
       (ifThenElseP2PKH pbkh₁ pbkh₂)
       (ifThenElseP2PKH pbkh₃ pbkh₄)
       (assumptionDoubleIfThenElseP2PKH pbkh₁ pbkh₂ pbkh₃ pbkh₄ ifStack₁ active)

