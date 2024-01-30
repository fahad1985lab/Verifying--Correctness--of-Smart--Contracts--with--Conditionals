open import basicBitcoinDataType

module verificationWithIfStack.verificationifThenElseP2PKHPart1 (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
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
open import libraries.natLib
open import libraries.boolLib
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

open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationP2PKH param
open import verificationWithIfStack.verificationP2PKHindexed param
open import verificationWithIfStack.ifThenElseTheoremPart6 param
open import verificationWithIfStack.ifThenElseTheoremPart7 param
open import verificationWithIfStack.verificationP2PKHwithIfStackindexedPart2 param
open import verificationWithIfStack.hoareTripleStackNonActiveIfStack param


IsActiveIfStackElImpliesExecution :
   (ifStackEl : IfStackEl)
   (ifStack₁ : IfStack)
   → IsActiveIfStackEl ifStackEl
   → IsActiveIfStack (ifStackEl ∷ ifStack₁)
IsActiveIfStackElImpliesExecution ifCase ifStack₁ isDo = tt
IsActiveIfStackElImpliesExecution elseCase ifStack₁ isDo = tt


ifStackElementIsSkipImpliesSkipping :
   (ifStackEl : IfStackEl)
   (ifStack₁ : IfStack)
   → IsNonActiveIfStackEl ifStackEl
   → IsNonActiveIfStack (ifStackEl ∷ ifStack₁)
ifStackElementIsSkipImpliesSkipping ifSkip ifStack₁ isSkip = tt
ifStackElementIsSkipImpliesSkipping elseSkip ifStack₁ isSkip = tt
ifStackElementIsSkipImpliesSkipping ifIgnore ifStack₁ isSkip = tt


assumptionIfThenElseP2PKH-ifCaseDo :
   (pubKeyHash : ℕ )(ifStack₁ : IfStack)
   → (x : IfStackEl)
   → IsActiveIfStackEl x
   →  < liftStackPred2Pred (wPreCondP2PKHˢ pubKeyHash) (x ∷ ifStack₁)  >ⁱᶠᶠ
                              scriptP2PKH pubKeyHash
       <  liftStackPred2Pred accept-0Basic (x ∷ ifStack₁)   >
assumptionIfThenElseP2PKH-ifCaseDo pubKeyHash ifStack₁ x isdo
    = lemmaP2PKHwithStack-new pubKeyHash (x ∷ ifStack₁) (IsActiveIfStackElImpliesExecution x ifStack₁ isdo)

assumptionIfThenElseP2PKH-ifCaseSkipIgnore :
   (pubKeyHash₁ pubKeyHash₂ : ℕ )(ifStack₁ : IfStack)
   → (x : IfStackEl)
   → IsNonActiveIfStackEl x
   →  < liftStackPred2Pred (wPreCondP2PKHˢ pubKeyHash₁) (x ∷ ifStack₁)  >ⁱᶠᶠ
                              scriptP2PKH pubKeyHash₂
       < liftStackPred2Pred (wPreCondP2PKHˢ pubKeyHash₁) (x ∷ ifStack₁)   >
assumptionIfThenElseP2PKH-ifCaseSkipIgnore pubKeyHash₁ pubKeyHash₂ ifStack₁ x isSkip
   = lemmaP2PKHwithNonActiveIfStack (wPreCondP2PKHˢ pubKeyHash₁) pubKeyHash₂ (x ∷ ifStack₁)
      (ifStackElementIsSkipImpliesSkipping x ifStack₁ isSkip)


assumptionIfThenElseP2PKH-elseSkipIgnore :
   (pubKeyHash₂ : ℕ )(ifStack₁ : IfStack)
   → (x : IfStackEl)
   → IsNonActiveIfStackEl x
   →  < liftStackPred2Pred accept-0Basic (x ∷ ifStack₁) >ⁱᶠᶠ
                              scriptP2PKH pubKeyHash₂
       < liftStackPred2Pred accept-0Basic (x ∷ ifStack₁)   >
assumptionIfThenElseP2PKH-elseSkipIgnore pubKeyHash₂ ifStack₁ x isSkip
   = lemmaP2PKHwithNonActiveIfStack (λ z z₁ z₂ → acceptStateˢ z z₁ z₂) pubKeyHash₂ (x ∷ ifStack₁)
     (ifStackElementIsSkipImpliesSkipping x ifStack₁ isSkip)



assumptionIfThenElseP2PKH :
   (pubKeyHash₁ pubKeyHash₂ : ℕ )(ifStack₁ : IfStack)
   (active : IsActiveIfStack ifStack₁)
   →  AssumptionIfThenElseSimplified ifStack₁ (wPreCondP2PKHˢ pubKeyHash₁) (wPreCondP2PKHˢ pubKeyHash₂)
       accept-0Basic (scriptP2PKH pubKeyHash₁) (scriptP2PKH pubKeyHash₂)
assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active .activeIfStack  = active
assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active .ifCaseDo
       = assumptionIfThenElseP2PKH-ifCaseDo pubKeyHash₁ ifStack₁
assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active .ifCaseSkipIgnore x x₁
       = assumptionIfThenElseP2PKH-ifCaseSkipIgnore pubKeyHash₂ pubKeyHash₁ ifStack₁ x x₁
assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active .elseCaseDo
       = assumptionIfThenElseP2PKH-ifCaseDo pubKeyHash₂ ifStack₁
assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active .elseCaseSkip
       = assumptionIfThenElseP2PKH-elseSkipIgnore pubKeyHash₂ ifStack₁

ifThenElseP2PKH : (pubKeyHash₁ pubKeyHash₂ : ℕ ) → BitcoinScript
ifThenElseP2PKH pubKeyHash₁ pubKeyHash₂ =
   ifThenElseProg (scriptP2PKH pubKeyHash₁) (scriptP2PKH pubKeyHash₂)



-- test
test = ifThenElseP2PKH 555 666
{-
test = opIf ∷ opDup ∷ opHash ∷ opPush 555 ∷ opEqual ∷ opVerify ∷ opCheckSig   ∷
       opElse ∷ opDup ∷ opHash ∷ opPush 666 ∷ opEqual ∷ opVerify ∷ opCheckSig ∷
       opEndIf ∷ []
-}


weakestPreCondIfThenElseP2PKHStackPred : (pubKeyHash₁ pubKeyHash₂ : ℕ )
                                         → StackPredicate
weakestPreCondIfThenElseP2PKHStackPred pubKeyHash₁ pubKeyHash₂
           = truePredaux (weakestPreConditionP2PKHˢ pubKeyHash₁)
                              ⊎sp falsePredaux (weakestPreConditionP2PKHˢ pubKeyHash₂)


weakestPreCondIfThenElseP2PKHS : (pubKeyHash₁ pubKeyHash₂ : ℕ )
                                 (ifStack₁ : IfStack)
                                 → Predicate
weakestPreCondIfThenElseP2PKHS pubKeyHash₁ pubKeyHash₂ ifStack₁
    =  liftStackPred2Pred (weakestPreCondIfThenElseP2PKHStackPred pubKeyHash₁ pubKeyHash₂)
              ifStack₁




correctnessIfThenElseP2PKH1 : (pubKeyHash₁ pubKeyHash₂ : ℕ )
                             (ifStack₁ : IfStack)
                             (active : IsActiveIfStack ifStack₁)
     → <  (truePred (weakestPreConditionP2PKHˢ pubKeyHash₁) ∧p ifStackPredicate ifStack₁) ⊎p
           (falsePred (weakestPreConditionP2PKHˢ pubKeyHash₂) ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
          ifThenElseP2PKH pubKeyHash₁ pubKeyHash₂
        < liftStackPred2Pred acceptStateˢ  ifStack₁ >
correctnessIfThenElseP2PKH1 pubKeyHash₁ pubKeyHash₂ ifStack₁ active
     = proofIfThenElseTheorem1Simplified ifStack₁
       (weakestPreConditionP2PKHˢ pubKeyHash₁) (weakestPreConditionP2PKHˢ pubKeyHash₂)
       acceptStateˢ
       (scriptP2PKH pubKeyHash₁) (scriptP2PKH pubKeyHash₂)
       (assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active)




correctnessIfThenElseP2PKH2 : (pubKeyHash₁ pubKeyHash₂ : ℕ )
                             (ifStack₁ : IfStack)
                             (active : IsActiveIfStack ifStack₁)
     → <  weakestPreCondIfThenElseP2PKHS pubKeyHash₁ pubKeyHash₂ ifStack₁ >ⁱᶠᶠ
          ifThenElseP2PKH pubKeyHash₁ pubKeyHash₂
        < liftStackPred2Pred acceptStateˢ  ifStack₁ >
correctnessIfThenElseP2PKH2 pubKeyHash₁ pubKeyHash₂ ifStack₁ active
     = ifThenElseTheorem1SimplifiedImproved ifStack₁
       (weakestPreConditionP2PKHˢ pubKeyHash₁) (weakestPreConditionP2PKHˢ pubKeyHash₂)
       acceptStateˢ
       (scriptP2PKH pubKeyHash₁) (scriptP2PKH pubKeyHash₂)
       (assumptionIfThenElseP2PKH pubKeyHash₁ pubKeyHash₂ ifStack₁ active)
