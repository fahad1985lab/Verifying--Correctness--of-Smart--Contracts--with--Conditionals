

open import basicBitcoinDataType
module verificationWithIfStack.ifThenElseTheoremPart6 (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List
open import Data.Sum
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ )  renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head)
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite

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
-- open import verificationWithIfStack.verificationP2PKH param

open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param
open import verificationWithIfStack.ifThenElseTheoremPart5 param




record  AssumptionIfThenElseSimplified (ifStack₁ : IfStack)
                          (φtrue φfalse ψ : StackPredicate)
                          (ifCaseProg elseCaseProg : BitcoinScript) : Set where
   constructor assumptionIfThenElseSimplified
   field
-- everything works only if the ifStack₁ is that this ifthenelse is executed:

      activeIfStack : IsActiveIfStack ifStack₁

-- Two conditions to be shown for the ifCaseProg

      ifCaseDo        :     (x : IfStackEl)
                         → IsActiveIfStackEl x
                         →  < liftStackPred2Pred φtrue (x ∷ ifStack₁)  >ⁱᶠᶠ
                                   ifCaseProg
                            < liftStackPred2Pred ψ (x ∷ ifStack₁)    >

      ifCaseSkipIgnore : (x : IfStackEl)
                         → IsNonActiveIfStackEl x
                         → < liftStackPred2Pred φfalse (x ∷ ifStack₁)  >ⁱᶠᶠ
                        
                            ifCaseProg
                            < liftStackPred2Pred φfalse  (x ∷ ifStack₁)  >


-- Two conditions to be shown for the elseCaseProg

      elseCaseDo      : (x : IfStackEl)
                         → IsActiveIfStackEl x
                           → < liftStackPred2Pred φfalse  (x ∷ ifStack₁)  >ⁱᶠᶠ

                            elseCaseProg
                            < liftStackPred2Pred ψ (x ∷ ifStack₁)  >

      elseCaseSkip  : (x : IfStackEl)
                         → IsNonActiveIfStackEl x
                         → < liftStackPred2Pred ψ (x ∷ ifStack₁)   >ⁱᶠᶠ
                            elseCaseProg
                            < liftStackPred2Pred ψ (x ∷ ifStack₁)   >
open AssumptionIfThenElseSimplified public

IfThenElseTheorem1Simplified : Set₁
IfThenElseTheorem1Simplified = (ifStack₁ : IfStack)
                   (φtrue φfalse ψ : StackPredicate)
                   (ifCaseProg elseCaseProg : BitcoinScript)
                   → AssumptionIfThenElseSimplified ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
                   → Conclusion ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg

proofIfThenElseTheorem1Simplified : IfThenElseTheorem1Simplified
proofIfThenElseTheorem1Simplified ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
      ( assumptionIfThenElseSimplified activeIfStack₁ ifCaseDo
                                           ifCaseSkipIgnore elseCaseDo elseCaseSkip)
   = proofIfThenElseTheorem1 ifStack₁ φtrue φfalse ψ
       ifCaseProg elseCaseProg
       (assumptionIfThenElse
        activeIfStack₁
        (ifCaseDo ifCase tt) (ifCaseSkipIgnore ifSkip tt)
        elseCaseDo
        (λ x p → elseCaseSkip x
                  (lemmaIfStackElIsIfSkipOrElseSkip2IsSkip x p)))

