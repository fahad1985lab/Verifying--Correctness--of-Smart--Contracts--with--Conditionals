

open import basicBitcoinDataType
module verificationBitcoinScripts.ifThenElseTheorem (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base hiding (_++_)
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Unit  hiding (_≤_)
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


open import libraries.andLib
open import libraries.maybeLib

open import stack
open import stackPredicate
open import instruction


open import verificationBitcoinScripts.ifStack
open import verificationBitcoinScripts.state
open import verificationBitcoinScripts.predicate
open import verificationBitcoinScripts.semanticsInstructions param
open import verificationBitcoinScripts.hoareTriple param



record  AssumptionIfThenElse (ifStack₁ : IfStack)
                          (φtrue φfalse ψ : StackPredicate)
                          (ifCaseProg elseCaseProg : BitcoinScript) : Set where
   constructor assumptionIfThenElse
   field
-- everything works only if the ifStack₁ is that this ifthenelse is executed:

      activeIfStack : IsActiveIfStack ifStack₁

-- Two conditions to be shown for the ifCaseProg
                      
      ifCaseDo   : 
                    < liftStackPred2Pred φtrue (ifCase ∷ ifStack₁) >ⁱᶠᶠ
                      ifCaseProg
                    < liftStackPred2Pred ψ (ifCase ∷ ifStack₁)   >
                    

      ifCaseSkip :  < liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁) >ⁱᶠᶠ
                      ifCaseProg
                    < liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁) >

-- Two conditions to be shown for the elseCaseProg

      elseCaseDo    : (x : IfStackEl) → IsActiveIfStackEl x
                  → < liftStackPred2Pred φfalse  (x ∷ ifStack₁) >ⁱᶠᶠ
                     elseCaseProg
                     < liftStackPred2Pred ψ  (x ∷ ifStack₁) >
      elseCaseSkip  : (x : IfStackEl)
                  → IfStackElIsIfSkipOrElseSkip x
                  → < liftStackPred2Pred ψ  (x ∷ ifStack₁) >ⁱᶠᶠ
                       elseCaseProg
                     < liftStackPred2Pred ψ  (x ∷ ifStack₁) >

open AssumptionIfThenElse public



ConclusionTmp : (ifStack₁ : IfStack)
             (φtrue φfalse ψ : StackPredicate)
             (ifCaseProg elseCaseProg : BitcoinScript)
             → Set
ConclusionTmp ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
      =  < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
           (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
        ((opIf ∷ ifCaseProg ++ (opElse ∷ elseCaseProg)) ++ (opEndIf ∷ [] ))
         < liftStackPred2Pred ψ  ifStack₁ >

IfThenElseTheorem1Tmp : Set₁
IfThenElseTheorem1Tmp = (ifStack₁ : IfStack)
                   (φtrue φfalse ψ : StackPredicate)
                   (ifCaseProg elseCaseProg : BitcoinScript)
                   → AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
                   → ConclusionTmp ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg


Conclusion : (ifStack₁ : IfStack)
             (φtrue φfalse ψ : StackPredicate)
             (ifCaseProg elseCaseProg : BitcoinScript)
             → Set
Conclusion ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
      =   < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                 ((opIf ∷ [] ) ++ ifCaseProg ++ (opElse ∷ [] ) ++ elseCaseProg ++ (opEndIf ∷ [] ))
          <  liftStackPred2Pred ψ  ifStack₁ >


-- the statement of the theorem we want to prove is

IfThenElseTheorem1 : Set₁
IfThenElseTheorem1 = (ifStack₁ : IfStack)
                   (φtrue φfalse ψ : StackPredicate)
                   (ifCaseProg elseCaseProg : BitcoinScript)
                   →  AssumptionIfThenElse ifStack₁  φtrue φfalse ψ ifCaseProg elseCaseProg
                   → Conclusion ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg


