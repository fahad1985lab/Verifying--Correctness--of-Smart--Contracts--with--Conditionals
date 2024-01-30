{- OPTIONS --allow-unsolved-metas #-}

open import basicBitcoinDataType

module verificationWithIfStack.ifThenElseTheoremPart5 (param : GlobalParameters) where


open import  Data.List.Base hiding ( _++_)
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding ( _++_)
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

open import libraries.listLib
open import libraries.natLib
open import libraries.equalityLib
open import libraries.andLib

open import libraries.maybeLib

open import stack
open import instruction
-- open import ledger param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param

open import verificationWithIfStack.ifThenElseTheoremPart1 param
--  open import verificationWithIfStack.verificationP2PKH param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param
open import verificationWithIfStack.ifThenElseTheoremPart4 param
open import verificationWithIfStack.equalitiesIfThenElse param





proofIfThenElseTheorem1Tmp : IfThenElseTheorem1Tmp
proofIfThenElseTheorem1Tmp ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
       ass@(assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
      =
   (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p (falsePred φfalse ∧p ifStackPredicate ifStack₁)
   <><>⟨ (opIf ∷ []) ++ (ifCaseProg ++ ((opElse ∷ []) ++ elseCaseProg))
       ⟩⟨ lemmaIfThenElseExcludingEndIf ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
         ass ⟩
   (liftStackPred2PredIgnoreIfStack  ψ  ∧p ifStackPredicateAnyNonIfIgnoreTop ifStack₁)
   <><>⟨  opEndIf ∷ []  ⟩⟨ opEndIfCorrectness'' ψ ifStack₁  activeIfStack  ⟩ᵉ
   (liftStackPred2Pred ψ  ifStack₁ )
   ∎p




proofIfThenElseTheorem1 : IfThenElseTheorem1
proofIfThenElseTheorem1 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption
  = transfer
       (λ l → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                 l
          <  liftStackPred2Pred ψ  ifStack₁ >)
         (lemmaOpIfProg++[]4 ifCaseProg elseCaseProg)
       (proofIfThenElseTheorem1Tmp ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)





