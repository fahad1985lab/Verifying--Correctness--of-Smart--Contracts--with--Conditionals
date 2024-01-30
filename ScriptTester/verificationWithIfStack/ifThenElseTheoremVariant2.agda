
open import basicBitcoinDataType

module verificationWithIfStack.ifThenElseTheoremVariant2 (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base hiding (_++_)
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
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
--open import Agda.Builtin.Equality.Rewrite

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

--  activeStack is part of AssumptionIfThenSElse
lemmaElseSkip2PhiTrue : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
      → < (truePred φtrue ∧p ifStackPredicate ifStack₁ ) >ⁱᶠᶠ --
                       ((opIf ∷ [] ) ++ (ifCaseProg ++ ((opElse ∷ [] ) ++ elseCaseProg )))
      <  liftStackPred2Pred ψ (elseSkip ∷ ifStack₁)  >
lemmaElseSkip2PhiTrue ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
      (assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
      = (truePred φtrue ∧p ifStackPredicate ifStack₁)
                <><>⟨  opIf ∷ [] ⟩⟨ opIfCorrectness1 φtrue ifStack₁ activeIfStack  ⟩
        (liftStackPred2Pred φtrue (ifCase ∷ ifStack₁)  )
                <><>⟨ ifCaseProg  ⟩⟨ ifCaseDo   ⟩
        (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )
                <><>⟨  (opElse ∷ [])   ⟩⟨ opElseCorrectness1  ψ  ifStack₁ activeIfStack  ⟩
        (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )
                <><>⟨  elseCaseProg  ⟩⟨ elseCaseSkip elseSkip tt  ⟩ᵉ
        (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )
        ∎p





lemmaElseCase2PhiTrue : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
      → < (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       ((opIf ∷ [] ) ++ (ifCaseProg ++ ((opElse ∷ [] ) ++ elseCaseProg )))
      <  liftStackPred2Pred ψ (elseCase ∷ ifStack₁ ) >
lemmaElseCase2PhiTrue ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
     (assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
      = (falsePred φfalse ∧p ifStackPredicate ifStack₁)
          <><>⟨  opIf ∷ [] ⟩⟨ opIfCorrectness2 φfalse ifStack₁ activeIfStack ⟩
         (liftStackPred2Pred φfalse ( ifSkip ∷ ifStack₁))
         <><>⟨ ifCaseProg  ⟩⟨ ifCaseSkip  ⟩
         ((liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁)))
         <><>⟨  (opElse ∷ [])   ⟩⟨ opElseCorrectness2  φfalse  ifStack₁  ⟩
         (((liftStackPred2Pred  φfalse  (elseCase ∷ ifStack₁))))
         <><>⟨  elseCaseProg  ⟩⟨ elseCaseDo elseCase tt  ⟩ᵉ
        (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )
          ∎p


lemmaIfThenElseExcludingEndIf4' : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       ((opIf ∷ [] ) ++ (ifCaseProg ++ ((opElse ∷ [] ) ++ elseCaseProg )))
               < (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )  ⊎p
                (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )  >

lemmaIfThenElseExcludingEndIf4' ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption
       = ⊎HoareLemma2
              ((opIf ∷ []) ++ (ifCaseProg ++ ((opElse ∷ []) ++ elseCaseProg )))
              (lemmaElseSkip2PhiTrue ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)
              (lemmaElseCase2PhiTrue ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)
