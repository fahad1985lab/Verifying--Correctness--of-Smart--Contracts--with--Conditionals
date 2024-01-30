open import basicBitcoinDataType

module verificationWithIfStack.ifThenElseTheoremVariant1 (param : GlobalParameters) where


open import Data.List.Base hiding (_++_)
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ )   renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
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

open import verificationWithIfStack.equalitiesIfThenElse param
open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param
open import verificationWithIfStack.ifThenElseTheoremPart4 param
open import verificationWithIfStack.ifThenElseTheoremPart5 param







opEndIfCorrectness' : (ρ :  StackPredicate )  (ifStack₁  : IfStack)
                    → (active : IsActiveIfStack ifStack₁)
                    → < liftStackPred2PredIgnoreIfStack ρ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁ >ⁱᶠᶠ
                        (opEndIf ∷ [])
                       < liftStackPred2Pred ρ ifStack₁  >
opEndIfCorrectness' ρ [] active .==> ⟨ time , msg₁ , stack₁ , x ∷ [] , consis₁ ⟩ (conj and4 and5) = conj and4 refl
opEndIfCorrectness' ρ (x ∷ i) active .==> ⟨ time , msg₁ , stack₁ , x₁ ∷ .x ∷ .i , consis₁ ⟩ (conj and4 (conj refl and6)) = conj and4 refl
opEndIfCorrectness' ρ i active .<== ⟨ time , msg₁ , stack₁ , x ∷ .i , consis₁ ⟩ (conj and4 refl) = conj and4 (conj refl (lemmaIfStackIsNonIfIgnore x i consis₁ active))



lemmaEquivalenceBeforeEndIf'1 :
     (ifStack₁ : IfStack)
     (active : IsActiveIfStack ifStack₁)
     (ψ : StackPredicate)
      → ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
          (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  ) ⊎p
          (liftStackPred2Pred ψ  (ifCase ∷ ifStack₁) )  ⊎p
          (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁)  ))
         <=>ᵖ
        (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁)
lemmaEquivalenceBeforeEndIf'1 ifStack₁ act  ψ .==>e ⟨ time , msg₁ , stack₁ , .(elseSkip ∷ ifStack₁) , consis₁ ⟩ (inj₁ (inj₁ (inj₁ (conj and4 refl)))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf'1 ifStack₁ act  ψ .==>e ⟨ time , msg₁ , stack₁ , .(elseCase ∷ ifStack₁) , consis₁ ⟩ (inj₁ (inj₁ (inj₂ (conj and4 refl)))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf'1 ifStack₁ act  ψ .==>e ⟨ time , msg₁ , stack₁ , .(ifCase ∷ ifStack₁) , consis₁ ⟩ (inj₁ (inj₂ (conj and4 refl))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf'1 ifStack₁ act  ψ .==>e ⟨ time , msg₁ , stack₁ , .(ifSkip ∷ ifStack₁) , consis₁ ⟩ (inj₂ (conj and4 refl)) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf'1 i act ψ .<==e ⟨ time , msg₁ , stack₁ , ifCase ∷ .i , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₂ (conj and4 refl))
lemmaEquivalenceBeforeEndIf'1 i act ψ .<==e ⟨ time , msg₁ , stack₁ , elseCase ∷ .i , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₂ (conj and4 refl)))
lemmaEquivalenceBeforeEndIf'1 i act ψ .<==e ⟨ time , msg₁ , stack₁ , ifSkip ∷ .i , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₂ (conj and4 refl)
lemmaEquivalenceBeforeEndIf'1 i act ψ .<==e ⟨ time , msg₁ , stack₁ , elseSkip ∷ .i , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₁ (conj and4 refl)))



lemmaIfThenElseExcludingEndIf'2 : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       ((opIf ∷ [] ) ++ (ifCaseProg ++ ((opElse ∷ [] ) ++ elseCaseProg)))
               < ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )) ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  ⊎p
                     (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) ) >
lemmaIfThenElseExcludingEndIf'2 ifStack₁ φtrue φfalse ψ ifcaseProg elsecaseProg
   ass@( assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
  = ⊎HoareLemma1   ((opIf ∷ []) ++ (ifcaseProg ++ ((opElse ∷ []) ++ elsecaseProg)))
                   (lemmaIfThenElseExcludingEndIf5 ifStack₁ φtrue φfalse ψ ifcaseProg elsecaseProg ass)
                   (lemmaTopElementIfSkip ifStack₁ φfalse ψ ifcaseProg elsecaseProg activeIfStack elseCaseSkip)


lemmaIfThenElseExcludingEndIf''2 : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷ ifCaseProg ++ (opElse ∷ []) ++ elseCaseProg)
               < ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  ) ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  ⊎p
                     (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) )) >
lemmaIfThenElseExcludingEndIf''2 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption
     = transfer (λ prog → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       prog
               < ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (elseCase ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  ⊎p
                     (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) )) >)
                   ( ( ((lemmaOpIfProg++[]new ifCaseProg  elseCaseProg))))
                     (lemmaIfThenElseExcludingEndIf'2 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)


lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' : (ifStack₁ : IfStack)
                               (active : IsActiveIfStack ifStack₁)
                              (ψ : StackPredicate)
                              →
                    ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (elseCase ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  ⊎p
                     (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (ifIgnore ∷ ifStack₁) ))
                    <=>ᵖ
                   (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁)
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .==>e  ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (inj₁ (inj₁ (inj₂ (conj and4 refl)))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .==>e ⟨ time , msg₁ , stack₁ , elseCase ∷ .ifStack₁ , consis₁ ⟩ (inj₁ (inj₁ (inj₁ (inj₂ (conj and4 refl))))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .==>e ⟨ time , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , consis₁ ⟩ (inj₁ (inj₂ (conj and4 refl))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .==>e ⟨ time , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , consis₁ ⟩ (inj₁ (inj₁ (inj₁ (inj₁ (conj and4 refl))))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .==>e ⟨ time , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , consis₁ ⟩ (inj₂ (conj and4 refl))
                                       = conj and4 (conj refl (lemmaIfStackIsNonIfIgnore ifIgnore ifStack₁ consis₁ active))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .<==e ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₂ (conj and4 refl)))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .<==e ⟨ time , msg₁ , stack₁ , elseCase ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₁ (inj₂ (conj and4 refl))))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .<==e ⟨ time , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₂ (conj and4 refl))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack'' ifStack₁ active ψ .<==e ⟨ time , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₁ (inj₁ (conj and4 refl))))



lemmaIfThenElseExcludingEndIf' : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (((opIf ∷' []  ++ ifCaseProg ++ opElse ∷' []  ++ elseCaseProg) )  )
               < (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁) >
lemmaIfThenElseExcludingEndIf' ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
            ass@(assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
            =         (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p (falsePred φfalse ∧p ifStackPredicate ifStack₁)
                       <><>⟨ opIf ∷' [] ++ ifCaseProg ++ opElse ∷' [] ++ elseCaseProg
                           ⟩⟨ lemmaIfThenElseExcludingEndIf''2 ifStack₁ φtrue φfalse ψ ifCaseProg
                                                               elseCaseProg ass ⟩ᵉ
             ( (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )
             ⊎p   (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )
             ⊎p (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )
             ⊎p (liftStackPred2Pred ψ  (ifSkip ∷ ifStack₁) ))
                    <=>⟨ lemmaEquivalenceBeforeEndIf'1   ifStack₁ activeIfStack  ψ ⟩ 
            ((liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁))
            ∎p
