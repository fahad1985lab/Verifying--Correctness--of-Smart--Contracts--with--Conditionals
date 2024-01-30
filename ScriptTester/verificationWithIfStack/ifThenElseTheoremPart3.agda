{- OPTIONS --allow-unsolved-metas #-}

open import basicBitcoinDataType
module verificationWithIfStack.ifThenElseTheoremPart3 (param : GlobalParameters) where

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
open import Data.List.NonEmpty hiding (head)
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
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param



record  AssumptionIfThenElse (ifStack₁ : IfStack)
                          (φtrue φfalse ψ : StackPredicate)
                          (ifCaseProg elseCaseProg : BitcoinScript) : Set where
   constructor assumptionIfThenElse
   field
-- everything works only if the ifStack₁ is that this ifthenelse is executed:

      activeIfStack : IsActiveIfStack ifStack₁

-- Two conditions to be shown for the ifCaseProg
                      -- liftStackPred2Pred (ifCase ∷ ifStack₁) φtrue
      ifCaseDo   :  -- < liftStackPred2Pred φtrue ∧p  ifStackPredicate (ifCase ∷ ifStack₁) >iff
                    < liftStackPred2Pred φtrue (ifCase ∷ ifStack₁) >ⁱᶠᶠ
                      ifCaseProg
                    < liftStackPred2Pred ψ (ifCase ∷ ifStack₁)   >
                    -- < liftStackPred2Pred ψ ∧p  ifStackPredicate (ifCase ∷ ifStack₁) >

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



{- Now we need that coming from the right after the opEndIf
   where we had any element on the ifstack added so we had
   liftStackPred2PredIgnoreIfStack ρ ∧p  ifStackPredicateAnyTop  ifStack₁
   that we had either the post condition of lemmaTopElementFalse or of lemmaTopElementTrue
-}




lemmaEquivalenceBeforeEndIf : (ifStack₁ : IfStack)
                              (ψ : StackPredicate)
                              →
                    ((liftStackPred2PredIgnoreIfStack ψ ∧p ifStackPredicateAnyDoTop ifStack₁) ⊎p   
                     (liftStackPred2PredIgnoreIfStack ψ ∧p ifStackPredicateAnySkipTop ifStack₁))   
                    <=>ᵖ
                   (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyTop  ifStack₁)
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , c ⟩ (inj₁ (conj and4 refl)) = conj and4 refl
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₂ , c ⟩ (inj₂ (conj and4 refl)) = conj and4 refl
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₂ , c ⟩ (inj₁ (conj and4 refl)) = conj and4 refl
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₂ , c ⟩ (inj₂ (conj and4 refl)) = conj and4 refl
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ (inj₂ (conj and4 refl)) = conj and4 refl
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₁ (conj and4 refl)
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₂ (conj and4 refl)
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , elseCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₁ (conj and4 refl)
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₂ , c ⟩ (conj and4 refl) = inj₂ (conj and4 refl)
lemmaEquivalenceBeforeEndIf ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₂ , c ⟩ (conj and4 refl) = inj₂ (conj and4 refl)




{- and that when we can merge the two pre conditions
   at the beginning of the lemmaTopElementFalse or of lemmaTopElementTrue
-}


lemmaEquivalenceBeforeOpIf : (ifStack₁ : IfStack)
                             (φtrue φfalse : StackPredicate)
      →  ((truePred φtrue ⊎p falsePred φfalse) ∧p ifStackPredicate ifStack₁)
          <=>ᵖ
         ((truePred φtrue ∧p ifStackPredicate ifStack₁)  ⊎p
          (falsePred φfalse ∧p ifStackPredicate ifStack₁))
lemmaEquivalenceBeforeOpIf .ifStack₁ φtrue φfalse .==>e ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ (conj (inj₁ x) refl) = inj₁ (conj x refl)
lemmaEquivalenceBeforeOpIf .(ifStack s) φtrue φfalse .==>e s (conj (inj₂ y) refl) = inj₂ (conj y refl)
lemmaEquivalenceBeforeOpIf .(ifStack s) φtrue φfalse .<==e s (inj₁ (conj and4 refl)) = conj (inj₁ and4) refl
lemmaEquivalenceBeforeOpIf .(ifStack s) φtrue φfalse .<==e s (inj₂ (conj and4 refl)) = conj (inj₂ and4) refl








lemmaTopElementFalse' : (ifStack₁ : IfStack)
                      (φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
-- The following 3 assumptions are the assumptions from
--     AssumptionIfThenElse
-- we need for case where the top element is false
      (activeIfStack : IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁) --IsActiveIfStack ifStack₁)
      (ifCaseSkipIgnore : (x : IfStackEl)
                         → ifStackElementIsIfSkipOrIfIgnore x
                         --IfStackElIsIfSkipOrElseSkip x --ifStackElementIsIfSkipOrIfIgnore x
                         → < liftStackPred2Pred φfalse  (x ∷ ifStack₁) >ⁱᶠᶠ
                            ifCaseProg
                            < liftStackPred2Pred φfalse  (x ∷ ifStack₁) >)
      (elseCaseDo      : (x : IfStackEl)
                         → IsActiveIfStackEl x
                         → < liftStackPred2Pred φfalse  (x ∷ ifStack₁) >ⁱᶠᶠ
                            elseCaseProg
                            < liftStackPred2Pred ψ  (x ∷ ifStack₁) >)
      → < (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       ((opIf ∷ [] ) ++ (ifCaseProg ++ ((opElse ∷ [] ) ++ elseCaseProg)))
        <  liftStackPred2Pred ψ  (elseCase ∷ ifStack₁) >
lemmaTopElementFalse' ifStack₁ φfalse ψ ifCaseProg elseCaseProg activeIfStack ifCaseSkipIgnore elseCaseDo
    = (falsePred φfalse ∧p ifStackPredicate ifStack₁)
            <><>⟨ opIf ∷ []    ⟩⟨ opIfCorrectness2 φfalse ifStack₁ activeIfStack   ⟩
          (liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁))
            <><>⟨ ifCaseProg   ⟩⟨ ifCaseSkipIgnore ifSkip  tt  ⟩
          (liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁))
            <><>⟨ opElse ∷ []   ⟩⟨ opElseCorrectness2 (λ z z₁ → φfalse z z₁) ifStack₁  ⟩
          (liftStackPred2PredIgnoreIfStack ((λ z z₁ → φfalse z z₁)) ∧p
            ifStackPredicate (elseCase ∷ ifStack₁))
            <><>⟨ elseCaseProg ⟩⟨ elseCaseDo elseCase  tt   ⟩ᵉ
            (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )
          ∎p




lemmaTopElementTrue' : (ifStack₁ : IfStack)
                      (φtrue ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
-- The following 3 assumptions are the assumptions from
--     AssumptionIfThenElse
-- we need for case where the top element is false
      (activeIfStack : IsActiveIfStack ifStack₁)
      (ifCaseDo        : (x : IfStackEl)
                       → IsActiveIfStackEl x
                       → < liftStackPred2Pred φtrue  (ifCase ∷ ifStack₁) >ⁱᶠᶠ
                               ifCaseProg
                            < liftStackPred2Pred ψ  (ifCase ∷ ifStack₁) >)
       (ifCaseSkipIgnore : (x : IfStackEl)
                         → ifStackElementIsIfSkipOrIfIgnore x
                         → < liftStackPred2Pred ψ  (x ∷ ifStack₁) >ⁱᶠᶠ
                            ifCaseProg
                            < liftStackPred2Pred ψ  (x ∷ ifStack₁) >)
      (elseCaseSkip  : (x : IfStackEl)
                         → IfStackElIsIfSkipOrElseSkip x
                         → < liftStackPred2Pred ψ  (x ∷ ifStack₁) >ⁱᶠᶠ
                            elseCaseProg
                            < liftStackPred2Pred ψ  (x ∷ ifStack₁) >)

      → < (truePred φtrue ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ --
                       ((opIf ∷ [] ) ++ (ifCaseProg ++ ((opElse ∷ [] ) ++ elseCaseProg )))
      <  liftStackPred2Pred ψ (elseSkip ∷ ifStack₁)  >

lemmaTopElementTrue' ifStack₁ φtrue   ψ ifCaseProg elseCaseProg activeIfStack ifCaseDo ifCaseSkipIgnore   elseCaseSkip
       =
 (truePred φtrue ∧p ifStackPredicate ifStack₁)
 <><>⟨ opIf ∷ [] ⟩⟨ ⊎HoareLemma1 

                (opIf ∷ []) (opIfCorrectness1 φtrue ifStack₁ activeIfStack)
                                 (opIfCorrectness3  ψ  ifStack₁ activeIfStack)    ⟩

 ((liftStackPred2PredIgnoreIfStack φtrue ∧p  (ifStackPredicate (ifCase ∷ ifStack₁))) ⊎p
  (liftStackPred2Pred ψ (ifIgnore ∷ ifStack₁)))
  <><>⟨ ifCaseProg  ⟩⟨ ⊎HoareLemma2
  ifCaseProg  (ifCaseDo  ifCase tt) ((ifCaseSkipIgnore ifIgnore tt ))  ⟩
  ((liftStackPred2PredIgnoreIfStack ψ ∧p  (ifStackPredicate (ifCase ∷ ifStack₁))) ⊎p
  (liftStackPred2Pred ψ  (ifIgnore ∷ ifStack₁)))
  <=>⟨ equivPreds⊎Rev (liftStackPred2PredIgnoreIfStack ψ )   ( ifStackPredicate (ifCase ∷ ifStack₁))  (ifStackPredicate (ifIgnore ∷ ifStack₁))  ⟩
 (liftStackPred2PredIgnoreIfStack ψ ∧p  (ifStackPredicate (ifCase ∷ ifStack₁) ⊎p ifStackPredicate (ifIgnore ∷ ifStack₁)))
 <><>⟨ opElse ∷ []  ⟩⟨ opElseCorrectness1withoutActiveCond  ψ  ifStack₁  ⟩
   ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ))
   <><>⟨ elseCaseProg ⟩⟨ elseCaseSkip elseSkip tt   ⟩ᵉ
 ( liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )
  ∎p









record  AssumptionIfThenElseTest (ifStack₁ : IfStack)
                          (φtrue φfalse ψ : StackPredicate)
                          (ifCaseProg elseCaseProg : BitcoinScript) : Set where
   constructor assumptionIfThenElse
   field
-- everything works only if the ifStack₁ is that this ifthenelse is executed:

      activeIfStack : IsActiveIfStack ifStack₁

-- Two conditions to be shown for the ifCaseProg

      ifCaseDo   :  < liftStackPred2Pred φtrue (ifCase ∷ ifStack₁)    >ⁱᶠᶠ
                      ifCaseProg
                    < liftStackPred2Pred ψ (ifCase ∷ ifStack₁)   >
      ifCaseSkip :  < liftStackPred2Pred φfalse (ifSkip ∷ ifStack₁)   >ⁱᶠᶠ
                      ifCaseProg
                    < liftStackPred2Pred φfalse (ifSkip ∷ ifStack₁)    >

-- Two conditions to be shown for the elseCaseProg

      elseCaseDo    : (x : IfStackEl) → IsActiveIfStackEl x
                  → < liftStackPred2Pred φfalse (x ∷ ifStack₁)   >ⁱᶠᶠ
                     elseCaseProg
                     < liftStackPred2Pred ψ (x ∷ ifStack₁)   >
      elseCaseSkip  : (x : IfStackEl)
                  → IfStackElIsIfSkipOrElseSkip x
                  → < liftStackPred2Pred ψ (x ∷ ifStack₁)    >ⁱᶠᶠ
                       elseCaseProg
                     < liftStackPred2Pred ψ (x ∷ ifStack₁)    >


ConclusionTest : (ifStack₁ : IfStack)
             (φtrue φfalse ψ : StackPredicate)
             (ifCaseProg elseCaseProg : BitcoinScript)
             → Set
ConclusionTest ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
      =  < liftStackPred2Pred (truePredaux φtrue)  ifStack₁  ⊎p
             liftStackPred2Pred (falsePredaux φfalse)  ifStack₁   >ⁱᶠᶠ
                 ((opIf ∷ [] ) ++ ifCaseProg ++ (opElse ∷ [] ) ++ elseCaseProg ++ (opEndIf ∷ [] ))
          <  liftStackPred2Pred ψ ifStack₁  >

IfThenElseTheorem1test : Set₁
IfThenElseTheorem1test = (ifStack₁ : IfStack)
                   (φtrue φfalse ψ : StackPredicate)
                   (ifCaseProg elseCaseProg : BitcoinScript)
                   →  AssumptionIfThenElse ifStack₁  φtrue φfalse ψ ifCaseProg elseCaseProg
                   → ConclusionTest ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg


testIfThenElseTheorem1 : IfThenElseTheorem1 ≡ IfThenElseTheorem1test
testIfThenElseTheorem1 = refl
