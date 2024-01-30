open import basicBitcoinDataType
module verificationWithIfStack.ifThenElseTheoremPart4 (param : GlobalParameters) where

open import Data.List.Base hiding (_++_)
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

open import libraries.listLib
open import libraries.natLib
open import libraries.equalityLib
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
open import verificationWithIfStack.equalitiesIfThenElse param
open import verificationWithIfStack.ifThenElseTheoremPart1 param
open import verificationWithIfStack.ifThenElseTheoremPart2 param
open import verificationWithIfStack.ifThenElseTheoremPart3 param



lemmaTopElementIfCase : (ifStack₁ : IfStack)
                      (φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
-- The following 3 assumptions are the assumptions from
--     AssumptionIfThenElse
-- we need for case where the top element is false
      (activeIfStack :  IsActiveIfStack ifStack₁) 
      (elseCaseDo      : (x : IfStackEl)
                         → IsActiveIfStackEl x
                         → < liftStackPred2Pred φfalse (x ∷ ifStack₁) >ⁱᶠᶠ
                            elseCaseProg
                            < liftStackPred2Pred ψ  (x ∷ ifStack₁) >)
      → < ⊥p >ⁱᶠᶠ
                       (opIf ∷ (ifCaseProg ++ (opElse ∷  elseCaseProg)))
      <  liftStackPred2Pred ψ (ifCase ∷ ifStack₁)  >


lemmaTopElementIfCase ifStack₁ φfalse   ψ ifCaseProg elseCaseProg activeIfStack elseCaseDo
       =   ⊥p    <><>⟨  opIf ∷ [] ⟩⟨   ⊥Lemmap (opIf ∷ [])   ⟩
           ⊥p     <><>⟨  ifCaseProg  ⟩⟨   ⊥Lemmap ifCaseProg   ⟩
           ⊥p     <><>⟨  opElse ∷ [] ⟩⟨   opElseCorrectness3 φfalse ifStack₁   ⟩
           (liftStackPred2PredIgnoreIfStack φfalse ∧p
             ifStackPredicate (ifCase ∷ ifStack₁))     <><>⟨  elseCaseProg ⟩⟨    elseCaseDo ifCase tt   ⟩ᵉ
           (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )
           ∎p




lemmaTopElementIfSkip : (ifStack₁ : IfStack)
                      (φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
-- The following 3 assumptions are the assumptions from
--     AssumptionIfThenElse
-- we need for case where the top element is false
      (activeIfStack :  IsActiveIfStack ifStack₁)
      (elseCaseSkip  : (x : IfStackEl)
                         → IfStackElIsIfSkipOrElseSkip x 
                         → < liftStackPred2Pred ψ  (x ∷ ifStack₁) >ⁱᶠᶠ
                            elseCaseProg
                            < liftStackPred2Pred ψ  (x ∷ ifStack₁) >)

      → < ⊥p >ⁱᶠᶠ
                        (opIf ∷ (ifCaseProg ++ (opElse ∷  elseCaseProg)))
      <  liftStackPred2Pred ψ (ifSkip ∷ ifStack₁)  >


lemmaTopElementIfSkip ifStack₁ φfalse   ψ ifCaseProg elseCaseProg activeIfStack elseCaseSkip
  =      ⊥p     <><>⟨  opIf ∷ [] ⟩⟨   ⊥Lemmap (opIf ∷ [])   ⟩
         ⊥p     <><>⟨ ifCaseProg  ⟩⟨   ⊥Lemmap ifCaseProg   ⟩
         ⊥p     <><>⟨  opElse ∷ [] ⟩⟨   opElseCorrectness4 ψ ifStack₁   ⟩
         (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) )
                <><>⟨  elseCaseProg ⟩⟨   elseCaseSkip ifSkip tt   ⟩ᵉ
         (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) )
            ∎p




lemmaEquivalenceBeforeEndIf3 : (ifStack₁ : IfStack)
                              (ψ : StackPredicate)
                              →
                    ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  ) ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  ⊎p
                     (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) ))
                    <=>ᵖ
                   (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop ifStack₁)
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .(elseSkip ∷ ifStack₁) , consis₁ ⟩ (inj₁ (inj₁ (inj₁ (conj and4 refl)))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .(elseCase ∷ ifStack₁) , consis₁ ⟩ (inj₁ (inj₁ (inj₂ (conj and4 refl)))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .(ifCase ∷ ifStack₁) , consis₁ ⟩ (inj₁ (inj₂ (conj and4 refl))) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .(ifSkip ∷ ifStack₁) , consis₁ ⟩ (inj₂ (conj and4 refl)) = conj and4 (conj refl tt)
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₂ (conj and4 refl))
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , elseCase ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₂ (conj and4 refl)))
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₂ (conj and4 refl)
lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and4 (conj refl and6)) = inj₁ (inj₁ (inj₁ (conj and4 refl)))


lemmaEquivalenceBeforeEndIf2WithoutActiveStack : (ifStack₁ : IfStack)
                              (ψ : StackPredicate)
                              →
                    ((liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  ) ⊎p
                     (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁)  ) ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  ⊎p
                     (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) ) ⊎p
                     (liftStackPred2Pred ψ (ifIgnore ∷ ifStack₁) ))
                    <=>ᵖ
                   (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyTop  ifStack₁)
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .elseCase ∷ .ifStack₁ , c ⟩ (inj₁ (inj₁ (inj₁ (inj₁ (conj and4 refl))))) = conj and4 refl
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .elseSkip ∷ .ifStack₁ , c ⟩ (inj₁ (inj₁ (inj₁ (inj₂ (conj and4 refl))))) = conj and4 refl
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .ifCase ∷ .ifStack₁ , c ⟩ (inj₁ (inj₁ (inj₂ (conj and4 refl)))) = conj and4 refl
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .ifSkip ∷ .ifStack₁ , c ⟩ (inj₁ (inj₂ (conj and4 refl))) = conj and4 refl
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .==>e ⟨ time , msg₁ , stack₁ , .ifIgnore ∷ .ifStack₁ , c ⟩ (inj₂ (conj and4 refl)) = conj and4 refl
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₁ (inj₁ (inj₂ (conj and4 refl)))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₁ (inj₂ (conj and4 refl))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , elseCase ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₁ (inj₁ (inj₁ (inj₁ (conj and4 refl))))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₁ (inj₁ (inj₁ (inj₂ (conj and4 refl))))
lemmaEquivalenceBeforeEndIf2WithoutActiveStack ifStack₁ ψ .<==e ⟨ time , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , c ⟩ (conj and4 refl) = inj₂ (conj and4 refl)


lemmaIfThenElseExcludingEndIf4a : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷ (ifCaseProg ++ (opElse ∷  elseCaseProg )))
               < (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )   >
lemmaIfThenElseExcludingEndIf4a ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
            (assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
          = (truePred φtrue ∧p ifStackPredicate ifStack₁)
                             <><>⟨  opIf ∷ []   ⟩⟨   opIfCorrectness1 φtrue ifStack₁ activeIfStack ⟩
            (liftStackPred2Pred φtrue  (ifCase ∷ ifStack₁))
                             <><>⟨  ifCaseProg  ⟩⟨   ifCaseDo ⟩
            (liftStackPred2Pred ψ  (ifCase ∷ ifStack₁))
                             <><>⟨  opElse ∷ []  ⟩⟨   opElseCorrectness1 ψ ifStack₁ activeIfStack ⟩
            (liftStackPred2Pred ψ  (elseSkip ∷ ifStack₁))
                             <><>⟨  elseCaseProg  ⟩⟨   elseCaseSkip elseSkip tt ⟩ᵉ
            (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )
            ∎p




lemmaIfThenElseExcludingEndIf4b : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷ (ifCaseProg ++ (opElse ∷  elseCaseProg )))
               < (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )   >
lemmaIfThenElseExcludingEndIf4b ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
            (assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
          = (falsePred φfalse ∧p ifStackPredicate ifStack₁)
                             <><>⟨  opIf ∷ []   ⟩⟨   opIfCorrectness2 φfalse ifStack₁ activeIfStack ⟩
            (liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁))
                             <><>⟨  ifCaseProg  ⟩⟨   ifCaseSkip ⟩
            (liftStackPred2Pred φfalse  (ifSkip ∷ ifStack₁))
                             <><>⟨  opElse ∷ []  ⟩⟨   opElseCorrectness2 φfalse ifStack₁ ⟩
            (liftStackPred2Pred φfalse  (elseCase ∷ ifStack₁))
                             <><>⟨  elseCaseProg  ⟩⟨   elseCaseDo elseCase tt ⟩ᵉ
            (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )
            ∎p





lemmaIfThenElseExcludingEndIf4 : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷  (ifCaseProg ++ (opElse ∷  elseCaseProg )))
               < (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )  ⊎p
                ((liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  ))  >

lemmaIfThenElseExcludingEndIf4 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption
       = ⊎HoareLemma2
              (opIf ∷ (ifCaseProg ++ (opElse ∷ elseCaseProg )))
              (lemmaIfThenElseExcludingEndIf4a ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)
              (lemmaIfThenElseExcludingEndIf4b ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)






lemmaIfThenElseExcludingEndIf5 : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷ (ifCaseProg ++ (opElse ∷  elseCaseProg)))
               <  ((liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) )  ⊎p
                    (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  ))  ⊎p
                     (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )  >
lemmaIfThenElseExcludingEndIf5 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
    ass@(assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkipIgnore elseCaseDo elseCaseSkip)
  = ⊎HoareLemma1 (opIf ∷ (ifCaseProg ++ (opElse ∷ elseCaseProg)))
                 (lemmaIfThenElseExcludingEndIf4 ifStack₁ φtrue φfalse  ψ  ifCaseProg elseCaseProg ass)
                 (lemmaTopElementIfCase ifStack₁ φfalse  ψ ifCaseProg elseCaseProg activeIfStack elseCaseDo)


  -- using ⊎HoareLemma1 by lemmaIfThenElseExcludingEndIf4
  --  and the lemma showing that (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )
  --  is impossible

lemmaIfThenElseExcludingEndIf6 : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷ (ifCaseProg ++ (opElse ∷  elseCaseProg)))
               < ( (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                   (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )) ⊎p
                   (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )   ⊎p
                   (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) )      >
lemmaIfThenElseExcludingEndIf6 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
     ass@( assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkipIgnore elseCaseDo elseCaseSkip )
   = ⊎HoareLemma1  (opIf ∷ (ifCaseProg ++ opElse ∷' elseCaseProg))
                    (lemmaIfThenElseExcludingEndIf5 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg ass)
                   ( (lemmaTopElementIfSkip ifStack₁ φfalse  ψ ifCaseProg elseCaseProg activeIfStack elseCaseSkip))





lemmaIfThenElseExcludingEndIf : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg))
               < (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁ ) >
lemmaIfThenElseExcludingEndIf ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
            ass@(assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
        =  (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p (falsePred φfalse ∧p ifStackPredicate ifStack₁)
                         <><>⟨ opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg) ⟩⟨
                               lemmaIfThenElseExcludingEndIf6 ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
                               ass ⟩ᵉ
           (( (liftStackPred2Pred ψ (elseSkip ∷ ifStack₁) ) ⊎p
                   (liftStackPred2Pred ψ (elseCase ∷ ifStack₁)  )) ⊎p
                   (liftStackPred2Pred ψ (ifCase ∷ ifStack₁) )   ⊎p
                   (liftStackPred2Pred ψ (ifSkip ∷ ifStack₁) ))
                          <=>⟨  lemmaEquivalenceBeforeEndIf3 ifStack₁ ψ  ⟩
           (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁ )
           ∎p


lemmaIfThenElseWithEndIf : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       ((opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg)) ++ (opEndIf ∷ []))
               < (liftStackPred2Pred ψ   ifStack₁ ) >
lemmaIfThenElseWithEndIf  ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
            ass@(assumptionIfThenElse activeIfStack ifCaseDo ifCaseSkip elseCaseDo elseCaseSkip)
            = (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p (falsePred φfalse ∧p ifStackPredicate ifStack₁)
              <><>⟨ opIf ∷  (ifCaseProg ++ (opElse ∷  elseCaseProg)) ⟩⟨
                    lemmaIfThenElseExcludingEndIf ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg
                      ass ⟩
                  (liftStackPred2PredIgnoreIfStack ψ ∧p  ifStackPredicateAnyNonIfIgnoreTop  ifStack₁ )
              <><>⟨  opEndIf ∷ []  ⟩⟨
                    opEndIfCorrectness'' ψ ifStack₁ activeIfStack ⟩ᵉ
                  (liftStackPred2Pred ψ   ifStack₁ )
                  ∎p


theoremIfThenElse : (ifStack₁ : IfStack)
                      (φtrue φfalse ψ : StackPredicate)
                      (ifCaseProg elseCaseProg : BitcoinScript)
                      (assumption : AssumptionIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg)
            → < (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
                 (falsePred φfalse ∧p ifStackPredicate ifStack₁) >ⁱᶠᶠ
                       (opIf ∷' ifCaseProg ++ opElse ∷' elseCaseProg ++ opEndIf ∷' [])
               < (liftStackPred2Pred ψ   ifStack₁ ) >
theoremIfThenElse ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption
   = transfer
       (λ prog →
          <
          (truePred φtrue ∧p ifStackPredicate ifStack₁) ⊎p
          (falsePred φfalse ∧p ifStackPredicate ifStack₁)
          >ⁱᶠᶠ prog < liftStackPred2Pred ψ  ifStack₁
          >)
       ((lemmaIfThenElseProg== ifCaseProg elseCaseProg))
         (lemmaIfThenElseWithEndIf ifStack₁ φtrue φfalse ψ ifCaseProg elseCaseProg assumption)



