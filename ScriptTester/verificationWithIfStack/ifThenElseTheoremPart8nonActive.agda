open import basicBitcoinDataType

module verificationWithIfStack.ifThenElseTheoremPart8nonActive (param : GlobalParameters) where

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
open import Relation.Nullary hiding (True)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality


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


open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.equalitiesIfThenElse param
open import verificationWithIfStack.ifThenElseTheoremPart1 param



{- Proof of the if then else lemma with non active stack -}





opEndIfCorrectnessNonActIfStack1 : (φ :  StackPredicate )  (ifStack₁  : IfStack)
                    → (nonactive : IsNonActiveIfStack ifStack₁)
                    → < liftStackPred2PredIgnoreIfStack φ ∧p  ifStackPredicateElseSkipOrIgnoreOnTop ifStack₁ >ⁱᶠᶠ
                        (opEndIf ∷ [])
                       < liftStackPred2Pred φ   ifStack₁ >
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 ())
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = let
                             isactive1 : True (isActiveIfStack ifStack₁)
                             isactive1 = ∧bproj₁ consis₁

                             nonAct : ¬ (True (isActiveIfStack ifStack₁))
                             nonAct = ¬bLem  nonactive

                          in efq (nonAct isactive1)
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , elseCase ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = efq ( (¬bLem  nonactive) (∧bproj₁ consis₁))
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = efq ( (¬bLem  nonactive) (∧bproj₁ consis₁))
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = conj and3 refl


opEndIfCorrectnessNonActIfStack<=> : (φ :  StackPredicate )  (ifStack₁  : IfStack)
                    → ((liftStackPred2Pred φ  (elseSkip ∷ ifStack₁)) ⊎p
                       (liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁)))
                       <=>ᵖ
                       (liftStackPred2PredIgnoreIfStack φ ∧p  ifStackPredicateElseSkipOrIgnoreOnTop ifStack₁)
opEndIfCorrectnessNonActIfStack<=> φ ifStack₁ .==>e ⟨ currentTime₁ , msg₁ , stack₁ , .(elseSkip ∷ ifStack₁) , consis₁ ⟩ (inj₁ (conj and3 refl)) = conj and3 refl
opEndIfCorrectnessNonActIfStack<=> φ ifStack₁ .==>e ⟨ currentTime₁ , msg₁ , stack₁ , .(ifIgnore ∷ ifStack₁) , consis₁ ⟩ (inj₂ (conj and3 refl)) = conj and3 refl
opEndIfCorrectnessNonActIfStack<=> φ ifStack₁ .<==e ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = inj₁ (conj and3 refl)
opEndIfCorrectnessNonActIfStack<=> φ ifStack₁ .<==e ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = inj₂ (conj and3 refl)





opEndIfCorrectnessNonActIfStack2 : (φ :  StackPredicate )  (ifStack₁  : IfStack)
                    → (nonactive : IsNonActiveIfStack ifStack₁)
                    → < ((liftStackPred2Pred φ  (elseSkip ∷ ifStack₁)) ⊎p
                           (liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁))) >ⁱᶠᶠ
                          (opEndIf ∷ [])
                       < liftStackPred2Pred φ   ifStack₁ >
opEndIfCorrectnessNonActIfStack2 φ ifStack₁ nonactive =
                       ((liftStackPred2Pred φ  (elseSkip ∷ ifStack₁)) ⊎p
                           (liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁)))
                          <=>⟨ opEndIfCorrectnessNonActIfStack<=> φ ifStack₁ ⟩
                        liftStackPred2PredIgnoreIfStack φ ∧p  ifStackPredicateElseSkipOrIgnoreOnTop ifStack₁
                          <><>⟨ opEndIf ∷ [] ⟩⟨ opEndIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive  ⟩ᵉ
                        liftStackPred2Pred φ   ifStack₁
                        ∎p


opElseCorrectnessNonActIfStack1 : (φ :  StackPredicate ) (ifStack₁  : IfStack)
                      (nonactive : IsNonActiveIfStack ifStack₁)
                    → < liftStackPred2Pred φ (ifIgnore ∷ ifStack₁) >ⁱᶠᶠ
                        (opElse ∷ [])
                       < liftStackPred2Pred φ  (elseSkip ∷ ifStack₁) >
opElseCorrectnessNonActIfStack1 φ ifStack₁ nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , .(ifIgnore ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opElseCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = efq ( (¬bLem  nonactive) (∧bproj₁ consis₁))
                         -- same proof as above
opElseCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl) = conj and3 refl


opElseCorrectnessNonActIfStack2 : (φ :  StackPredicate ) (ifStack₁  : IfStack)
                      (nonactive : IsNonActiveIfStack ifStack₁)
                    → < liftStackPred2Pred φ (ifIgnore ∷ ifStack₁) >ⁱᶠᶠ
                        (opElse ∷ [])
                       < (((liftStackPred2Pred φ  (elseSkip ∷ ifStack₁)) ⊎p
                           (liftStackPred2Pred φ  (ifSkip ∷ ifStack₁))) ⊎p
                           (liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁))) >
opElseCorrectnessNonActIfStack2 φ ifStack₁ nonactive
        = ⊎HoareLemma1 ((opElse ∷ []))
          (⊎HoareLemma1 (opElse ∷ [])
            (opElseCorrectnessNonActIfStack1 φ ifStack₁ nonactive)
            (opElseCorrectness4 φ ifStack₁))
          (opElseCorrectness5 φ ifStack₁)


opIfCorrectnessNonActIfStack1 : (φ :  StackPredicate )  (ifStack₁  : IfStack)
                    → (nonactive : IsNonActiveIfStack ifStack₁)
                    → < liftStackPred2Pred φ   ifStack₁ >ⁱᶠᶠ
                        (opIf ∷ [])
                       < liftStackPred2Pred φ   (ifIgnore ∷ ifStack₁) >
opIfCorrectnessNonActIfStack1 φ (ifSkip ∷ ifStack₁) nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , .(ifSkip ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ (elseSkip ∷ ifStack₁) nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , .(elseSkip ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ (ifIgnore ∷ ifStack₁) nonactive .==> ⟨ currentTime₁ , msg₁ , stack₁ , .(ifIgnore ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , zero ∷ stack₁ , [] , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , suc x₁ ∷ stack₁ , [] , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ .(ifSkip ∷ ifStack₂) nonactive .<== ⟨ currentTime₁ , msg₁ , [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ .(elseSkip ∷ ifStack₂) nonactive .<== ⟨ currentTime₁ , msg₁ , [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ .(ifIgnore ∷ ifStack₂) nonactive .<== ⟨ currentTime₁ , msg₁ , [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , zero ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , suc x₂ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , zero ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , suc x₂ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ .(ifSkip ∷ ifStack₂) nonactive .<== ⟨ currentTime₁ , msg₁ , x₂ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ .(elseSkip ∷ ifStack₂) nonactive .<== ⟨ currentTime₁ , msg₁ , x₂ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
opIfCorrectnessNonActIfStack1 φ .(ifIgnore ∷ ifStack₂) nonactive .<== ⟨ currentTime₁ , msg₁ , x₂ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl

opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , [] , [] , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
opIfCorrectnessNonActIfStack1 φ ifStack₁ nonactive .<== ⟨ currentTime₁ , msg₁ , [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()

-----------------------------------------------------------------------------------------------------

record  AssumptionIfThenElseNonActIfSt (ifStack₁ : IfStack)
                          (φ : StackPredicate)
                          (ifCaseProg elseCaseProg : BitcoinScript) : Set where
   constructor assumptionIfThenElseNActIfSt
   field
      nonActive : IsNonActiveIfStack ifStack₁
      ifCaseIfIgnore : < liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁) >ⁱᶠᶠ
                          ifCaseProg
                       < liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁) >
      elseCaseSkip  :  (x : IfStackEl) → ifStackElementIsElseSkipOrIfIgnore x
                       → < liftStackPred2Pred φ   (x ∷ ifStack₁)  >ⁱᶠᶠ
                             elseCaseProg
                          < liftStackPred2Pred φ   (x ∷ ifStack₁)  >

open AssumptionIfThenElseNonActIfSt public

lemmaIfThenElseNonActiveEndingElseSkip :
    (ifStack₁ : IfStack)
    (φ : StackPredicate)
    (ifCaseProg elseCaseProg : BitcoinScript)
    (assumption : AssumptionIfThenElseNonActIfSt ifStack₁ φ ifCaseProg elseCaseProg)
    → < liftStackPred2Pred φ    ifStack₁ >ⁱᶠᶠ
         (opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg))
        < liftStackPred2Pred φ   (elseSkip ∷ ifStack₁)  >
lemmaIfThenElseNonActiveEndingElseSkip ifStack₁ φ ifCaseProg elseCaseProg assu
    =  liftStackPred2Pred φ   ifStack₁
                        <><>⟨ opIf ∷ []  ⟩⟨ opIfCorrectnessNonActIfStack1 φ ifStack₁ (assu .nonActive) ⟩
       liftStackPred2Pred φ   (ifIgnore  ∷ ifStack₁)
                        <><>⟨ ifCaseProg ⟩⟨ assu .ifCaseIfIgnore ⟩
       liftStackPred2Pred φ   (ifIgnore ∷ ifStack₁)
                        <><>⟨ opElse ∷ []  ⟩⟨ opElseCorrectnessNonActIfStack1 φ ifStack₁ (assu .nonActive)  ⟩
       liftStackPred2Pred φ   (elseSkip ∷ ifStack₁)
                        <><>⟨ elseCaseProg  ⟩⟨ assu .elseCaseSkip elseSkip tt  ⟩ᵉ
       liftStackPred2Pred φ   (elseSkip ∷ ifStack₁)
       ∎p

lemmaIfThenElseNonActiveEndingIfIgnore :
    (ifStack₁ : IfStack)
    (φ : StackPredicate)
    (ifCaseProg elseCaseProg : BitcoinScript)
    (assumption : AssumptionIfThenElseNonActIfSt ifStack₁ φ ifCaseProg elseCaseProg)
    → < ⊥p >ⁱᶠᶠ
         (opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg))
        < liftStackPred2Pred φ   (ifIgnore ∷ ifStack₁)  >
lemmaIfThenElseNonActiveEndingIfIgnore ifStack₁ φ ifCaseProg elseCaseProg assu
    =  ⊥p
                      <><>⟨ opIf ∷ []  ⟩⟨ ⊥Lemmap (opIf ∷ [] ) ⟩
       ⊥p
                        <><>⟨ ifCaseProg ⟩⟨ ⊥Lemmap ifCaseProg  ⟩
       ⊥p
                        <><>⟨ opElse ∷ []  ⟩⟨ opElseCorrectness5  φ ifStack₁ ⟩
       liftStackPred2Pred φ   (ifIgnore ∷ ifStack₁)
                        <><>⟨ elseCaseProg  ⟩⟨ assu .elseCaseSkip ifIgnore tt  ⟩ᵉ
       liftStackPred2Pred φ   (ifIgnore ∷ ifStack₁)
       ∎p


lemmaIfThenElseNonActiveEndingElseSkiporIfIgnore :
    (ifStack₁ : IfStack)
    (φ : StackPredicate)
    (ifCaseProg elseCaseProg : BitcoinScript)
    (assumption : AssumptionIfThenElseNonActIfSt ifStack₁ φ ifCaseProg elseCaseProg)
    → < liftStackPred2Pred φ    ifStack₁ >ⁱᶠᶠ
         (opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg))
        < ((liftStackPred2Pred φ  (elseSkip ∷ ifStack₁)) ⊎p
          (liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁)))  >
lemmaIfThenElseNonActiveEndingElseSkiporIfIgnore ifStack₁ φ ifCaseProg elseCaseProg assumption
       = ⊎HoareLemma1
           (opIf ∷ ifCaseProg ++ opElse ∷' elseCaseProg)
           (lemmaIfThenElseNonActiveEndingElseSkip ifStack₁ φ ifCaseProg elseCaseProg assumption)
           (lemmaIfThenElseNonActiveEndingIfIgnore ifStack₁ φ ifCaseProg elseCaseProg assumption)


theoremIfThenElseNonActiveStackaux :
    (ifStack₁ : IfStack)
    (φ : StackPredicate)
    (ifCaseProg elseCaseProg : BitcoinScript)
    (assumption : AssumptionIfThenElseNonActIfSt ifStack₁ φ ifCaseProg elseCaseProg)
    → < liftStackPred2Pred φ    ifStack₁ >ⁱᶠᶠ
         ((opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg)) ++ (opEndIf ∷ []))
        < liftStackPred2Pred φ    ifStack₁ >
theoremIfThenElseNonActiveStackaux ifStack₁ φ ifCaseProg elseCaseProg assu
   = (liftStackPred2Pred φ    ifStack₁)
                   <><>⟨ opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg )
     ⟩⟨ lemmaIfThenElseNonActiveEndingElseSkiporIfIgnore ifStack₁ φ ifCaseProg elseCaseProg assu  ⟩
     ((liftStackPred2Pred φ  (elseSkip ∷ ifStack₁)) ⊎p
     (liftStackPred2Pred φ  (ifIgnore ∷ ifStack₁)))
                   <><>⟨ opEndIf ∷ []  ⟩⟨ opEndIfCorrectnessNonActIfStack2 φ ifStack₁ (assu .nonActive)  ⟩ᵉ
     liftStackPred2Pred φ    ifStack₁
     ∎p




theoremIfThenElseNonActiveStack :
    (ifStack₁ : IfStack)
    (φ : StackPredicate)
    (ifCaseProg elseCaseProg : BitcoinScript)
    (assumption : AssumptionIfThenElseNonActIfSt ifStack₁ φ ifCaseProg elseCaseProg)
    → < liftStackPred2Pred φ    ifStack₁ >ⁱᶠᶠ
         (opIf ∷' ifCaseProg ++ opElse ∷' elseCaseProg ++ opEndIf ∷' [])
        < liftStackPred2Pred φ    ifStack₁ >
theoremIfThenElseNonActiveStack ifStack₁ φ ifCaseProg elseCaseProg assu
  = transfer
      (λ prog →
         < liftStackPred2Pred φ  ifStack₁ >ⁱᶠᶠ prog
         < liftStackPred2Pred φ  ifStack₁ >)
      (lemmaIfThenElseProg== ifCaseProg elseCaseProg)
      (theoremIfThenElseNonActiveStackaux ifStack₁ φ ifCaseProg elseCaseProg assu)
