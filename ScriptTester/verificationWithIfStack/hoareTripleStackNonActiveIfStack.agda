open import basicBitcoinDataType

module verificationWithIfStack.hoareTripleStackNonActiveIfStack (param : GlobalParameters) where
-- was in verificationP2PKHwithIfStackindexedPart4

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
open import instruction
open import stack
open import stackPredicate
open import instruction
open import stackSemanticsInstructions param
-- open import ledger param
open import hoareTripleStack param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTripleStack2HoareTriple param
open import verificationWithIfStack.verificationP2PKHindexed param
open import verificationWithIfStack.verificationP2PKHwithIfStackindexedPart2 param
open import verificationP2PKHbasic param


lift2StateCorrectnessNonActiveStackFun=> : (ifStack₁ : IfStack)
                                  (nonactive : IsNonActiveIfStack ifStack₁)
                                  (φ : StackPredicate)
                                  (stackfun : StackTransformer)
                                  (s : State)
                                  → liftStackPred2Pred φ ifStack₁  s
                                  → ( (liftStackPred2Pred φ ifStack₁ ) ⁺)
                                                    (stackTransform2StateTransform stackfun s)
lift2StateCorrectnessNonActiveStackFun=> (ifSkip ∷ ifStack₁) nonactive φ stackfun ⟨ currentTime₁ , msg₁ , stack₁ , .(ifSkip ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun=> (elseSkip ∷ ifStack₁) nonactive φ stackfun ⟨ currentTime₁ , msg₁ , stack₁ , .(elseSkip ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun=> (ifIgnore ∷ ifStack₁) nonactive φ stackfun ⟨ currentTime₁ , msg₁ , stack₁ , .(ifIgnore ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl



lift2StateCorrectnessNonActiveStackFun<=aux : (ifStack₁ ifStack₂ : IfStack)
       (nonactive : IsNonActiveIfStack ifStack₁)
       (φ : StackPredicate)
       (currentTime₁ : Time)
       (msg₁ : Msg)
       (consis₁ : IfStackConsis ifStack₂)
       (stack₁ : Stack)
       (stackfunres : Maybe Stack)
       → ((λ s → φ (currentTime s) (msg s) (stack s) ∧  (ifStack s ≡ ifStack₁)) ⁺)
          (exeTransformerDepIfStack' (liftStackToStateTransformerAux' stackfunres)
             ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₂ , consis₁ ⟩)
       → φ currentTime₁ msg₁ stack₁ ∧ (ifStack₂ ≡ ifStack₁)
lift2StateCorrectnessNonActiveStackFun<=aux .[] [] () φ currentTime₁ msg₁ consis₁ stack₁ (just x₁) (conj and3 refl)
lift2StateCorrectnessNonActiveStackFun<=aux .(ifCase ∷ ifStack₂) (ifCase ∷ ifStack₂) () φ currentTime₁ msg₁ consis₁ stack₁ (just x₁) (conj and3 refl)
lift2StateCorrectnessNonActiveStackFun<=aux .(elseCase ∷ ifStack₂) (elseCase ∷ ifStack₂) () φ currentTime₁ msg₁ consis₁ stack₁ (just x₁) (conj and3 refl)
lift2StateCorrectnessNonActiveStackFun<=aux .(ifSkip ∷ ifStack₂) (ifSkip ∷ ifStack₂) nonactive φ currentTime₁ msg₁ consis₁ stack₁ (just x₁) (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun<=aux .(ifSkip ∷ ifStack₂) (ifSkip ∷ ifStack₂) nonactive φ currentTime₁ msg₁ consis₁ stack₁ nothing (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun<=aux .(elseSkip ∷ ifStack₂) (elseSkip ∷ ifStack₂) nonactive φ currentTime₁ msg₁ consis₁ stack₁ (just x₁) (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun<=aux .(elseSkip ∷ ifStack₂) (elseSkip ∷ ifStack₂) nonactive φ currentTime₁ msg₁ consis₁ stack₁ nothing (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun<=aux .(ifIgnore ∷ ifStack₂) (ifIgnore ∷ ifStack₂) nonactive φ currentTime₁ msg₁ consis₁ stack₁ (just x₁) (conj and3 refl) = conj and3 refl
lift2StateCorrectnessNonActiveStackFun<=aux .(ifIgnore ∷ ifStack₂) (ifIgnore ∷ ifStack₂) nonactive φ currentTime₁ msg₁ consis₁ stack₁ nothing (conj and3 refl) = conj and3 refl

lift2StateCorrectnessNonActiveStackFun<= : (ifStack₁ : IfStack)
                                  (nonactive : IsNonActiveIfStack ifStack₁)
                                  (φ : StackPredicate)
                                  (stackfun : StackTransformer)
                                  (s : State)
                                  → ((liftStackPred2Pred φ ifStack₁ ) ⁺)
                                                    (stackTransform2StateTransform stackfun s)
                                  → liftStackPred2Pred φ ifStack₁  s

lift2StateCorrectnessNonActiveStackFun<= (ifSkip ∷ ifStack₁) nonactive φ stackfun
          ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₂ , consis₁ ⟩ x
          = lift2StateCorrectnessNonActiveStackFun<=aux (ifSkip ∷ ifStack₁)
              ifStack₂ tt φ  currentTime₁ msg₁ consis₁ stack₁ (stackfun currentTime₁ msg₁ stack₁) x
lift2StateCorrectnessNonActiveStackFun<= (elseSkip ∷ ifStack₁) nonactive φ stackfun
       ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₂ , consis₁ ⟩ x
       = lift2StateCorrectnessNonActiveStackFun<=aux (elseSkip ∷ ifStack₁)
              ifStack₂ tt φ  currentTime₁ msg₁ consis₁ stack₁ (stackfun currentTime₁ msg₁ stack₁) x
lift2StateCorrectnessNonActiveStackFun<= (ifIgnore ∷ ifStack₁) nonactive φ stackfun
       ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₂ , consis₁ ⟩ x
       = lift2StateCorrectnessNonActiveStackFun<=aux (ifIgnore ∷ ifStack₁)
              ifStack₂ tt φ  currentTime₁ msg₁ consis₁ stack₁ (stackfun currentTime₁ msg₁ stack₁) x


lemmaHoareTripleStackPartToHoareTripleNonActiveGeneric
    : (ifStack₁ : IfStack)
      (nonactive : IsNonActiveIfStack ifStack₁)
      (φ : StackPredicate)
      (stackfun : StackTransformer)
      → < liftStackPred2Pred φ ifStack₁ >gen
         stackTransform2StateTransform  stackfun
         < liftStackPred2Pred φ ifStack₁ >
lemmaHoareTripleStackPartToHoareTripleNonActiveGeneric ifStack₁ nonactive φ stackfun .==>g
    = lift2StateCorrectnessNonActiveStackFun=> ifStack₁ nonactive φ stackfun
lemmaHoareTripleStackPartToHoareTripleNonActiveGeneric ifStack₁ nonactive φ stackfun .<==g
    = lift2StateCorrectnessNonActiveStackFun<= ifStack₁ nonactive φ stackfun



lemmaNonActiveIfStackHoareTriple :
     (ifStack₁ : IfStack)
     (nonactive : IsNonActiveIfStack ifStack₁)
     (instr : InstructionAll)
     (nonIf : NonIfInstr instr)
     (φ : StackPredicate)
     → < liftStackPred2Pred φ ifStack₁  >ⁱᶠᶠ instr ∷ []  < liftStackPred2Pred φ ifStack₁  >
lemmaNonActiveIfStackHoareTriple ifStack₁ nonactive instr nonIf φ
   = lemmaGenericHoareTripleImpliesHoareTriple instr
       (liftStackPred2Pred φ ifStack₁ )
       (liftStackPred2Pred φ ifStack₁ )
      ( (lemmaNonIfInstrGenericCondImpliesTripleaux instr nonIf
        (liftStackPred2Pred φ ifStack₁ )
        (liftStackPred2Pred φ ifStack₁ )
        (lemmaHoareTripleStackPartToHoareTripleNonActiveGeneric ifStack₁ nonactive φ
         ⟦ instr ⟧stacks)))








correctStepWithNonActiveIfStack :
          (φ : StackPredicate)
          (pubKey : ℕ)(ifStack₁ : IfStack)(nonactive : IsNonActiveIfStack ifStack₁)
          (n : ℕ)(p : n ≤ 5)
           → < liftStackPred2Pred φ ifStack₁    >ⁱᶠᶠ
                                instructions pubKey n p ∷ []
             < liftStackPred2Pred φ ifStack₁  >
correctStepWithNonActiveIfStack φ pubKey ifStack₁ nonactive n p  =
    lemmaNonActiveIfStackHoareTriple ifStack₁ nonactive (instructions pubKey n p) (p2pkhInstrIsNonIf pubKey n p) φ





correctSeqWithNonActiveIfStack  :
  (φ : StackPredicate)(pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (nonactive : IsNonActiveIfStack ifStack₁)(n : ℕ) (p : n ≤ 6)
  →   < liftStackPred2Pred φ ifStack₁    >ⁱᶠᶠ
           (script' pubKeyHash n p)
       < liftStackPred2Pred φ ifStack₁  >
correctSeqWithNonActiveIfStack φ pubKeyHash ifStack₁ nonactive 0 p
   = lemmaHoare[]
correctSeqWithNonActiveIfStack φ pubKeyHash ifStack₁ nonactive (suc n) p
  = liftStackPred2Pred φ ifStack₁
           <><>⟨ instructions pubKeyHash n p ∷ [] ⟩⟨ correctStepWithNonActiveIfStack φ pubKeyHash ifStack₁ nonactive n p  ⟩
    liftStackPred2Pred φ ifStack₁
           <><>⟨ script' pubKeyHash n (leqSucLemma n 5 p) ⟩⟨ correctSeqWithNonActiveIfStack φ pubKeyHash ifStack₁ nonactive n (leqSucLemma n 5 p)   ⟩ᵉ
   liftStackPred2Pred φ ifStack₁
     ∎p


lemmaP2PKHwithNonActiveIfStack :
   (φ : StackPredicate)(pubKeyHash : ℕ)(ifStack₁ : IfStack)
  (nonactive : IsNonActiveIfStack ifStack₁)
  → <  liftStackPred2Pred φ ifStack₁    >ⁱᶠᶠ
        scriptP2PKH pubKeyHash
    <  liftStackPred2Pred φ ifStack₁    >
lemmaP2PKHwithNonActiveIfStack φ pubKeyHash ifStack₁ nonactive
   = correctSeqWithNonActiveIfStack  φ pubKeyHash ifStack₁ nonactive 6 tt

