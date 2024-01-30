open import basicBitcoinDataType

module verificationWithIfStack.verificationP2PKHindexed (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding   (_≤_ ; _<_ ; if_then_else_ )
                       renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.List.NonEmpty hiding (head )
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite

open import libraries.andLib
open import libraries.maybeLib
open import libraries.boolLib
open import libraries.listLib
open import libraries.natLib

open import stack
open import stackPredicate
open import instruction
-- open import ledger param
open import semanticBasicOperations param
open import verificationP2PKHbasic param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.verificationP2PKH param

instructions : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 5 → InstructionAll
instructions pbkh n p = basicInstr2Instr (instructionsBasic pbkh n p)





script : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 6 → BitcoinScript
script pubKeyHash 0 _ = []
script pubKeyHash (suc n) p
   = instructions pubKeyHash n  p ∷ script pubKeyHash  n (leqSucLemma n 5 p)


script' : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 6 → BitcoinScript
script' pubKeyHash 0 _ = []
script' pubKeyHash (suc n) p
   = (instructions pubKeyHash n  p ∷ [] ) ++ script' pubKeyHash  n (leqSucLemma n 5 p)


conditionBasic : (pubKeyHash : ℕ)  (n : ℕ) → n ≤ 6 → StackPredicate
conditionBasic pubKeyHash 0 _ = acceptStateˢ
conditionBasic pubKeyHash 1 _ = accept₁ˢ
conditionBasic pubKeyHash 2 _ = accept₂ˢ
conditionBasic pubKeyHash 3 _ = accept₃ˢ
conditionBasic pubKeyHash 4 _ = accept₄ˢ pubKeyHash
conditionBasic pubKeyHash 5 _ = accept₅ˢ pubKeyHash
conditionBasic pubKeyHash 6 _ = wPreCondP2PKHˢ pubKeyHash

condition : (pubKeyHash : ℕ)  (n : ℕ) → n ≤ 6 → (s : State) → Set
condition pubKeyHash n p = stackPred2Pred (conditionBasic pubKeyHash n p)


correct-1-to' : (s : State) → accept₁ s
                →  (acceptState ⁺) (⟦ opCheckSig ⟧s s)
correct-1-to' ⟨ time , msg₁ , pubKey  ∷ sig ∷ st , []  , c ⟩ p
     = boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) p


correct-1-from' : (s : State)
                 →  (acceptState ⁺) (⟦ opCheckSig ⟧s s)
                 → accept₁ s
correct-1-from' ⟨ time , msg₁ , pubKey ∷ sig ∷ stack₁ , [] , c ⟩ p
        = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) p
correct-1-from' ⟨ time , msg₁ , x ∷ [] , ifCase ∷ ifStack₁ , c ⟩ p = p
correct-1-from' ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ p = p
correct-1-from' ⟨ time , msg₁ , x ∷ [] , elseCase ∷ ifStack₁ , c ⟩ p = p
correct-1-from' ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ p = p


correctStep-to  : (pubKeyHash : ℕ)  (n : ℕ) (p : n ≤ 5)
  (s : State)
  → condition pubKeyHash (suc n) p s
  → ((condition pubKeyHash n (leqSucLemma n 5 p)) ⁺)
                    (⟦ instructions pubKeyHash n p ⟧s s)
correctStep-to pubKeyHash 0 _ = correct-1-to'
correctStep-to pubKeyHash 1 _ = correct-2-to
correctStep-to pubKeyHash 2 _ = correct-3-to
correctStep-to pubKeyHash 3 _ = correct-4-to pubKeyHash
correctStep-to pubKeyHash 4 _ = correct-5-to pubKeyHash
correctStep-to pubKeyHash 5 _ = correct-6-to pubKeyHash


correctStep-from :  (pubKeyHash : ℕ)  (n : ℕ)(p : n ≤ 5)(s : State)
    → ((condition pubKeyHash n (leqSucLemma n 5 p)) ⁺)
                        (⟦ instructions pubKeyHash n p ⟧s s)
    → condition pubKeyHash (suc n) p s
correctStep-from pubKeyHash 0 _ = correct-1-from'
correctStep-from pubKeyHash 1 _ = correct-2-from
correctStep-from pubKeyHash 2 _ = correct-3-from
correctStep-from pubKeyHash 3 _ = correct-4-from pubKeyHash
correctStep-from pubKeyHash 4 _ = correct-5-from pubKeyHash
correctStep-from pubKeyHash 5 _ = correct-6-from pubKeyHash




correct-from : (pubKeyHash : ℕ) (n : ℕ)  (p : n ≤ 6)(s : State)
               → (acceptState ⁺) ( ⟦ script pubKeyHash n p ⟧ s)
               → condition pubKeyHash n p s
correct-from pubKeyHash 0 p s st
       = emptyProgramCorrect-from (condition pubKeyHash 0 tt) s st
correct-from pubKeyHash (suc n) p s st
       = bindTransformer-fromSingle
         (condition pubKeyHash (suc n) p)
         (condition pubKeyHash n (leqSucLemma n 5 p))
         acceptState
         (instructions pubKeyHash n p)
         (script pubKeyHash n (leqSucLemma n 5 p))
         (correctStep-from pubKeyHash n p)
         (correct-from pubKeyHash n (leqSucLemma n 5 p)) s st

correct-to  : (pubKeyHash : ℕ)  (n : ℕ) (p : n ≤ 6)(s : State)
           → condition pubKeyHash n p s
           → (acceptState ⁺) (⟦ script pubKeyHash n p ⟧ s)
correct-to pubKeyHash 0 p = emptyProgramCorrect-to (condition pubKeyHash 0 tt)
correct-to pubKeyHash (suc n) p = bindTransformer-toSingle (condition pubKeyHash (suc n) p)
     (condition pubKeyHash n (leqSucLemma n 5 p)) acceptState
     (instructions pubKeyHash n p)
     (script pubKeyHash n (leqSucLemma n 5 p))
     (correctStep-to pubKeyHash n p)
     (correct-to pubKeyHash n (leqSucLemma n 5 p))





completeCorrect-1-to : (s : State) → accept₁ s
     →  (acceptState ⁺) (⟦ script-1 ⟧ s)
completeCorrect-1-to ⟨ time , msg₁ , pubKey  ∷ sig ∷ st , []  , c ⟩ p
     = boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) p


completeCorrect-1-from : (s : State)
                         → (acceptState ⁺) (⟦  script-1 ⟧ s )
                         → accept₁ s
completeCorrect-1-from ⟨ time , msg₁ , pubKey ∷ sig ∷ stack₁ , [] , c ⟩ p
         = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) p
completeCorrect-1-from ⟨ time , msg₁ , x ∷ [] , ifCase ∷ ifStack₁ , c ⟩ ()
completeCorrect-1-from ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
completeCorrect-1-from ⟨ time , msg₁ , x ∷ [] , elseCase ∷ ifStack₁ , c ⟩ ()
completeCorrect-1-from ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()


completeCorrect-2-to : (s : State) → accept₂ s
                      →  (acceptState ⁺) (⟦ script-2 ⟧ s)
completeCorrect-2-to  s a
    = bindTransformer-toSingle accept₂ accept₁ acceptState  (basicInstr2Instr instruction-2)
      script-1 correct-2-to completeCorrect-1-to  s a


completeCorrect-2-from : (s : State) →  (acceptState ⁺) (⟦ script-2 ⟧ s) → accept₂ s
completeCorrect-2-from  s a = bindTransformer-fromSingle accept₂ accept₁ acceptState (basicInstr2Instr instruction-2) script-1 correct-2-from completeCorrect-1-from  s a



completeCorrect-3-to : (s : State) → accept₃ s →  (acceptState ⁺) (⟦ script-3 ⟧ s)
completeCorrect-3-to  s a = bindTransformer-toSingle accept₃ accept₂ acceptState (basicInstr2Instr instruction-3) script-2 correct-3-to completeCorrect-2-to s a


completeCorrect-3-from : (s : State) →  (acceptState ⁺) (⟦ script-3 ⟧ s) → accept₃ s
completeCorrect-3-from  s a = bindTransformer-fromSingle accept₃ accept₂ acceptState (basicInstr2Instr instruction-3) script-2 correct-3-from completeCorrect-2-from  s a


completeCorrect-4-to : (pubKeyHash : ℕ )(s : State) → accept₄ pubKeyHash s  →  (acceptState ⁺) (⟦ script-4 pubKeyHash ⟧ s)
completeCorrect-4-to pubKeyHash s a  = bindTransformer-toSingle (accept₄ pubKeyHash) accept₃ acceptState (basicInstr2Instr (instruction-4 pubKeyHash)) script-3 (correct-4-to pubKeyHash) completeCorrect-3-to s a



completeCorrect-4-from :(pubKeyHash : ℕ )(s : State) →  (acceptState ⁺) (⟦ script-4 pubKeyHash ⟧ s) → accept₄ pubKeyHash s
completeCorrect-4-from pubKeyHash s a = bindTransformer-fromSingle (accept₄ pubKeyHash) accept₃ acceptState (basicInstr2Instr (instruction-4 pubKeyHash)) script-3 (correct-4-from pubKeyHash) completeCorrect-3-from s a


completeCorrect-5-to : (pubKeyHash : ℕ )(s : State) → accept₅ pubKeyHash s  →  (acceptState ⁺) (⟦ script-5 pubKeyHash ⟧ s)
completeCorrect-5-to pubKeyHash s a  = bindTransformer-toSingle (accept₅ pubKeyHash) (accept₄ pubKeyHash) acceptState (basicInstr2Instr instruction-5) (script-4 pubKeyHash) (correct-5-to pubKeyHash) (completeCorrect-4-to pubKeyHash) s  a



completeCorrect-5-from :(pubKeyHash : ℕ )(s : State) →  (acceptState ⁺) (⟦ script-5 pubKeyHash ⟧ s) → accept₅ pubKeyHash s
completeCorrect-5-from pubKeyHash s a = bindTransformer-fromSingle (accept₅ pubKeyHash) (accept₄ pubKeyHash) acceptState (basicInstr2Instr instruction-5) (script-4 pubKeyHash) (correct-5-from pubKeyHash) (completeCorrect-4-from  pubKeyHash) s a



completecorrect-6-to : (pubKeyHash : ℕ ) → (s : State) → accept-6 pubKeyHash s →  (acceptState ⁺) (⟦ script-6 pubKeyHash ⟧ s )
completecorrect-6-to pubKeyHash s a = bindTransformer-toSingle (accept-6 pubKeyHash) (accept₅ pubKeyHash) acceptState (basicInstr2Instr instruction-6) (script-5 pubKeyHash) (correct-6-to pubKeyHash) (completeCorrect-5-to pubKeyHash) s a




completeCorrect-6-from :(pubKeyHash : ℕ )(s : State) →  (acceptState ⁺) (⟦ script-6 pubKeyHash ⟧ s) → accept-6 pubKeyHash s
completeCorrect-6-from pubKeyHash s a = bindTransformer-fromSingle (accept-6 pubKeyHash) (accept₅ pubKeyHash) acceptState (basicInstr2Instr instruction-6) (script-5 pubKeyHash) (correct-6-from pubKeyHash) (completeCorrect-5-from  pubKeyHash) s a


instructionSequence : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 5 → BitcoinScript
instructionSequence pubKeyHash n p = instructions pubKeyHash n p ∷ []

scriptSequence : (pubKeyHash : ℕ) (n : ℕ) → n ≤ 6 → BitcoinScript
scriptSequence pubKeyHash 0 _ = []
scriptSequence pubKeyHash (suc n) p = instructionSequence pubKeyHash n  p ++ scriptSequence pubKeyHash  n (leqSucLemma n 5 p)





correctStep-toSequence'  : (pubKeyHash : ℕ)  (n : ℕ) → (p : n ≤ 5)
               (s : State) → condition pubKeyHash (suc n) p s
                            → ((condition pubKeyHash n (leqSucLemma n 5 p)) ⁺)
                                              (⟦ instructionSequence pubKeyHash n p ⟧ s)
correctStep-toSequence' pubKeyHash 0 _  = liftCondOperation2Program-to (condition pubKeyHash 1 tt)
                                              (condition pubKeyHash 0 tt) (instructions pubKeyHash 0 tt)
                                              correct-1-to'
correctStep-toSequence' pubKeyHash 1 _ = liftCondOperation2Program-to (condition pubKeyHash 2 tt)
                                              (condition pubKeyHash 1 tt) (instructions pubKeyHash 1 tt)
                                              correct-2-to
correctStep-toSequence' pubKeyHash 2 _ = liftCondOperation2Program-to (condition pubKeyHash 3 tt)
                                              (condition pubKeyHash 2 tt) (instructions pubKeyHash 2 tt)
                                              correct-3-to
correctStep-toSequence' pubKeyHash 3 _ = liftCondOperation2Program-to (condition pubKeyHash 4 tt)
                                              (condition pubKeyHash 3 tt) (instructions pubKeyHash 3 tt)
                                              (correct-4-to pubKeyHash)
correctStep-toSequence' pubKeyHash 4 _ = liftCondOperation2Program-to (condition pubKeyHash 5 tt)
                                              (condition pubKeyHash 4 tt) (instructions pubKeyHash 4 tt)
                                              (correct-5-to pubKeyHash)
correctStep-toSequence' pubKeyHash 5 _ = liftCondOperation2Program-to (condition pubKeyHash 6 tt)
                                              (condition pubKeyHash 5 tt) (instructions pubKeyHash 5 tt)
                                              (correct-6-to pubKeyHash)


correctStep-FromSequence'  : (pubKeyHash : ℕ)  (n : ℕ) → (p : n ≤ 5)
                        (s : State) → ((condition pubKeyHash n (leqSucLemma n 5 p)) ⁺) (⟦ instructionSequence pubKeyHash n p ⟧ s)
                                  → condition pubKeyHash (suc n) p s

correctStep-FromSequence' pubKeyHash 0 _ = liftCondOperation2Program-from (condition pubKeyHash 1 tt)
                                              (condition pubKeyHash 0 tt) (instructions pubKeyHash 0 tt)
                                               correct-1-from'
correctStep-FromSequence' pubKeyHash 1 _ = liftCondOperation2Program-from (condition pubKeyHash 2 tt) (condition pubKeyHash 1 tt) (instructions pubKeyHash 1 tt)
                                           correct-2-from
correctStep-FromSequence' pubKeyHash 2 _ = liftCondOperation2Program-from (condition pubKeyHash 3 tt) (condition pubKeyHash 2 tt) (instructions pubKeyHash 2 tt)
                                               correct-3-from
correctStep-FromSequence' pubKeyHash 3 _ = liftCondOperation2Program-from (condition pubKeyHash 4 tt)(condition pubKeyHash 3 tt) (instructions pubKeyHash 3 tt)
                                               (correct-4-from pubKeyHash)
correctStep-FromSequence' pubKeyHash 4 _ = liftCondOperation2Program-from (condition pubKeyHash 5 tt)(condition pubKeyHash 4 tt) (instructions pubKeyHash 4 tt)
                                               (correct-5-from  pubKeyHash)
correctStep-FromSequence' pubKeyHash 5 _ = liftCondOperation2Program-from (condition pubKeyHash 6 tt)(condition pubKeyHash 5 tt) (instructions pubKeyHash 5 tt)
                                               (correct-6-from pubKeyHash)


correct-toSequence  : (pubKeyHash : ℕ)  (n : ℕ) (p : n ≤ 6)(s : State)
           → condition pubKeyHash n p s
           → (acceptState ⁺) (⟦ scriptSequence pubKeyHash n p ⟧ s)
correct-toSequence pubKeyHash 0 p = emptyProgramCorrect-to (condition pubKeyHash 0 tt)
correct-toSequence pubKeyHash (suc n) p = bindTransformer-toSequence ( (condition pubKeyHash (suc n) p))
                                                       ( (condition pubKeyHash n (leqSucLemma n 5 p)))  acceptState
                                                       ((instructionSequence pubKeyHash n p)) (scriptSequence  pubKeyHash n (leqSucLemma n 5 p))
                                                       (correctStep-toSequence' pubKeyHash n p)
                                                       (correct-toSequence pubKeyHash n (leqSucLemma n 5 p))



correct-fromSequence  : (pubKeyHash : ℕ)  (n : ℕ) (p : n ≤ 6)(s : State)
             → (acceptState ⁺) (⟦ scriptSequence pubKeyHash n p ⟧ s)
            → condition pubKeyHash n p s
correct-fromSequence pubKeyHash zero p s st =  emptyProgramCorrect-from (condition pubKeyHash 0 tt) s st
correct-fromSequence pubKeyHash (suc n) p s st =
 bindTransformer-fromSequence (condition pubKeyHash (suc n) p)
 (condition pubKeyHash n (leqSucLemma n 5 p)) acceptState (instructionSequence pubKeyHash n p)
 (scriptSequence pubKeyHash n (leqSucLemma n 5 p)) (correctStep-FromSequence' pubKeyHash n p)
 (correct-fromSequence pubKeyHash n (leqSucLemma n 5 p)) s st



weakestPreConditionP2PKH : (pubKeyHash : ℕ) (s : State) → Set
weakestPreConditionP2PKH pubKeyHash = stackPred2Pred (wPreCondP2PKHˢ pubKeyHash)

correctComplete-from : (pubKeyHash : ℕ)(s : State)
         → (acceptState ⁺) (⟦ script-6 pubKeyHash ⟧ s)
         → weakestPreConditionP2PKH pubKeyHash s
correctComplete-from pubKeyHash = correct-from pubKeyHash 6 tt

correctComplete-to : (pubKeyHash : ℕ)(s : State) → weakestPreConditionP2PKH pubKeyHash s
                  → (acceptState ⁺) (⟦ script-6 pubKeyHash ⟧ s)
correctComplete-to pubKeyHash = correct-to pubKeyHash 6 tt

correctnessP2PKH : (pubKeyHash : ℕ)
                   → < weakestPreConditionP2PKH pubKeyHash >ⁱᶠᶠ
                      scriptP2PKH pubKeyHash
                     < acceptState  >
correctnessP2PKH pubKeyHash .==> = correctComplete-to   pubKeyHash
correctnessP2PKH pubKeyHash .<== = correctComplete-from pubKeyHash
