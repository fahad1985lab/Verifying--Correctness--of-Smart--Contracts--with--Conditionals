open import basicBitcoinDataType

module verificationWithIfStack.verificationP2PKH (param : GlobalParameters) where

open import libraries.listLib
open import Data.List.Base
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
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

open import stack
open import stackPredicate
open import instruction
-- open import ledger param
open import semanticBasicOperations param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
-- open import verificationWithIfStack.verificationLemmas param
-- open import verificationWithIfStack.hoareTriple param
open import verificationP2PKHbasic param



-- note accept_0 is the same as acceptState
accept-0 : Predicate
accept-0 = stackPred2Pred accept-0Basic


accept₁ : Predicate
accept₁  = stackPred2Pred accept₁ˢ

accept₂ : Predicate
accept₂ = stackPred2Pred accept₂ˢ

accept₃ : Predicate
accept₃ = stackPred2Pred accept₃ˢ

accept₄ : ℕ → Predicate
accept₄ pubKey  = stackPred2Pred (accept₄ˢ pubKey)

accept₅ : ℕ → Predicate
accept₅ pubKey  = stackPred2Pred (accept₅ˢ pubKey)

accept-6 : ℕ → Predicate
accept-6 pubKeyHash  = stackPred2Pred (wPreCondP2PKHˢ pubKeyHash)



-- the following is the same as
-- correct-1-to : (s : State) → accept₁ s → AcceptingMaybeState (⟦ opCheckSig ⟧s s )
correct-1-to : (s : State) → accept₁ s → (accept-0 ⁺) (⟦ opCheckSig ⟧s s )
correct-1-to ⟨ time , msg₁ , pubKey  ∷ sig ∷ st , []  , c ⟩ p =  boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) p


-- the following is the same as
-- correct-1-from : (s : State) → AcceptingMaybeState (⟦ opCheckSig ⟧s s ) → accept₁ s
correct-1-from : (s : State) → (accept-0 ⁺) (⟦ opCheckSig ⟧s s ) → accept₁ s
correct-1-from ⟨ time , msg₁ , pubKey ∷ sig ∷ stack₁ , [] , c ⟩ p = boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) p
correct-1-from ⟨ time , msg₁ , x ∷ [] , ifCase ∷ ifStack₁ , c ⟩ ()
correct-1-from ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
correct-1-from ⟨ time , msg₁ , x ∷ [] , elseCase ∷ ifStack₁ , c ⟩ ()
correct-1-from ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()



correct-2-to : (s : State) → accept₂ s → (accept₁ ⁺) (⟦ opVerify ⟧s s )
correct-2-to ⟨ time , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , c ⟩ p = p

correct-2-from : (s : State) → (accept₁ ⁺) (⟦ opVerify ⟧s s ) → accept₂ s
correct-2-from ⟨ time , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , c ⟩ p = p
correct-2-from ⟨ time , msg₁ , zero ∷ stack₁ , ifCase ∷ s , c ⟩ ()
correct-2-from ⟨ time , msg₁ , suc x ∷ stack₁ , ifCase ∷ s , c ⟩ ()
correct-2-from ⟨ time , msg₁ , zero ∷ stack₁ , elseCase ∷ s , c ⟩ ()
correct-2-from ⟨ time , msg₁ , suc x ∷ stack₁ , elseCase ∷ s , c ⟩ ()


correct-3-to : (s : State) → accept₃ s → (accept₂ ⁺) (⟦ opEqual ⟧s s )
correct-3-to ⟨ time , msg₁ , pubKey1  ∷ .pubKey1 ∷ pubKey2 ∷ sig ∷ [] , [] , c ⟩ (conj refl checkSig)  rewrite ( lemmaCompareNat pubKey1 ) =  checkSig
correct-3-to ⟨ time , msg₁ , pubKey1 ∷ .pubKey1 ∷ pubKey2  ∷ sig ∷ x ∷ rest , [] , c ⟩ (conj refl checkSig) rewrite  ( lemmaCompareNat pubKey1 ) = checkSig

correct-3-from  : (s : State)  → (accept₂ ⁺) (⟦ opEqual ⟧s s ) → accept₃ s
correct-3-from ⟨ time , msg₁ , x ∷ x₁ ∷ pbk ∷ sig ∷ stack₁ , [] , c ⟩ p rewrite ( lemmaCorrect3From x x₁ pbk sig time msg₁ p )
  =   let
        q : True (isSigned  msg₁ sig pbk) -- True (isSigned  msg₁ x₂ x₃)
        q = correct3Aux2 (compareNaturals x x₁) pbk sig stack₁ time msg₁ p
      in (conj refl q)

correct-3-from ⟨ time , msg₁ , x ∷ [] , ifCase ∷ ifStack₁ , c ⟩ ()
correct-3-from ⟨ time , msg₁ , x ∷ x₁ ∷ [] , ifCase ∷ ifStack₁ , c ⟩ ()
correct-3-from ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ ()
correct-3-from ⟨ time , msg₁ , x ∷ [] , elseCase ∷ ifStack₁ , c ⟩ ()
correct-3-from ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ ()



correct-4-to : ( pubKey : ℕ ) →  (s : State) → accept₄ pubKey  s → (accept₃ ⁺) (⟦ opPush pubKey ⟧s s )
correct-4-to pubKey ⟨ currentTime₁ , msg₁ , .pubKey ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj refl and4) = conj refl and4

correct-4-from : ( pubKey : ℕ ) →  (s : State) → (accept₃ ⁺) (⟦ opPush pubKey ⟧s s ) → accept₄ pubKey  s
correct-4-from pubKey ⟨ currentTime₁ , msg₁ , .pubKey ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj refl and4) = conj refl and4
correct-4-from pubKey ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ ifStack₁ , consis₁ ⟩ ()
correct-4-from pubKey ⟨ currentTime₁ , msg₁ , stack₁ , elseCase ∷ ifStack₁ , consis₁ ⟩ ()
correct-4-from pubKey ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , consis₁ ⟩ ()
correct-4-from pubKey ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , consis₁ ⟩ ()
correct-4-from pubKey ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , consis₁ ⟩ ()

correct-5-to : (pubKey : ℕ ) → (s : State) → accept₅ pubKey s →  ((accept₄ pubKey ) ⁺) (⟦ opHash ⟧s s )
correct-5-to pubKey ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , c ⟩ (conj refl checkSig) = (conj refl checkSig)

correct-5-from : ( pubKey : ℕ ) →  (s : State)  → ((accept₄ pubKey) ⁺) (⟦ opHash ⟧s s ) → accept₅ pubKey  s
correct-5-from .(hashFun x) ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , c ⟩ (conj refl checkSig) = conj refl checkSig
correct-5-from pubKey ⟨ time , msg₁ , [] , ifCase ∷ ifStack₁ , c ⟩ ()
correct-5-from pubKey ⟨ time , msg₁ , x ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ p = p
correct-5-from pubKey ⟨ time , msg₁ , [] , elseCase ∷ ifStack₁ , c ⟩ p = p
correct-5-from pubKey ⟨ time , msg₁ , x ∷ stack₁ , elseCase ∷ ifStack₁ , c ⟩ p = p





correct-6-to : (pubKeyHash : ℕ ) → (s : State) → accept-6 pubKeyHash s →  ((accept₅ pubKeyHash ) ⁺)  (⟦ opDup ⟧s s )
correct-6-to pubKeyHash ⟨ time , msg₁ , x ∷ x₁ ∷ [] , [] , c ⟩ p = p
correct-6-to pubKeyHash ⟨ time , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , c ⟩ p = p

correct-6-from : ( pubKeyHash : ℕ ) →  (s : State)  → ((accept₅ pubKeyHash) ⁺) (⟦ opDup ⟧s s ) → accept-6 pubKeyHash  s
correct-6-from pubKeyHash ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , [] , c ⟩ p = p
correct-6-from pubKeyHash ⟨ time , msg₁ , [] , ifCase ∷ ifStack₁ , c ⟩ p = p
correct-6-from pubKeyHash ⟨ time , msg₁ , x ∷ [] , ifCase ∷ ifStack₁ , c ⟩ p = p
correct-6-from pubKeyHash ⟨ time , msg₁ , x ∷ x₁ ∷ stack₁ , ifCase ∷ ifStack₁ , c ⟩ p = p
