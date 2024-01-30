open import basicBitcoinDataType

module verificationWithIfStack.verificationP2PKHwithIfStack (param : GlobalParameters) where

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
open import instruction
-- open import ledger param
open import semanticBasicOperations param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param

open import verificationP2PKHbasic param

open import verificationWithIfStack.verificationP2PKH param
-- open import verificationWithIfStack.hoareTriple param


{-

In this section all we do is lift those lemma so that they work as well
with an additional ifstack. This happens if we embed this script into an if then else statement.
-}

acceptWithIfStack-0 : IfStack → Predicate
acceptWithIfStack-0 ifStack₁ = liftStackPred2Pred accept-0Basic ifStack₁


acceptWithIfStack-1 : IfStack → Predicate
acceptWithIfStack-1  ifStack₁ = liftStackPred2Pred accept₁ˢ ifStack₁


acceptWithIfStack-2 : IfStack → Predicate
acceptWithIfStack-2 ifStack₁ = liftStackPred2Pred accept₂ˢ ifStack₁

acceptWithIfStack-3 : IfStack → Predicate
acceptWithIfStack-3 ifStack₁ = liftStackPred2Pred accept₃ˢ ifStack₁

acceptWithIfStack-4 : ℕ → IfStack → Predicate
acceptWithIfStack-4 pubKey  ifStack₁ = liftStackPred2Pred (accept₄ˢ pubKey) ifStack₁

acceptWithIfStack-5 : ℕ → IfStack → Predicate
acceptWithIfStack-5 pubKey  ifStack₁ = liftStackPred2Pred (accept₅ˢ pubKey) ifStack₁

acceptWithIfStack-6 : ℕ → IfStack → Predicate
acceptWithIfStack-6 pubKeyHash  ifStack₁ = liftStackPred2Pred (wPreCondP2PKHˢ pubKeyHash) ifStack₁



correctWithIfStack-1-to : (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → acceptWithIfStack-1 ifStack₁ s
                          → ((acceptWithIfStack-0 ifStack₁) ⁺) (⟦ opCheckSig ⟧s s )
correctWithIfStack-1-to [] active ⟨ time , msg₁ , pubKey ∷ sig ∷ st , .[] , c ⟩ (conj and3 refl)
                   = conj (boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) and3) refl
correctWithIfStack-1-to (ifCase ∷ ifStack₁) active
                         ⟨ time , msg₁ , pubKey ∷ sig ∷ st , .(ifCase ∷ ifStack₁) , c ⟩ (conj and3 refl)
                   = conj (boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) and3) refl
correctWithIfStack-1-to (elseCase ∷ ifStack₁) active
                         ⟨ time , msg₁ , pubKey ∷ sig ∷ st , .(elseCase ∷ ifStack₁) , c ⟩
                        (conj and3 refl)
                   = conj (boolToNatNotFalseLemma (isSigned  msg₁ sig pubKey) and3) refl



correctWithIfStack-1-from : (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                            (s : State)
                            → ((acceptWithIfStack-0 ifStack₁) ⁺) (⟦ opCheckSig ⟧s s )
                            → acceptWithIfStack-1 ifStack₁ s
correctWithIfStack-1-from ifStack₁ active ⟨ time , msg₁ , [] , ifCase ∷ ifst , c ⟩ ()
correctWithIfStack-1-from ifStack₁ active ⟨ time , msg₁ , [] , elseCase ∷ ifst , c ⟩ ()
correctWithIfStack-1-from ifStack₁ active ⟨ time , msg₁ , [] , ifSkip ∷ ifst , c ⟩ ()
correctWithIfStack-1-from ifStack₁ active ⟨ time , msg₁ , [] , elseSkip ∷ ifst , c ⟩ ()
correctWithIfStack-1-from ifStack₁ active ⟨ time , msg₁ , [] , ifIgnore ∷ ifst , c ⟩ ()
correctWithIfStack-1-from .(ifSkip ∷ ifst) () ⟨ time , msg₁ , x ∷ [] , ifSkip ∷ ifst , c ⟩ (conj and3 refl)
correctWithIfStack-1-from .(elseSkip ∷ ifst) () ⟨ time , msg₁ , x ∷ [] , elseSkip ∷ ifst , c ⟩ (conj and3 refl)
correctWithIfStack-1-from .(ifIgnore ∷ ifst) () ⟨ time , msg₁ , x ∷ [] , ifIgnore ∷ ifst , c ⟩ (conj and3 refl)
correctWithIfStack-1-from .[] tt ⟨ time , msg₁ , pubKey ∷ sig ∷ l , [] , c ⟩ (conj and3 refl) = conj (boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) and3) refl
correctWithIfStack-1-from .(ifCase ∷ ifst) active ⟨ time , msg₁ , pubKey ∷ sig ∷ l , ifCase ∷ ifst , c ⟩ (conj and3 refl) = conj (boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) and3) refl
correctWithIfStack-1-from .(elseCase ∷ ifst) active ⟨ time , msg₁ , pubKey ∷ sig ∷ l , elseCase ∷ ifst , c ⟩ (conj and3 refl) = conj (boolToNatNotFalseLemma2 (isSigned  msg₁ sig pubKey) and3) refl
correctWithIfStack-1-from .(ifSkip ∷ ifst) () ⟨ time , msg₁ , x ∷ x₁ ∷ l , ifSkip ∷ ifst , c ⟩ (conj and3 refl)
correctWithIfStack-1-from .(elseSkip ∷ ifst) () ⟨ time , msg₁ , x ∷ x₁ ∷ l , elseSkip ∷ ifst , c ⟩ (conj and3 refl)
correctWithIfStack-1-from .(ifIgnore ∷ ifst) () ⟨ time , msg₁ , x ∷ x₁ ∷ l , ifIgnore ∷ ifst , c ⟩ (conj and3 refl)


correctWithIfStack-2-to : (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → acceptWithIfStack-2 ifStack₁ s
                          → ((acceptWithIfStack-1 ifStack₁) ⁺) (⟦ opVerify ⟧s s )
correctWithIfStack-2-to [] active ⟨ currentTime₁ , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ , .[] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-2-to (ifCase ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ , .(ifCase ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-2-to (elseCase ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ , .(elseCase ∷ ifStack₁) , consis₁ ⟩ (conj and3 refl) = conj and3 refl



correctWithIfStack-2-from : (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → ((acceptWithIfStack-1 ifStack₁) ⁺) (⟦ opVerify ⟧s s )
                          → acceptWithIfStack-2 ifStack₁ s
correctWithIfStack-2-from .[] active ⟨ currentTime₁ , msg₁ , suc x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-2-from (x₃ ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , zero ∷ x₂ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) =  conj active refl
correctWithIfStack-2-from (x₃ ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , zero ∷ x₂ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from (x₃ ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , zero ∷ x₂ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from (x₃ ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from (x₃ ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from (x₃ ∷ ifStack₁) active ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from ifStack₁ active ⟨ currentTime₁ , msg₁ , zero ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from ifStack₁ active ⟨ currentTime₁ , msg₁ , zero ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from ifStack₁ active ⟨ currentTime₁ , msg₁ , zero ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj active refl
correctWithIfStack-2-from ifStack₁ active ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-2-from ifStack₁ active ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-2-from (.ifSkip ∷ ifStack₁) () ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ .ifStack₁ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-2-from .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-2-from .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , suc x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)

correctWithIfStack-3-to : (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State) → acceptWithIfStack-3 ifStack₁ s
                          → ((acceptWithIfStack-2 ifStack₁) ⁺) (⟦ opEqual ⟧s s )
correctWithIfStack-3-to [] active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , [] , consis₁ ⟩(conj (conj refl and4) refl)  rewrite (lemmaCompareNat x)
                        = conj and4 refl
correctWithIfStack-3-to .(ifCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x₁ ∷ .x₁ ∷ x₃ ∷ x₄ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj (conj refl and5) refl)  rewrite (lemmaCompareNat x₁)
                        = conj and5 refl
correctWithIfStack-3-to .(elseCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x₁ ∷ .x₁ ∷ x₃ ∷ x₄ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj (conj refl and5) refl)  rewrite (lemmaCompareNat x₁)
                        = conj and5 refl
correctWithIfStack-3-to .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-to .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-to .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)


correctWithIfStack-3-from : (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → ((acceptWithIfStack-2 ifStack₁) ⁺ ) (⟦ opEqual ⟧s s )
                          → acceptWithIfStack-3 ifStack₁ s
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ pbk ∷ sig ∷ stack₁ , [] , consis₁ ⟩
             (conj and3 refl) rewrite ( lemmaCorrect3From x x₁ pbk sig currentTime₁ msg₁ and3 )  =   let
                                                                                                   q : True (isSigned  msg₁ sig pbk)
                                                                                                   q = correct3Aux2 (compareNaturals x x₁) pbk sig stack₁ currentTime₁ msg₁ and3

                                                                                                   in conj (conj refl q) refl

correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-3-from .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-from .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-from .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-from .(ifCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ pbk ∷ sig ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩
                (conj and3 refl) rewrite ( lemmaCorrect3From x₁ x₂ pbk sig currentTime₁ msg₁ and3 )  =   let
                                                                                                       q : True (isSigned  msg₁ sig pbk)
                                                                                                       q = correct3Aux2 (compareNaturals x₁ x₂) pbk sig stack₁ currentTime₁ msg₁ and3

                                                                                                       in conj (conj refl q) refl

correctWithIfStack-3-from .(elseCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ pbk ∷ sig ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩
                (conj and3 refl) rewrite ( lemmaCorrect3From x₁ x₂ pbk sig currentTime₁ msg₁ and3 )  =   let
                                                                                                       q : True (isSigned  msg₁ sig pbk)
                                                                                                       q = correct3Aux2 (compareNaturals x₁ x₂) pbk sig stack₁ currentTime₁ msg₁ and3

                                                                                                       in conj (conj refl q) refl

correctWithIfStack-3-from .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ pbk ∷ sig ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-from .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ pbk ∷ sig ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-3-from .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ pbk ∷ sig ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)


correctWithIfStack-4-to : (pubKey : ℕ)
                          (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State) → acceptWithIfStack-4 pubKey ifStack₁ s
                          → ((acceptWithIfStack-3 ifStack₁) ⁺) (⟦ opPush pubKey ⟧s s )
correctWithIfStack-4-to pubKey .[] active ⟨ currentTime₁ , msg₁ , .pubKey ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj (conj refl and4) refl) = conj (conj refl and4) refl
correctWithIfStack-4-to pubKey .(ifCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj (conj refl and4) refl) = conj (conj refl and4) refl
correctWithIfStack-4-to pubKey .(elseCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj (conj refl and4) refl) = conj (conj refl and4) refl
correctWithIfStack-4-to pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-4-to pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-4-to pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)


correctWithIfStack-4-from : (pubKey : ℕ)
                          (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → ((acceptWithIfStack-3 ifStack₁) ⁺) (⟦ opPush pubKey ⟧s s )
                          → acceptWithIfStack-4 pubKey ifStack₁ s
correctWithIfStack-4-from pubKey .[] active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj (conj refl and4) refl) = conj (conj refl and4) refl
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-4-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj (conj refl and4) refl) = conj (conj refl and4) refl
correctWithIfStack-4-from pubKey .(elseCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj (conj refl and4) refl) = conj (conj refl and4) refl
correctWithIfStack-4-from pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-4-from pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-4-from pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)



correctWithIfStack-5-to : (pubKey : ℕ)
                          (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → acceptWithIfStack-5 pubKey ifStack₁ s
                          → ((acceptWithIfStack-4 pubKey ifStack₁) ⁺) (⟦ opHash ⟧s s )
correctWithIfStack-5-to pubKey .[] active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-5-to pubKey .(ifCase ∷ ifStack₂) active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) =  conj and3 refl
correctWithIfStack-5-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-5-to pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-5-to pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-5-to pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)


correctWithIfStack-5-from : (pubKey : ℕ)
                          (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → ((acceptWithIfStack-4 pubKey ifStack₁) ⁺) (⟦ opHash ⟧s s )
                          → acceptWithIfStack-5 pubKey ifStack₁ s
correctWithIfStack-5-from pubKey .[] active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-5-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-5-from pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-5-from pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-5-from pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)



correctWithIfStack-6-to : (pubKey : ℕ)
                          (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → acceptWithIfStack-6 pubKey ifStack₁ s
                          → ((acceptWithIfStack-5 pubKey ifStack₁) ⁺) (⟦ opDup ⟧s s )
correctWithIfStack-6-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ [] , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-to pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-to pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-to pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-to pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-to pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-to pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-to pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)


correctWithIfStack-6-from : (pubKey : ℕ)
                          (ifStack₁ : IfStack)(active : IsActiveIfStack ifStack₁)
                          (s : State)
                          → ((acceptWithIfStack-5 pubKey ifStack₁) ⁺) (⟦ opDup ⟧s s )
                          → acceptWithIfStack-6 pubKey ifStack₁ s
correctWithIfStack-6-from pubKey .[] active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ [] , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x ∷ x₁ ∷ x₂ ∷ stack₁ , [] , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , elseSkip ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ [] , ifIgnore ∷ ifStack₂ , consis₁ ⟩ ()
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ [] , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-from pubKey ifStack₁ active ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseCase ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl) = conj and3 refl
correctWithIfStack-6-from pubKey .(ifSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-from pubKey .(elseSkip ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , elseSkip ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)
correctWithIfStack-6-from pubKey .(ifIgnore ∷ ifStack₂) () ⟨ currentTime₁ , msg₁ , x₁ ∷ x₂ ∷ x₃ ∷ stack₁ , ifIgnore ∷ ifStack₂ , consis₁ ⟩ (conj and3 refl)


