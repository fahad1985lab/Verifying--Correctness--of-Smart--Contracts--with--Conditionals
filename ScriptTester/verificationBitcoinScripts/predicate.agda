

module verificationBitcoinScripts.predicate where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Sum
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality

open import libraries.andLib


open import basicBitcoinDataType
open import stack
open import stackPredicate

open import verificationBitcoinScripts.ifStack
open import verificationBitcoinScripts.state


BPredicate  : Set
BPredicate =  State →  Bool

Predicate  : Set₁
Predicate =  State →  Set



MaybeBPredicate : Set
MaybeBPredicate = Maybe State →  Bool




ifStackPredicate : IfStack → Predicate
ifStackPredicate ifs ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ = ifStack₁ ≡ ifs


truefalsePred : (φ ψ : StackPredicate) → Predicate
truefalsePred φ ψ ⟨ time , msg , [] , ifStack , c ⟩ = ⊥
truefalsePred φ ψ ⟨ time , msg , zero ∷ stack , ifStack , c ⟩ = φ time msg stack
truefalsePred φ ψ ⟨ time , msg , suc x ∷ stack , ifStack , c ⟩ = ψ time msg stack


_∧p_ : ( φ ψ  : Predicate ) → Predicate
(φ ∧p ψ ) s  =  φ s  ∧  ψ s



infixl 4 _⊎p_

_⊎p_   : (φ ψ : Predicate) → Predicate
(φ ⊎p ψ) s = φ s ⊎ ψ s


liftStackPred2PredIgnoreIfStack : StackPredicate → Predicate
liftStackPred2PredIgnoreIfStack f  ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ = f time msg₁ stack₁


-- predicate expressing top element is not false and φ holds for the
-- stack excluding the top element

truePred : StackPredicate → Predicate
truePred φ = liftStackPred2PredIgnoreIfStack (truePredaux  φ)



-- predicate expressing top element is not false and φ holds for the
-- stack excluding the top element

falsePredaux : StackPredicate → StackPredicate
falsePredaux φ time msg [] = ⊥
falsePredaux φ time msg (zero ∷ st) = φ time msg  st
falsePredaux φ time msg (suc x ∷ st) = ⊥

falsePred : StackPredicate → Predicate
falsePred φ = liftStackPred2PredIgnoreIfStack (falsePredaux  φ)


--lift Stack Predicate to Predicate
--short name is lift
liftStackPred2Pred : StackPredicate →  IfStack → Predicate
liftStackPred2Pred ψ ifStack₁ = liftStackPred2PredIgnoreIfStack ψ ∧p ifStackPredicate  ifStack₁



