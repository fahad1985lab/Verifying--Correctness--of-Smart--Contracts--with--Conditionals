open import basicBitcoinDataType

module verificationBitcoinScripts.hoareTriple (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality



open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib
open import libraries.emptyLib
open import libraries.equalityLib

open import stack
open import instruction
open import verificationBitcoinScripts.ifStack
open import verificationBitcoinScripts.state
open import verificationBitcoinScripts.predicate
open import verificationBitcoinScripts.semanticsInstructions param







_<_>_  : BPredicate →  BitcoinScript →  BPredicate →  Set
ϕ < P > ψ = (s : State) → True (ϕ s) → True( (ψ ⁺ᵇ) ( ⟦ P ⟧ s))


record <_>ⁱᶠᶠ_<_>  (P : Predicate)(p : BitcoinScript)(Q : Predicate) : Set where
  constructor hoare3
  field
    ==> : (s : State) → P s → (Q ⁺) (⟦ p ⟧ s )
    <== : (s : State) → (Q ⁺) (⟦ p ⟧ s ) → P s

open <_>ⁱᶠᶠ_<_>  public


record _<=>ᵖ_ (φ ψ : Predicate) : Set where
  constructor equivp
  field
    ==>e  : (s : State) → φ s → ψ s
    <==e  : (s : State) → ψ s →  φ s
open _<=>ᵖ_ public


refl<=>  :   (φ : Predicate)
            →  φ <=>ᵖ φ
refl<=> φ  .==>e s x  =  x
refl<=> φ  .<==e s x = x


sym<=>  :   (φ ψ : Predicate)
            →  φ <=>ᵖ ψ
            →  ψ <=>ᵖ φ
sym<=> φ ψ (equivp ==>e₁ <==e₁) .==>e  = <==e₁
sym<=> φ ψ (equivp ==>e₁ <==e₁) .<==e  = ==>e₁


