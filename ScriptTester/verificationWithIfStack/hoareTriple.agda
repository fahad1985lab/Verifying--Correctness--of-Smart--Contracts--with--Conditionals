open import basicBitcoinDataType

module verificationWithIfStack.hoareTriple (param : GlobalParameters) where

open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Maybe
open import Data.Unit  
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
open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param






_<_>_  : BPredicate →  BitcoinScript →  BPredicate →  Set
ϕ < P > ψ = (s : State) → True (ϕ s) → True( (ψ ⁺ᵇ) ( ⟦ P ⟧ s))


weakestPreCond  :  (Postcond : BPredicate) → BitcoinScript →  BPredicate
weakestPreCond ψ P state =  (ψ ⁺ᵇ) ( ⟦ P ⟧ state)



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


trans<=>  :   (φ ψ ψ' : Predicate)
            →  φ <=>ᵖ ψ
            →  ψ <=>ᵖ ψ'
            →  φ <=>ᵖ ψ'
trans<=> φ ψ ψ' (equivp ==>e₁ <==e₁) (equivp ==>e₂ <==e₂)
 .==>e s p =  ==>e₂ s (==>e₁ s p)
trans<=> φ ψ ψ' (equivp ==>e₁ <==e₁) (equivp ==>e₂ <==e₂)
 .<==e s p = <==e₁ s (<==e₂ s p)




⊎HoareLemma1 : {φ ψ ψ' : Predicate}(p : BitcoinScript)
                  → < φ >ⁱᶠᶠ  p  < ψ >
                  → < ⊥p >ⁱᶠᶠ  p  < ψ' >
                  → < φ >ⁱᶠᶠ p < ψ ⊎p ψ' >
⊎HoareLemma1 {φ} {ψ} {ψ'} p (hoare3 c1 c2) c .==> s q
 = lemma⊎pleft ψ  ψ' (⟦ p ⟧ s) (c1 s q)
⊎HoareLemma1 {φ} {ψ} {ψ'} p (hoare3 ==>₁ <==₁)
 (hoare3 ==>₂ <==₂) .<== s q
          = let
              r : (ψ' ⁺) (⟦ p ⟧ s) → φ s
              r x = efq (<==₂ s x)
            in lemma⊎pinv ψ  ψ' (φ s) (⟦ p ⟧ s) (<==₁ s) r q


⊎HoareLemma2 : {φ φ' ψ ψ' : Predicate}(p : BitcoinScript)
                  → < φ >ⁱᶠᶠ  p  < ψ >
                  → < φ' >ⁱᶠᶠ  p  < ψ' >
                  → < φ ⊎p φ' >ⁱᶠᶠ p < ψ ⊎p ψ' >
⊎HoareLemma2 {φ} {φ'} {ψ} {ψ'} prog (hoare3 ==>₁ <==₁)
 (hoare3 ==>₂ <==₂) .==> s (inj₁ q)
          = lemma⊎pleft ψ ψ' (⟦ prog ⟧ s) (==>₁ s q)
⊎HoareLemma2 {φ} {φ'} {ψ} {ψ'} prog (hoare3 ==>₁ <==₁)
 (hoare3 ==>₂ <==₂) .==> s (inj₂ q)
           = lemma⊎pright ψ ψ' (⟦ prog ⟧ s) (==>₂ s q)
⊎HoareLemma2 {φ} {φ'} {ψ} {ψ'} prog (hoare3 ==>₁ <==₁)
 (hoare3 ==>₂ <==₂) .<== s q
          = let
              q1 : (ψ ⁺) (⟦ prog ⟧ s) → φ s ⊎ φ' s
              q1 x = inj₁ (<==₁ s x)

              q2 : (ψ' ⁺) (⟦ prog ⟧ s) → φ s ⊎ φ' s
              q2 x = inj₂ (<==₂ s x)
            in lemma⊎pinv ψ  ψ' ((φ ⊎p φ') s) (⟦ prog ⟧ s) q1 q2 q



predEquivr : (φ ψ ψ' : Predicate)
             (prog : BitcoinScript)
             → < φ >ⁱᶠᶠ prog < ψ >
             → ψ <=>ᵖ ψ'
             → < φ >ⁱᶠᶠ prog < ψ' >
predEquivr φ ψ ψ' prog (hoare3 ==>₁ <==₁) (equivp ==>e <==e) .==> s p1
  = liftPredtransformerMaybe ψ ψ' ==>e (⟦ prog ⟧ s) (==>₁ s p1)
predEquivr φ ψ ψ' prog (hoare3 ==>₁ <==₁) (equivp ==>e <==e) .<== s p1
             = let
                 subgoal : (ψ ⁺) (⟦ prog ⟧ s)
                 subgoal =  liftPredtransformerMaybe ψ' ψ <==e (⟦ prog ⟧ s) p1
                 goal : φ s
                 goal = <==₁ s subgoal
               in goal

predEquivl : (φ φ' ψ : Predicate)
             (prog : BitcoinScript)
             → φ <=>ᵖ φ'
             → < φ' >ⁱᶠᶠ prog < ψ >
             → < φ >ⁱᶠᶠ prog < ψ >
predEquivl φ φ' ψ prog (equivp ==>e <==e) (hoare3 ==>₁ <==₁) .==> s p1
             = let
                 goal : (ψ ⁺) (⟦ prog ⟧ s)
                 goal = ==>₁ s (==>e s p1)
               in goal
predEquivl φ φ' ψ prog (equivp ==>e <==e) (hoare3 ==>₁ <==₁) .<== s p1
              = let
                  subgoal : φ' s
                  subgoal = <==₁ s p1
                  goal : φ s
                  goal = <==e s subgoal
                in goal


equivPreds⊎ : (φ ψ ψ' : Predicate)
             → (φ ∧p (ψ ⊎p ψ')) <=>ᵖ ((φ ∧p ψ ) ⊎p (φ ∧p ψ'))

equivPreds⊎ φ ψ ψ' .==>e s (conj and4 (inj₁ x)) = inj₁ (conj and4 x)
equivPreds⊎ φ ψ ψ' .==>e s (conj and4 (inj₂ y)) = inj₂ (conj and4 y)
equivPreds⊎ φ ψ ψ' .<==e s (inj₁ (conj and4 and5)) = conj and4 (inj₁ and5)
equivPreds⊎ φ ψ ψ' .<==e s (inj₂ (conj and4 and5)) = conj and4 (inj₂ and5)

equivPreds⊎Rev : (φ ψ ψ' : Predicate)
             →  ((φ ∧p ψ ) ⊎p (φ ∧p ψ'))  <=>ᵖ (φ ∧p (ψ ⊎p ψ'))

equivPreds⊎Rev φ ψ ψ' .==>e s (inj₁ (conj and4 and5)) = conj and4 (inj₁ and5)
equivPreds⊎Rev φ ψ ψ' .==>e s (inj₂ (conj and4 and5)) = conj and4 (inj₂ and5)
equivPreds⊎Rev φ ψ ψ' .<==e s (conj and4 (inj₁ x)) = inj₁ (conj and4 x)
equivPreds⊎Rev φ ψ ψ' .<==e s (conj and4 (inj₂ y)) = inj₂ (conj and4 y)


_++ho_ : {P Q R : Predicate}{p q : BitcoinScript} → < P >ⁱᶠᶠ p < Q >
 → < Q >ⁱᶠᶠ q < R > → < P >ⁱᶠᶠ p ++  q < R >
_++ho_ {P} {Q} {R} {p} {q} pproof qproof .==>
 = bindTransformer-toSequence P Q R p q (pproof .==>)  (qproof .==>)
_++ho_ {P} {Q} {R} {p} {q} pproof qproof .<==
 = bindTransformer-fromSequence P Q R p q (pproof .<==)  (qproof .<==)

_++hoeq_ : {P Q R : Predicate}{p : BitcoinScript} → < P >ⁱᶠᶠ p < Q >  → < Q >ⁱᶠᶠ [] < R > → < P >ⁱᶠᶠ p  < R >
_++hoeq_ {P} {Q} {R} {p} pproof qproof .==>
 = bindTransformer-toSequenceeq P Q R p (pproof .==>)  (qproof .==>)
_++hoeq_ {P} {Q} {R} {p} pproof qproof .<==
 = bindTransformer-fromSequenceeq P Q R p (pproof .<==)  (qproof .<==)


module HoareReasoning  where
  infix  3 _∎p
  infixr 2 step-<><>  step-<><>ᵉ step-<=>

  _∎p : ∀ (φ : Predicate) → < φ >ⁱᶠᶠ [] < φ >
  (φ ∎p) .==>  s p = p
  (φ ∎p) .<==  s p = p


  step-<><> : ∀ {φ ψ ρ : Predicate}(p : BitcoinScript){q : BitcoinScript}
             → < φ >ⁱᶠᶠ p < ψ >
             → < ψ >ⁱᶠᶠ q < ρ >
             → < φ >ⁱᶠᶠ p ++ q < ρ >
  step-<><>  {φ} {ψ} {ρ} p φpψ ψqρ = φpψ ++ho ψqρ

  step-<><>ᵉ : ∀ {φ ψ ρ : Predicate}(p : BitcoinScript)
             → < φ >ⁱᶠᶠ p < ψ >
             → < ψ >ⁱᶠᶠ [] < ρ >
             → < φ >ⁱᶠᶠ p  < ρ >
  step-<><>ᵉ  p φpψ ψqρ = φpψ ++hoeq ψqρ





  step-<=> : ∀ {φ ψ ρ : Predicate}{p : BitcoinScript}
             → φ <=>ᵖ ψ
             → < ψ >ⁱᶠᶠ p < ρ >
             → < φ >ⁱᶠᶠ p < ρ >
  step-<=>  {φ} {ψ} {ρ} {p} φψ ψqρ = predEquivl φ ψ ρ p φψ ψqρ




  syntax step-<><> {φ} p φψ ψρ = φ <><>⟨  p ⟩⟨ φψ ⟩ ψρ
  syntax step-<><>ᵉ {φ} p φψ ψρ = φ <><>⟨  p ⟩⟨ φψ ⟩ᵉ ψρ



  syntax step-<=>  {φ} φψ ψρ = φ <=>⟨  φψ ⟩ ψρ




open HoareReasoning public



unfoldGenericCase=> : (A : IfStackEl → Set)
                     (φ ψ : (x : IfStackEl) → Predicate)
                     (prog : BitcoinScript)
                     (case : (x : IfStackEl) → A x → < φ x >ⁱᶠᶠ prog < ψ x >)
                     (x : IfStackEl)
                     → A x
                     → (s : State)
                     → φ x s → ((ψ x) ⁺) ( ⟦ prog ⟧ s)
unfoldGenericCase=> A φ ψ prog case x a = case x a .==>


unfoldGenericCase<= : (A : IfStackEl → Set)
                     (φ ψ : (x : IfStackEl) → Predicate)
                     (prog : BitcoinScript)
                     (case : (x : IfStackEl) → A x → < φ x >ⁱᶠᶠ prog < ψ x >)
                     (x : IfStackEl)
                     → A x
                     → (s : State)
                     → ((ψ x) ⁺) ( ⟦ prog ⟧ s) → φ x s
unfoldGenericCase<= A φ ψ prog case x a = case x a .<==


⊥Lemmap : (p : BitcoinScript)
          → < ⊥p >ⁱᶠᶠ  p  < ⊥p >
⊥Lemmap [] .==> s ()
⊥Lemmap p .<== s p' = liftToMaybeLemma⊥ (⟦ p ⟧ s)  p'


lemmaHoare[] : {φ : Predicate}
               → < φ >ⁱᶠᶠ [] < φ >
lemmaHoare[]  .==> s p = p
lemmaHoare[]  .<== s p = p


-- a generic Hoare triple, which refers instead of an instruction to the
--    state transformer (f will be equal to  ⟦ instr ⟧s )
record <_>gen_<_> (φ : Predicate)(f : State → Maybe State)(ψ : Predicate) : Set where
  constructor hoareTripleGen
  field
    ==>g : (s : State) → φ s → (ψ ⁺) (f s )
    <==g : (s : State) → (ψ ⁺)  (f s ) → φ s

open <_>gen_<_>  public




lemmaTransferHoareTripleGen : (φ ψ : Predicate)
                              (f g : State → Maybe State)
                              (p : (s : State) → f s ≡ g s)
                              → < φ >gen f < ψ >
                              → < φ >gen g < ψ >
lemmaTransferHoareTripleGen φ ψ f g p (hoareTripleGen ==>g₁ <==g₁) .==>g s x₁
          = transfer (λ x → (ψ ⁺) x) (p s) (==>g₁ s x₁)
lemmaTransferHoareTripleGen φ ψ f g p (hoareTripleGen ==>g₁ <==g₁) .<==g s x₁
          = <==g₁ s (transfer (λ x → (ψ ⁺) x) (sym (p s)) x₁)



