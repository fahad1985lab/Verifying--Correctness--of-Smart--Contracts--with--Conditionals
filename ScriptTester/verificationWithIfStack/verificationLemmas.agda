open import basicBitcoinDataType

module verificationWithIfStack.verificationLemmas (param : GlobalParameters) where

open import libraries.listLib
open import libraries.natLib
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_ )
                       renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
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
--open import libraries.miscLib
open import libraries.maybeLib
open import libraries.boolLib

-- open import verificationWithIfStack.ifStack
open import stack
open import instruction
-- open import ledger param

open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param

liftCondOperation2Program-to-simple : (accept2 : Predicate)
  (op : InstructionAll)  (s : State)
  → (accept2 ⁺) (⟦ op ⟧s s )
  → (accept2 ⁺) (⟦ op ∷ [] ⟧ s )
liftCondOperation2Program-to-simple accept2 op s x
    = x 

liftCondOperation2Program-from-simple : (accept2 : Predicate)
  (op : InstructionAll)  (s : State)
  → (accept2 ⁺) (⟦ op ∷ [] ⟧ s )
  → (accept2 ⁺) (⟦ op ⟧s s )
liftCondOperation2Program-from-simple accept2 op s x
    = x 



liftCondOperation2Program-to : (accept1 accept2 : Predicate)
  (op : InstructionAll)
  (correct : (s : State) → accept1 s → (accept2 ⁺) (⟦ op ⟧s s ))
  (s : State)
  → accept1 s
  → (accept2 ⁺) (⟦ op ∷ [] ⟧ s )
liftCondOperation2Program-to accept1 accept2 op correct s a
    = correct s a  


liftCondOperation2Program-from : (accept1 accept2 : Predicate)
   (op : InstructionAll)
   (correct : (s : State) → (accept2 ⁺) (⟦ op ⟧s s ) → accept1 s)
   (s : State)
   → (accept2 ⁺) (⟦ op ∷ [] ⟧ s ) → accept1 s
liftCondOperation2Program-from accept1 accept2 op correct s a
      = correct s a


emptyProgramCorrect-to : (accept1 : Predicate)
    (s : State) → accept1 s → (accept1 ⁺) (⟦ [] ⟧ s )
emptyProgramCorrect-to accept1 s a = a

emptyProgramCorrect-from : (accept1 : Predicate)
    (s : State) → (accept1 ⁺) (⟦ [] ⟧ s ) → accept1 s
emptyProgramCorrect-from accept1 s a = a


bindTransformerBack : (accept2 accept3 : Predicate)
     (f : State → Maybe State)
     (correct2 : (s : State) → (accept3 ⁺) (f s) → accept2 s)
     (s : Maybe State)
     → ((accept3 ⁺) (s >>= f)) → (accept2 ⁺) s
bindTransformerBack accept2 accept3 f correct2  (just s) a  = correct2 s a

bindTransformeraux : (accept2 accept3 : Predicate)
                        (f :  State → Maybe State)
                        (correct2 : (s : State) → accept2 s → (accept3 ⁺) (f s ))
                        → (s2 : Maybe State) →  ((accept2 ⁺) s2)  → (accept3 ⁺) (s2 >>= f)
bindTransformeraux accept2 accept3 f correct2  (just s) correct1 = correct2 s correct1


bindTransformer-toSingle : (accept1 accept2 accept3 : Predicate)
   (op : InstructionAll)
   (p  : List InstructionAll)
   (correct1 : (s : State) → accept1 s → (accept2 ⁺) (⟦ op ⟧s s ))
   (correct2 : (s : State) → accept2 s → (accept3 ⁺) (⟦ p ⟧ s ))  →
    (s : State)
    → accept1 s
    → (accept3 ⁺) (⟦ op ∷ p ⟧ s )
bindTransformer-toSingle accept1 accept2 accept3 op [] correct1 correct2 s a = liftPredtransformerMaybe accept2 accept3 correct2 (⟦ op ⟧s s) (correct1 s a) 
bindTransformer-toSingle accept1 accept2 accept3 op ( p@(x ∷ p₁) ) correct1 correct2 s a = bindTransformeraux  accept2  accept3 ⟦ p  ⟧  correct2  (⟦ op ⟧s  s) (correct1 s a)

bindTransformer-fromSingle : (accept1 accept2 accept3 : Predicate)
   (op : InstructionAll)
   (p  : List InstructionAll)
   (correct1 : (s : State) → (accept2 ⁺) (⟦ op ⟧s s ) → accept1 s)
   (correct2 : (s : State) → (accept3 ⁺) (⟦ p ⟧ s ) → accept2 s)             (s : State)
   → (accept3 ⁺) (⟦ op ∷ p ⟧ s ) → accept1 s
bindTransformer-fromSingle accept1 accept2 accept3 op [] correct1 correct2 s a
   = correct1 s (liftPredtransformerMaybe accept3 accept2 correct2 (⟦ op ⟧s s) a)
bindTransformer-fromSingle accept1 accept2 accept3 op (p@(x ∷ p₁)) correct1 correct2 s a = correct1 s (bindTransformerBack accept2 accept3  ⟦ p ⟧  correct2 ( ⟦ op ⟧s s)  a )



p++xSemLem :  (x : InstructionAll)(s : Maybe State) (p : BitcoinScript)
        →  (⟦ p ⟧⁺ s >>= ⟦ x ⟧s )
               ≡
           ⟦ p ++ (x ∷ []) ⟧⁺ s
p++xSemLem x nothing s = refl
p++xSemLem x (just s) [] = refl 
p++xSemLem x (just s) (x₁ ∷ []) = refl
p++xSemLem x (just s) (x₁ ∷ x₂ ∷ p) = p++xSemLem x (⟦ x₁ ⟧s s) (x₂ ∷ p) 

p++xSemLemb :  (x : InstructionAll)(s : Maybe State) (p : BitcoinScript)
        →  ⟦ p ++ (x ∷ []) ⟧⁺ s
               ≡
            (⟦ p ⟧⁺ s >>= ⟦ x ⟧s )
p++xSemLemb x nothing s = refl
p++xSemLemb x (just s) [] = refl
p++xSemLemb x (just s) (x₁ ∷ []) = refl
p++xSemLemb x (just s) (x₁ ∷ x₂ ∷ p) = p++xSemLemb x (⟦ x₁ ⟧s s ) ( x₂ ∷ p )

p++x::qLem : (p1 p2 : BitcoinScript)(x : InstructionAll) → p1 ++ x ∷' p2 ≡ (p1 ++ (x ∷ [])) ++ p2
p++x::qLem [] p2 x = refl
p++x::qLem (x₁ ∷ p1) p2 x = cong (λ p → x₁ ∷ p) (p++x::qLem p1 p2 x)

++[]lem : (p : BitcoinScript) → p ++ [] ≡ p
++[]lem [] = refl
++[]lem (x ∷ p) = cong (λ q → x ∷ q) (++[]lem p)

liftMaybeCompLemma : (f k : State → Maybe State)(s : Maybe State)
            → (s >>= λ s₁ → k s₁ >>= f  )  ≡ ((s >>= k) >>= f)
liftMaybeCompLemma f k nothing = refl
liftMaybeCompLemma f k (just x) = refl

liftMaybeCompLemma2 : (f k : State → Maybe State)(s : Maybe State)
            → ((s >>= k) >>= f)  ≡ (s >>= λ s₁ → k s₁ >>= f  )
liftMaybeCompLemma2 f k nothing = refl
liftMaybeCompLemma2 f k (just x) = refl


lemmaBindTransformerAux' : (p1 p2 : BitcoinScript)(s : Maybe  State)
    →  ⟦ p2 ++ p1 ⟧⁺ s ≡ (⟦ p2 ⟧⁺ s  >>= ⟦ p1 ⟧ )
lemmaBindTransformerAux' [] p2 s = ⟦ p2 ++ [] ⟧⁺ s
                                        ≡⟨ cong (λ p → ⟦ p  ⟧⁺ s) (++[]lem p2) ⟩
                                     ⟦ p2  ⟧⁺ s
                                        ≡⟨ liftJustEqLem2 (⟦ p2  ⟧⁺ s) ⟩
                                     (⟦ p2 ⟧⁺ s  >>= just )
                                     ∎

lemmaBindTransformerAux' (x ∷ []) p2 s = p++xSemLemb x s p2

lemmaBindTransformerAux' (x ∷ p1@(x₁ ∷ p1')) p2 s
        = ⟦ p2 ++ x ∷' p1 ⟧⁺ s
                ≡⟨ cong (λ p → ⟦ p ⟧⁺ s  ) (p++x::qLem p2 p1 x)  ⟩
             ⟦ (p2 ++ (x ∷ [])) ++ p1  ⟧⁺ s
                ≡⟨ lemmaBindTransformerAux'  p1 (p2 ++ (x ∷ [])) s  ⟩
             (⟦ p2 ++ (x ∷ []) ⟧⁺ s >>= ⟦ p1 ⟧  )
                ≡⟨ cong (λ t → ⟦ p1 ⟧⁺ t) (p++xSemLemb x s p2)  ⟩
             ((⟦ p2 ⟧⁺ s >>= ⟦ x ⟧s ) >>= ⟦ p1 ⟧  )
                ≡⟨ liftMaybeCompLemma2 ⟦ p1 ⟧  ⟦ x ⟧s (⟦ p2 ⟧⁺ s )  ⟩
             (⟦ p2 ⟧⁺ s  >>= λ s₁ → ⟦ x ⟧s s₁ >>= ⟦ p1 ⟧ )
                ≡⟨ refl  ⟩
             (⟦ p2 ⟧⁺ s  >>= ⟦ x ∷ p1 ⟧ )
             ∎


lemmaBindTransformer' : (p1 p2 : BitcoinScript)(s : State)
                       → ⟦ p2 ++ p1 ⟧ s ≡ (⟦ p2 ⟧ s >>= ⟦ p1 ⟧ )
lemmaBindTransformer' p1 p2 s = lemmaBindTransformerAux' p1 p2 (just s)




lemmaBindTransformerAux : (p1 p2 : BitcoinScript)(s : Maybe  State)
           → ⟦ p2 ++ p1 ⟧⁺ s ≡ (⟦ p2 ⟧⁺ s >>= ⟦ p1 ⟧ )
lemmaBindTransformerAux p1 [] s = lemmaBindTransformerAux' p1 [] s
lemmaBindTransformerAux p1 (x ∷ p2) s = lemmaBindTransformerAux' p1 (x ∷ p2) s

lemmaBindTransformer : (p1 p2 : BitcoinScript)(s : State) → ⟦ p2 ++ p1 ⟧ s ≡ (⟦ p2 ⟧ s >>= ⟦ p1 ⟧ )
lemmaBindTransformer p₁ [] s = refl
lemmaBindTransformer [] (x ∷ []) s = liftJustIsIdLem (λ l → ⟦ x ⟧s s ≡ l) (⟦ x ⟧s s) refl
lemmaBindTransformer (x₁ ∷ p₁) (x ∷ []) s = refl
lemmaBindTransformer p₁ (x ∷ p₂@(x₁ ∷ p₂')) s = lemmaBindTransformerAux p₁ p₂ (⟦ x ⟧s s)


lemmaBindTransformereq : (p2 : BitcoinScript)(s : State) → ⟦ p2  ⟧ s ≡ (⟦ p2 ⟧ s >>= ⟦ [] ⟧ )
lemmaBindTransformereq [] s = refl
lemmaBindTransformereq (x ∷ p₂) s = liftJustEqLem2 (⟦ x ∷ p₂ ⟧ s)

bindTransformer-toSequence : (accept1 accept2 accept3 : Predicate)
                               (p1 : BitcoinScript)
                               (p2  : BitcoinScript)
                               (correct1 : (s : State) → accept1 s → (accept2 ⁺) (⟦ p1 ⟧ s ))
                               (correct2 : (s : State) → accept2 s → (accept3 ⁺) (⟦ p2 ⟧ s ))                                                  →
                               (s : State) → accept1 s → (accept3 ⁺) (⟦ p1 ++ p2 ⟧ s )
bindTransformer-toSequence accept1 accept2 accept3 p1 p2 correct1 correct2 s a rewrite lemmaBindTransformer p2 p1 s
                                            = bindTransformeraux accept2 accept3 ⟦ p2 ⟧ correct2 ( ⟦ p1 ⟧ s  )(correct1 s a)

bindTransformer-fromSequence : (accept1 accept2 accept3 : Predicate)
                              (p1 : BitcoinScript)
                              (p2  : BitcoinScript)
                              (correct1 : (s : State) → (accept2 ⁺) (⟦ p1 ⟧ s ) → accept1 s)
                              (correct2 : (s : State) → (accept3 ⁺) (⟦ p2 ⟧ s ) → accept2 s) →
                              (s : State) → (accept3 ⁺) (⟦ p1 ++ p2 ⟧ s ) → accept1 s
bindTransformer-fromSequence accept1 accept2 accept3 p1 p2 correct1 correct2 s a   rewrite lemmaBindTransformer p2 p1 s
                             = correct1 s (bindTransformerBack accept2 accept3 ⟦ p2 ⟧   correct2 (⟦ p1 ⟧ s) a)


bindTransformer-toSequenceeq : (accept1 accept2 accept3 : Predicate)
                               (p1 : BitcoinScript)
                               (correct1 : (s : State) → accept1 s → (accept2 ⁺) (⟦ p1 ⟧ s ))
                               (correct2 : (s : State) → accept2 s → (accept3 ⁺) (⟦ [] ⟧ s ))                                                  →
                               (s : State) → accept1 s → (accept3 ⁺) (⟦ p1 ⟧ s )
bindTransformer-toSequenceeq accept1 accept2 accept3 p1  correct1 correct2 s a rewrite lemmaBindTransformereq p1 s
                                            = bindTransformeraux accept2 accept3 ⟦ [] ⟧ correct2 ( ⟦ p1 ⟧ s  )(correct1 s a)


bindTransformer-fromSequenceeq : (accept1 accept2 accept3 : Predicate)
                              (p1 : BitcoinScript)
                              (correct1 : (s : State) → (accept2 ⁺) (⟦ p1 ⟧ s ) → accept1 s)
                              (correct2 : (s : State) → (accept3 ⁺) (⟦ [] ⟧ s ) → accept2 s) →
                              (s : State) → (accept3 ⁺) (⟦ p1  ⟧ s ) → accept1 s
bindTransformer-fromSequenceeq accept1 accept2 accept3 p1 correct1 correct2 s a  rewrite lemmaBindTransformereq p1 s
                             = correct1 s (bindTransformerBack accept2 accept3 ⟦ [] ⟧   correct2 (⟦ p1 ⟧ s) a) 
