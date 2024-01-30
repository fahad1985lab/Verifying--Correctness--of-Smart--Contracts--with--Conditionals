open import basicBitcoinDataType

module verificationWithIfStack.equalitiesIfThenElse (param : GlobalParameters) where

open import Data.List hiding (_++_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite

open import libraries.listLib
-- open import libraries.natLib
-- open import libraries.equalityLib
-- open import libraries.andLib
-- open import libraries.miscLib
-- open import libraries.maybeLib

open import stack
open import instruction

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate





lemmaOpIfProg++[] : (ifCaseProg elseCaseProg : BitcoinScript)  →
   _≡_  {A = BitcoinScript}
   (opIf ∷' ifCaseProg ++ ( opElse ∷' elseCaseProg ++ []))
   (opIf ∷' ifCaseProg ++ opElse ∷' elseCaseProg)

lemmaOpIfProg++[]  ifCaseProg elseCaseProg
 = cong (λ l → opIf ∷ ifCaseProg ++ l)
   (lemma++[] (opElse ∷ elseCaseProg))


lemmaOpIfProg++[]' : (ifCaseProg elseCaseProg : BitcoinScript)  →
      _≡_ {A = BitcoinScript}
      (opIf ∷ (ifCaseProg ++ (opElse ∷ elseCaseProg) ++ [] ))
      (opIf ∷' ifCaseProg ++ opElse ∷' elseCaseProg)
lemmaOpIfProg++[]'  ifCaseProg elseCaseProg
 = cong (λ x → (opIf ∷ []) ++ x) ((lemma++[]
  (ifCaseProg ++ opElse ∷' elseCaseProg)))



lemmaOpIfProg++[]new : (ifCaseProg elseCaseProg : BitcoinScript)  →
      _≡_ {A = BitcoinScript}
 ((opIf ∷ [] ) ++ (ifCaseProg   ++ (((opElse ∷ [])   ++  elseCaseProg ) )))
 ((((opIf ∷ []) ++   ifCaseProg)  ++   (opElse ∷ []))  ++  elseCaseProg)
lemmaOpIfProg++[]new ifCaseProg elseCaseProg
  = lemmaListAssoc4 (opIf ∷ []) ifCaseProg (opElse ∷ []) elseCaseProg


lemmaIfThenElseProg== : (ifCaseProg elseCaseProg : BitcoinScript)  →
   _≡_  {A = BitcoinScript}
   ((opIf ∷ (ifCaseProg ++ opElse ∷'  elseCaseProg)) ++ opEndIf ∷' [])
   (opIf ∷' ifCaseProg ++ opElse ∷' elseCaseProg    ++ opEndIf ∷' [])
lemmaIfThenElseProg== ifCaseProg elseCaseProg = refl


lemmaOpIfProg++[]''' :
     (ifCaseProg elseCaseProg : BitcoinScript)  →
     _≡_  {A = BitcoinScript}
 (opIf ∷ (ifCaseProg ++ opElse ∷' elseCaseProg) ++ opEndIf ∷' [])
 (opIf ∷ ifCaseProg ++ opElse ∷' elseCaseProg ++ opEndIf ∷' [])
lemmaOpIfProg++[]''' ifCaseProg elseCaseProg  = refl






lemmaOpIfProg++[]5 : (ifCaseProg elseCaseProg : BitcoinScript)  →
 _≡_  {A = BitcoinScript}
 (ifCaseProg ++ (opElse ∷ elseCaseProg))
 (ifCaseProg ++ (opElse ∷ []) ++ elseCaseProg)
lemmaOpIfProg++[]5 [] elseCaseProg = refl
lemmaOpIfProg++[]5 (x ∷ ifCaseProg) elseCaseProg
 = cong (λ l → x ∷ l) (lemmaOpIfProg++[]5  ifCaseProg elseCaseProg)

lemmaOpIfProg++[]4 :
 (ifCaseProg elseCaseProg : BitcoinScript)  →
 _≡_  {A = BitcoinScript}
  (opIf ∷ (ifCaseProg ++ opElse ∷' elseCaseProg ++ opEndIf ∷' []))
  (opIf ∷ (ifCaseProg ++ opElse ∷' [] ++ elseCaseProg ++ opEndIf ∷' []))
lemmaOpIfProg++[]4 ifCaseProg elseCaseProg  =
 cong (λ l → opIf ∷ (l ++ opEndIf ∷' []))
 (lemmaOpIfProg++[]5 ifCaseProg elseCaseProg)

