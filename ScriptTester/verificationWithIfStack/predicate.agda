

module verificationWithIfStack.predicate where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
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

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
--open import libraries.miscLib
open import libraries.maybeLib

open import basicBitcoinDataType
open import stack
open import stackPredicate

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state


BPredicate  : Set
BPredicate =  State →  Bool

Predicate  : Set₁
Predicate =  State →  Set



MaybeBPredicate : Set
MaybeBPredicate = Maybe State →  Bool



ifStackPredicate : IfStack → Predicate
ifStackPredicate ifs ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ = ifStack₁ ≡ ifs

{- stack is equal to the argument but there is one more element on top -}
ifStackPredicateAnyTop : IfStack → Predicate
ifStackPredicateAnyTop ifs ⟨ time , msg₁ , stack₁ , [] , c ⟩ = ⊥
ifStackPredicateAnyTop ifs ⟨ time , msg₁ , stack₁ , x ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs


-- defined in ifThenElseTheoremPart1.agda
-- ifStackPredicateAnySkipTop : IfStack → Predicate
--     expresses that the IfStack in the state is   x ∷ ifStack₁
--     for any x such that
--     IsNonActiveIfStackEl x holds
--  which means any operation should be skipped

{- stack is equal to the argument but there is one more element on top which is a skip element -}
ifStackPredicateAnySkipTop : IfStack → Predicate
ifStackPredicateAnySkipTop ifs ⟨ time , msg₁ , stack₁ , [] , c ⟩ = ⊥
ifStackPredicateAnySkipTop ifs ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs
ifStackPredicateAnySkipTop ifs ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs
ifStackPredicateAnySkipTop ifs ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs
ifStackPredicateAnySkipTop ifs ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateAnySkipTop ifs ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₁ , c ⟩ = ⊥

-- defined in ifThenElseTheoremPart1.agda
-- ifStackPredicateAnyDoTop : IfStack → Predicate
--     expresses that the IfStack in the state is   x ∷ ifStack₁
--     for any x such that
--     IsActiveIfStackEl x holds
--  which means any operation should be executed

{- stack is equal to the argument but there is one more element on top which is a do case -}
ifStackPredicateAnyDoTop : IfStack → Predicate
ifStackPredicateAnyDoTop ifs ⟨ time , msg₁ , stack₁ , [] , c ⟩ = ⊥
ifStackPredicateAnyDoTop ifs ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , c ⟩ =  ⊥
ifStackPredicateAnyDoTop ifs ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateAnyDoTop ifs ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateAnyDoTop ifs ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs
ifStackPredicateAnyDoTop ifs ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs

ifStackPredicateIfSkipOrIgnoreOnTop : IfStack → Predicate
ifStackPredicateIfSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , [] , c ⟩ = ⊥
ifStackPredicateIfSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , c ⟩ =  ifStack₁ ≡ ifs
ifStackPredicateIfSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs
ifStackPredicateIfSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateIfSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateIfSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₁ , c ⟩ = ⊥

ifStackPredicateAnyNonIfIgnoreTop : IfStack → Predicate
ifStackPredicateAnyNonIfIgnoreTop ifs ⟨ time , msg₁ , stack₁ , [] , c ⟩ = ⊥
ifStackPredicateAnyNonIfIgnoreTop ifs ⟨ time , msg₁ , stack₁ , x ∷ ifStack₁ , c ⟩ = (ifStack₁ ≡ ifs) ∧  IfStackIsNonIfIgnore x

ifStackPredicateElseSkipOrIgnoreOnTop : IfStack → Predicate
ifStackPredicateElseSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , [] , c ⟩ = ⊥
ifStackPredicateElseSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , c ⟩ =  ifStack₁ ≡ ifs
ifStackPredicateElseSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , c ⟩ = ifStack₁ ≡ ifs
ifStackPredicateElseSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , ifCase ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateElseSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , c ⟩ = ⊥
ifStackPredicateElseSkipOrIgnoreOnTop ifs ⟨ time , msg₁ , stack₁ , elseCase ∷ ifStack₁ , c ⟩ = ⊥



predicateAfterPushingx : (n : ℕ)(P : Predicate) → Predicate
predicateAfterPushingx n P ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ = P ⟨ time , msg₁ , n ∷ stack₁ , ifStack₁ , c ⟩

predicateForTopElOfStack : (n : ℕ) → Predicate
predicateForTopElOfStack n ⟨ time , msg₁ , [] , ifStack₁ , c ⟩ = ⊥
predicateForTopElOfStack n ⟨ time , msg₁ , x ∷ stack₁ , ifStack₁ , c ⟩ = x ≡ n


truefalsePred : (φ ψ : StackPredicate) → Predicate
truefalsePred φ ψ ⟨ time , msg , [] , ifStack , c ⟩ = ⊥
truefalsePred φ ψ ⟨ time , msg , zero ∷ stack , ifStack , c ⟩ = φ time msg stack
truefalsePred φ ψ ⟨ time , msg , suc x ∷ stack , ifStack , c ⟩ = ψ time msg stack


_∧p_ : ( φ ψ  : Predicate ) → Predicate
(φ ∧p ψ ) s  =  φ s  ∧  ψ s





⊥p : Predicate
⊥p s = ⊥



infixl 4 _⊎p_

_⊎p_   : (φ ψ : Predicate) → Predicate
(φ ⊎p ψ) s = φ s ⊎ ψ s

lemma⊎pleft : (ψ ψ' : Predicate)(s : Maybe State)
              → (ψ ⁺) s → ((ψ ⊎p ψ') ⁺) s
lemma⊎pleft ψ ψ' (just x) p = inj₁ p

lemma⊎pright : (ψ ψ' : Predicate) (s : Maybe State)
               → (ψ' ⁺) s → ((ψ ⊎p ψ') ⁺) s
lemma⊎pright  ψ ψ' (just x) p = inj₂ p

lemma⊎pinv : (ψ ψ' : Predicate)(A : Set) (s : Maybe State)
             → ((ψ ⁺) s  → A)
             → ((ψ' ⁺) s  → A)
             →  ((ψ ⊎p ψ') ⁺) s → A
lemma⊎pinv ψ ψ' A (just x) p q (inj₁ x₁) = p x₁
lemma⊎pinv ψ ψ' A (just x) p q (inj₂ y) = q y



stackPred2Pred : StackPredicate  → Predicate
stackPred2Pred f  ⟨ time , msg₁ , stack₁ , [] , c ⟩ = f time msg₁ stack₁
stackPred2Pred f ⟨ time , msg₁ , stack₁ , x ∷ ifStack₁ , c ⟩ = ⊥


stackPred2PredBool : ( Time → Msg → Stack → Bool ) → (  State →  Bool )
stackPred2PredBool f ⟨ currentTime₁ , msg₁ , stack₁ , [] , consis₁ ⟩
              = f currentTime₁ msg₁ stack₁
stackPred2PredBool f ⟨ currentTime₁ , msg₁ , stack₁ , x ∷ ifStack₁ , consis₁ ⟩
             =  false


liftStackPred2PredIgnoreIfStack : StackPredicate → Predicate
liftStackPred2PredIgnoreIfStack f  ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ = f time msg₁ stack₁


topElStack>0 : Predicate
topElStack>0 ⟨ time , msg₁ , [] , ifStack₁ , c ⟩ = ⊥
topElStack>0 ⟨ time , msg₁ , zero ∷ stack₁ , ifStack₁ , c ⟩ = ⊥
topElStack>0 ⟨ time , msg₁ , suc x ∷ stack₁ , ifStack₁ , c ⟩ = ⊤

topElStack=0 : Predicate
topElStack=0 ⟨ time , msg₁ , [] , ifStack₁ , c ⟩ = ⊥
topElStack=0 ⟨ time , msg₁ , zero ∷ stack₁ , ifStack₁ , c ⟩ = ⊤
topElStack=0 ⟨ time , msg₁ , suc x ∷ stack₁ , ifStack₁ , c ⟩ = ⊥



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


liftAddingx : (n : ℕ)( φ : StackPredicate ) →  Predicate
liftAddingx n φ = predicateAfterPushingx n (liftStackPred2PredIgnoreIfStack φ)


liftStackPred2Pred : StackPredicate →  IfStack → Predicate
liftStackPred2Pred ψ ifStack₁ = liftStackPred2PredIgnoreIfStack ψ ∧p ifStackPredicate  ifStack₁


acceptState : Predicate
acceptState = stackPred2Pred acceptStateˢ

