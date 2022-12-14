module verificationBitcoinScripts.state where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
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



open import basicBitcoinDataType
open import stack

open import verificationBitcoinScripts.ifStack



-----------------------------------------------------------------------------------------------------------------------------------
record State  : Set  where
       constructor ⟨_,_,_,_,_⟩
       field
         currentTime : Time  -- current time, i.e. time when the
                             -- the smart contract is executed
         msg : Msg
         stack : Stack
         ifStack : IfStack
         consis  : IfStackConsis ifStack

open State public


record StateWithMaybe  : Set  where
       constructor ⟨_,_,_,_,_⟩
       field
         currentTime : Time  -- current time, i.e. time when the
                             -- the smart contract is executed
         msg : Msg
         maybeStack : Maybe Stack
         ifStack : IfStack
         consis  : IfStackConsis ifStack

open StateWithMaybe public

state1WithMaybe : StateWithMaybe → Maybe State
state1WithMaybe ⟨ currentTime₁ , msg₁ , just x , ifStack₁ , consis₁ ⟩ = just ⟨ currentTime₁ , msg₁ , x , ifStack₁ , consis₁ ⟩
state1WithMaybe ⟨ currentTime₁ , msg₁ , nothing , ifStack₁ , consis₁ ⟩ = nothing



mutual


  liftStackToStateTransformerAux' : Maybe Stack → State → StateWithMaybe
  liftStackToStateTransformerAux' maybest ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₁ , consis₁ ⟩ = ⟨ currentTime₁ , msg₁ , maybest , ifStack₁ , consis₁ ⟩


exeTransformerDepIfStack' : ( State → StateWithMaybe ) →  State → Maybe State
exeTransformerDepIfStack' f st@( ⟨ currentTime₁ , msg₁ , stack₁ , [] , consis₁ ⟩)  =  state1WithMaybe (f st)
exeTransformerDepIfStack' f st@( ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ ifStack₁ , consis₁ ⟩) = state1WithMaybe (f st)
exeTransformerDepIfStack' f st@( ⟨ currentTime₁ , msg₁ , stack₁ , elseCase ∷ ifStack₁ , consis₁ ⟩) = state1WithMaybe (f st)
exeTransformerDepIfStack' f st@( ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , consis₁ ⟩) = just st
exeTransformerDepIfStack' f st@( ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , consis₁ ⟩) = just st
exeTransformerDepIfStack' f st@( ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , consis₁ ⟩) = just st

stackTransform2StateTransform : StackTransformer  → State → Maybe State
stackTransform2StateTransform f s
     = exeTransformerDepIfStack' (liftStackToStateTransformerAux' (f (s .currentTime) (s .msg) (s .stack))) s


liftStackToStateTransformerDepIfStack' : (Stack → Maybe Stack)  → State → Maybe State
liftStackToStateTransformerDepIfStack' f = stackTransform2StateTransform (λ time msg → f)


liftTimeStackToStateTransformerDepIfStack' : (Time → Stack → Maybe Stack)  → State → Maybe State
liftTimeStackToStateTransformerDepIfStack' f = stackTransform2StateTransform (λ time msg → f time)


liftMsgStackToStateTransformerDepIfStack' : (Msg → Stack → Maybe Stack)  → State → Maybe State
liftMsgStackToStateTransformerDepIfStack' f  = stackTransform2StateTransform (λ time → f)

