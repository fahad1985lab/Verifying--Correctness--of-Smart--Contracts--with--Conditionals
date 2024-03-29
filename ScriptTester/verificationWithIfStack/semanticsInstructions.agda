open import basicBitcoinDataType

module verificationWithIfStack.semanticsInstructions (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
-- open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite


open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
--open import libraries.miscLib
open import libraries.maybeLib

open import stack
open import instruction
open import semanticBasicOperations param
open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate






--function for opIf
executeOpIfBasic :  State → Maybe State
executeOpIfBasic ⟨  time , msg , bitcoinStack₁ , ifSkip ∷ ifStack₁ , c ⟩ =  just ⟨  time , msg , bitcoinStack₁ ,  ifIgnore  ∷  ifSkip ∷ ifStack₁ , c ⟩
executeOpIfBasic ⟨  time , msg , bitcoinStack₁ , ifIgnore ∷ ifStack₁ , c ⟩ = just ⟨ time , msg ,  bitcoinStack₁ ,  ifIgnore  ∷  ifIgnore ∷ ifStack₁ , c ⟩
executeOpIfBasic ⟨  time , msg , bitcoinStack₁ , elseSkip ∷ ifStack₁ , c ⟩ = just ⟨ time , msg ,  bitcoinStack₁ ,  ifIgnore  ∷  elseSkip ∷ ifStack₁ , c ⟩
executeOpIfBasic ⟨ time , msg , []                     , [] , c ⟩ =  nothing
executeOpIfBasic ⟨ time , msg , zero ∷ bitcoinStack₁   , [] , c ⟩ = just  ⟨ time , msg ,  bitcoinStack₁ , ifSkip  ∷  [] , c ⟩
executeOpIfBasic ⟨ time , msg , suc x ∷ bitcoinStack₁  , [] , c ⟩ =  just  ⟨ time , msg ,  bitcoinStack₁ , ifCase  ∷  [] , c ⟩
executeOpIfBasic ⟨ time , msg , []                     , ifCase ∷ ifStack₁ , c ⟩ =  nothing
executeOpIfBasic ⟨ time , msg , zero ∷ bitcoinStack₁   , ifCase ∷ ifStack₁ , c ⟩ = just  ⟨  time , msg , bitcoinStack₁ , ifSkip  ∷  ifCase ∷  ifStack₁ , c ⟩
executeOpIfBasic ⟨ time , msg , suc x ∷ bitcoinStack₁  , ifCase ∷ ifStack₁ , c ⟩ = just ⟨ time , msg ,  bitcoinStack₁ , ifCase  ∷ ifCase ∷  ifStack₁  , c ⟩
executeOpIfBasic ⟨ time , msg , []                     , elseCase ∷ ifStack₁ , c ⟩ =  nothing
executeOpIfBasic ⟨ time , msg , zero ∷ bitcoinStack₁   , elseCase ∷ ifStack₁ , c ⟩ = just ⟨ time , msg ,  bitcoinStack₁ ,  ifSkip ∷  elseCase ∷ ifStack₁  , c ⟩
executeOpIfBasic ⟨ time , msg , suc x ∷ bitcoinStack₁  , elseCase ∷ ifStack₁ , c ⟩ = just ⟨ time , msg ,  bitcoinStack₁ ,  ifCase ∷  elseCase ∷ ifStack₁  , c ⟩


--function for opElse
executeOpElseBasic : State → Maybe State
executeOpElseBasic ⟨ time , msg , bitcoinStack₁ , [] , c ⟩ = nothing
executeOpElseBasic ⟨ time , msg , bitcoinStack₁ , elseSkip ∷ ifStack₁ , c ⟩ = nothing
executeOpElseBasic ⟨ time , msg , bitcoinStack₁ , elseCase ∷ ifStack₁ , c ⟩ = nothing
executeOpElseBasic ⟨ time , msg , bitcoinStack₁ , ifSkip ∷ ifStack₁ , c ⟩ = just ⟨ time , msg , bitcoinStack₁ , elseCase ∷ ifStack₁ , c ⟩
executeOpElseBasic ⟨ time , msg , bitcoinStack₁ , ifCase ∷ ifStack₁ , c ⟩  = just ⟨ time , msg , bitcoinStack₁ , elseSkip ∷ ifStack₁ , ∧bproj₂ c ⟩
executeOpElseBasic ⟨ time , msg , bitcoinStack₁ , ifIgnore ∷ ifStack₁ , c ⟩  = just ⟨ time , msg , bitcoinStack₁ , elseSkip ∷ ifStack₁ , ∧bproj₂ c ⟩


--function for opEndIf
executeOpEndIfBasic :  State → Maybe   State
executeOpEndIfBasic ⟨ time , msg , bitcoinStack , [] , c ⟩  = nothing
executeOpEndIfBasic ⟨ time , msg , bitcoinStack , x ∷ ifStack , c ⟩  = just (⟨ time , msg , bitcoinStack , ifStack , lemmaIfStackConsisTail x  ifStack c ⟩)





⟦_⟧s : InstructionAll → State → Maybe State
⟦ opEqual ⟧s = liftStackToStateTransformerDepIfStack'  executeStackEquality
⟦ opAdd ⟧s = liftStackToStateTransformerDepIfStack' executeStackAdd
⟦ (opPush x) ⟧s = liftStackToStateTransformerDepIfStack' (executeStackPush x)
⟦ opSub ⟧s  = liftStackToStateTransformerDepIfStack' executeStackSub
⟦ opVerify ⟧s = liftStackToStateTransformerDepIfStack' executeStackVerify
⟦ opCheckSig ⟧s  =  liftMsgStackToStateTransformerDepIfStack' executeStackCheckSig
⟦ opEqualVerify ⟧s =  liftStackToStateTransformerDepIfStack'  executeStackVerify
⟦ opDup ⟧s = liftStackToStateTransformerDepIfStack' executeStackDup
⟦ opDrop ⟧s = liftStackToStateTransformerDepIfStack' executeStackDrop
⟦ opSwap ⟧s =  liftStackToStateTransformerDepIfStack' executeStackSwap
⟦ opCHECKLOCKTIMEVERIFY ⟧s =  liftTimeStackToStateTransformerDepIfStack' executeOpCHECKLOCKTIMEVERIFY
⟦ opCheckSig3  ⟧s = liftMsgStackToStateTransformerDepIfStack' executeStackCheckSig3Aux
⟦ opHash  ⟧s =  liftStackToStateTransformerDepIfStack' executeOpHash
⟦ opMultiSig ⟧s = liftMsgStackToStateTransformerDepIfStack' executeMultiSig
⟦ opIf ⟧s =   executeOpIfBasic
⟦ opElse ⟧s =  executeOpElseBasic
⟦ opEndIf ⟧s =  executeOpEndIfBasic

⟦_⟧s⁺ : InstructionAll → Maybe State → Maybe State
⟦ op ⟧s⁺ t = t >>= ⟦ op ⟧s



⟦_⟧ : BitcoinScript → State → Maybe State
⟦ []  ⟧  = just
⟦ x ∷ []  ⟧  = ⟦ x ⟧s
⟦ x ∷ l   ⟧  s = ⟦ x ⟧s s >>= ⟦ l ⟧


⟦_⟧⁺ : BitcoinScript → Maybe State → Maybe State
⟦ op ⟧⁺ s = s >>= ⟦ op ⟧

validStackAux : (pbkh : ℕ) →  (msg : Msg) →  Stack →  Bool
validStackAux pkh msg[]  []  = false
validStackAux pkh msg (pbk ∷ []) = false
validStackAux pkh msg (pbk ∷ sig ∷ s) = hashFun pbk  ==b pkh ∧b isSigned msg sig pbk

validStack : (pkh : ℕ) →  BPredicate
validStack pkh ⟨ time , msg₁ , stack₁ , ifStack₁ , c ⟩ = validStackAux  pkh   msg₁  stack₁
