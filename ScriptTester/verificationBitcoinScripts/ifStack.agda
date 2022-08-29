module verificationBitcoinScripts.ifStack where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  hiding (_≤_)
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Bool.Base hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import basicBitcoinDataType

data IfStackEl : Set where
    ifCase elseCase ifSkip elseSkip ifIgnore  : IfStackEl

--ifStack
IfStack : Set
IfStack =  List IfStackEl


isActiveIfStackEl : IfStackEl → Bool
isActiveIfStackEl ifCase = true
isActiveIfStackEl elseCase = true
isActiveIfStackEl ifSkip = false
isActiveIfStackEl elseSkip = false
isActiveIfStackEl ifIgnore = false

IsActiveIfStackEl : IfStackEl → Set
IsActiveIfStackEl s = True  (isActiveIfStackEl s)

isActiveIfStack : IfStack → Bool
isActiveIfStack [] = true
isActiveIfStack (x ∷ s) = isActiveIfStackEl x

IsActiveIfStack : IfStack → Set
IsActiveIfStack s = True (isActiveIfStack s)


isNonActiveIfStackEl : IfStackEl → Bool
isNonActiveIfStackEl s = not (isActiveIfStackEl s)

IsNonActiveIfStackEl : IfStackEl → Set
IsNonActiveIfStackEl s = True  (isNonActiveIfStackEl s)







isNonActiveIfStack : IfStack → Bool
isNonActiveIfStack s =  not (isActiveIfStack s)

IsNonActiveIfStack : IfStack → Set
IsNonActiveIfStack s = True (isNonActiveIfStack s)


--from addition1
ifStackElIsIfSkipOrElseSkip : IfStackEl → Bool
ifStackElIsIfSkipOrElseSkip ifSkip = true
ifStackElIsIfSkipOrElseSkip elseSkip = true
ifStackElIsIfSkipOrElseSkip s = false
--from addition1
IfStackElIsIfSkipOrElseSkip : IfStackEl → Set
IfStackElIsIfSkipOrElseSkip s = True (ifStackElIsIfSkipOrElseSkip s)


ifStackConsis : IfStack → Bool
ifStackConsis [] = true
ifStackConsis (ifCase ∷ s) = isActiveIfStack s ∧b ifStackConsis s
ifStackConsis (elseCase ∷ s) = isActiveIfStack s ∧b ifStackConsis s
ifStackConsis (ifSkip ∷ s) = isActiveIfStack s ∧b ifStackConsis s
ifStackConsis (elseSkip ∷ s) = ifStackConsis s
ifStackConsis (ifIgnore ∷ s) = isNonActiveIfStack s ∧b ifStackConsis s

IfStackConsis : IfStack → Set
IfStackConsis s = True (ifStackConsis s)





lemmaIfStackConsisTail : (x : IfStackEl)(s : IfStack) → IfStackConsis (x ∷ s)
                         → IfStackConsis s
lemmaIfStackConsisTail ifCase s p = ∧bproj₂ p
lemmaIfStackConsisTail elseCase s p = ∧bproj₂ p
lemmaIfStackConsisTail ifSkip s p = ∧bproj₂ p
lemmaIfStackConsisTail elseSkip s p = p
lemmaIfStackConsisTail ifIgnore s p = ∧bproj₂ p

