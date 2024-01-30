module verificationWithIfStack.ifStack where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit  
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
--open import libraries.miscLib
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

isNonActiveIfStackEl : IfStackEl → Bool
isNonActiveIfStackEl s = not (isActiveIfStackEl s)

IsNonActiveIfStackEl : IfStackEl → Set
IsNonActiveIfStackEl s = True  (isNonActiveIfStackEl s)



isActiveIfStack : IfStack → Bool
isActiveIfStack [] = true
isActiveIfStack (x ∷ s) = isActiveIfStackEl x

IsActiveIfStack : IfStack → Set
IsActiveIfStack s = True (isActiveIfStack s)



isNonActiveIfStack : IfStack → Bool
isNonActiveIfStack s =  not (isActiveIfStack s)

IsNonActiveIfStack : IfStack → Set
IsNonActiveIfStack s = True (isNonActiveIfStack s)

--from addition1 -- NEEDS REPLACEMENT
ifStackElIsNonIfIgnore : IfStackEl → Bool
ifStackElIsNonIfIgnore ifIgnore = false
ifStackElIsNonIfIgnore s  = true


--from addition1
IfStackIsNonIfIgnore : IfStackEl → Set
IfStackIsNonIfIgnore s = True (ifStackElIsNonIfIgnore s)

--from addition1
ifStackElIsIfSkipOrElseSkip : IfStackEl → Bool
ifStackElIsIfSkipOrElseSkip ifSkip = true
ifStackElIsIfSkipOrElseSkip elseSkip = true
ifStackElIsIfSkipOrElseSkip s = false
--from addition1
IfStackElIsIfSkipOrElseSkip : IfStackEl → Set
IfStackElIsIfSkipOrElseSkip s = True (ifStackElIsIfSkipOrElseSkip s)
--from addition1



-- predicate expressing that an ifStackElement is such that any operation should be executed
--   i.e.   it is  one of
--   ifCase, elseCase




-- predicate expressing that an ifStackElement is one of
--   ifSkip, ifIgnore
-- these are the skip cases which could happen if coming from the left
-- after having passed ⊥h the opEndIf and opElse
-- after having passed an opEndIf coming from the right
--           we know the top element of the ifStack is any element
-- after having then passed an opElse coming from the right
--           we know the top element of the ifStack can only be
-- as a do element   a          ifCase
-- as a skip element one of     ifSkip, ifIgnore
ifStackElementIsIfSkipOrIfIgnore : IfStackEl → Set
ifStackElementIsIfSkipOrIfIgnore ifSkip   = ⊤
ifStackElementIsIfSkipOrIfIgnore ifIgnore = ⊤
ifStackElementIsIfSkipOrIfIgnore ifCase   = ⊥
ifStackElementIsIfSkipOrIfIgnore elseCase = ⊥
ifStackElementIsIfSkipOrIfIgnore elseSkip = ⊥




ifStackConsis : IfStack → Bool
ifStackConsis [] = true
ifStackConsis (ifCase ∷ s) = isActiveIfStack s ∧b ifStackConsis s
ifStackConsis (elseCase ∷ s) = isActiveIfStack s ∧b ifStackConsis s
ifStackConsis (ifSkip ∷ s) = isActiveIfStack s ∧b ifStackConsis s
ifStackConsis (elseSkip ∷ s) = ifStackConsis s
ifStackConsis (ifIgnore ∷ s) = isNonActiveIfStack s ∧b ifStackConsis s

IfStackConsis : IfStack → Set
IfStackConsis s = True (ifStackConsis s)



ifStackElementIsElseSkipOrIfIgnore : IfStackEl → Set
ifStackElementIsElseSkipOrIfIgnore ifIgnore = ⊤
ifStackElementIsElseSkipOrIfIgnore elseSkip = ⊤
ifStackElementIsElseSkipOrIfIgnore ifSkip   = ⊥
ifStackElementIsElseSkipOrIfIgnore ifCase   = ⊥
ifStackElementIsElseSkipOrIfIgnore elseCase = ⊥


lemmaIfStackIsNonIfIgnore : (x : IfStackEl)(l : IfStack) → IfStackConsis (x ∷ l)
                           → IsActiveIfStack l 
                           → IfStackIsNonIfIgnore x
lemmaIfStackIsNonIfIgnore ifCase l c a = tt
lemmaIfStackIsNonIfIgnore elseCase l c a = tt
lemmaIfStackIsNonIfIgnore ifSkip l c a = tt
lemmaIfStackIsNonIfIgnore elseSkip l c a = tt
lemmaIfStackIsNonIfIgnore ifIgnore (ifCase ∷ l) () a
lemmaIfStackIsNonIfIgnore ifIgnore (elseCase ∷ l) () a
lemmaIfStackIsNonIfIgnore ifIgnore (ifSkip ∷ l) c ()
lemmaIfStackIsNonIfIgnore ifIgnore (elseSkip ∷ l) c ()
lemmaIfStackIsNonIfIgnore ifIgnore (ifIgnore ∷ l) c ()


lemmaIfStackConsisTail : (x : IfStackEl)(s : IfStack) → IfStackConsis (x ∷ s)
                         → IfStackConsis s
lemmaIfStackConsisTail ifCase s p = ∧bproj₂ p
lemmaIfStackConsisTail elseCase s p = ∧bproj₂ p
lemmaIfStackConsisTail ifSkip s p = ∧bproj₂ p
lemmaIfStackConsisTail elseSkip s p = p
lemmaIfStackConsisTail ifIgnore s p = ∧bproj₂ p

lemmaIfStackConsisNonActiveIf : (s : IfStack) → IfStackConsis s → IsActiveIfStack s
                                → IsActiveIfStack (ifCase ∷ s)
lemmaIfStackConsisNonActiveIf s consis  active = tt

lemmaIfStackConsisNonActiveElse : (s : IfStack) → IfStackConsis s → IsActiveIfStack s
                                → IsActiveIfStack (elseCase ∷ s)
lemmaIfStackConsisNonActiveElse s consis  active = tt


lemmaIfStackElIsIfSkipOrElseSkip2IsSkip : (x : IfStackEl)
    → True (ifStackElIsIfSkipOrElseSkip x)
    → IsNonActiveIfStackEl x
lemmaIfStackElIsIfSkipOrElseSkip2IsSkip ifSkip p = p
lemmaIfStackElIsIfSkipOrElseSkip2IsSkip elseSkip p = p
