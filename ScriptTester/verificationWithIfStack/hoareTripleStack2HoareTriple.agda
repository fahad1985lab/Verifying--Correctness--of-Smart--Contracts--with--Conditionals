open import basicBitcoinDataType

module verificationWithIfStack.hoareTripleStack2HoareTriple (param : GlobalParameters) where



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
-- open import Data.List.NonEmpty hiding (head)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite


open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib

open import libraries.maybeLib
open import libraries.emptyLib



open import stack
open import stackPredicate
open import instruction

open import stackSemanticsInstructions param


open import hoareTripleStack param


open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param




-- Proof that the generic Hoare triple implies the standard one for an instruction
lemmaGenericHoareTripleImpliesHoareTriple : (instr : InstructionAll)
                                            (φ ψ : Predicate)
                                            → < φ >gen ⟦ instr ⟧s  < ψ >
                                            → < φ >ⁱᶠᶠ [ instr ] < ψ >
lemmaGenericHoareTripleImpliesHoareTriple instr φ ψ prog .==> = prog .==>g
lemmaGenericHoareTripleImpliesHoareTriple instr φ ψ prog .<== = prog .<==g


lemmaGenericHoareTripleImpliesHoareTriple'' : (prog : BitcoinScript)
                                            (φ ψ : Predicate)
                                            → < φ >gen ⟦ prog ⟧  < ψ >
                                            → < φ >ⁱᶠᶠ prog < ψ >
lemmaGenericHoareTripleImpliesHoareTriple'' prog φ ψ prog₁ .==> = prog₁ .==>g
lemmaGenericHoareTripleImpliesHoareTriple'' prog φ ψ prog₁ .<== = prog₁ .<==g



-- intermediate step towards showing that the
--   Hoare triple of a stack function implies
--   the Hoare triple of the instruction
lemmaNonIfInstrGenericCondImpliesTripleaux :
          (instr : InstructionAll)(nonIf : NonIfInstr instr)
          (φ ψ : Predicate)
          → < φ >gen stackTransform2StateTransform ⟦ [ instr ] ⟧stack < ψ >
          → < φ >gen ⟦ instr ⟧s <  ψ >
lemmaNonIfInstrGenericCondImpliesTripleaux opEqual nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opAdd nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux (opPush x₁) nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opSub nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opVerify nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opCheckSig nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opEqualVerify nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opDup nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opDrop nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opSwap nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opHash nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opCHECKLOCKTIMEVERIFY nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opCheckSig3 nonIf φ ψ x = x
lemmaNonIfInstrGenericCondImpliesTripleaux opMultiSig nonIf φ ψ x = x



lemmaNonIfInstrGenericCondImpliesHoareTriple :
          (instr : InstructionAll)
          (nonIf : NonIfInstr instr)
          (φ ψ : Predicate)
          → < φ >gen stackTransform2StateTransform ⟦ [ instr ] ⟧stack  < ψ  >
          → < φ >ⁱᶠᶠ [ instr ]  < ψ >
lemmaNonIfInstrGenericCondImpliesHoareTriple instr nonif φ ψ p
  = lemmaGenericHoareTripleImpliesHoareTriple instr φ ψ
      (lemmaNonIfInstrGenericCondImpliesTripleaux instr nonif φ ψ p)



-- auxiliary function used for proving lemmaLift2StateCorrectnessStackFun=>
lemmaLift2StateCorrectnessStackFun=>aux : (ifStack₂ : IfStack)
 (ψ : StackPredicate)(funRes : Maybe Stack) (currentTime₁ : Time)
 (msg₁ : Msg)(consis₁ : IfStackConsis ifStack₂)
 (p : liftPred2Maybe (ψ currentTime₁ msg₁) funRes)
 →  ((λ s → ψ (currentTime s) (msg s) (stack s) ∧ (ifStack s ≡ ifStack₂)) ⁺)
   (state1WithMaybe
   ⟨ currentTime₁ , msg₁ , funRes , ifStack₂ , consis₁ ⟩)
lemmaLift2StateCorrectnessStackFun=>aux ifStack₂ ψ (just x) currentTime₁ msg₁ consis₁ p = conj p refl


-- Stack correctness implies correctness of the hoare triple
--   here direction =>
lift2StateCorrectnessStackFun=> : (ifStack₁ : IfStack)
   (active : IsActiveIfStack ifStack₁)(φ ψ : StackPredicate)
 (stackfun : StackTransformer)(stackCorrectness : (time : Time)(msg : Msg)(s : Stack)
 → φ time msg s → liftPred2Maybe (ψ time msg) (stackfun time msg s))
  (s : State) → liftStackPred2Pred φ ifStack₁  s
  → ((liftStackPred2Pred ψ ifStack₁ ) ⁺)(stackTransform2StateTransform stackfun s)
lift2StateCorrectnessStackFun=> [] active φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ , .[] , consis₁ ⟩ (conj and3 refl)
        = lemmaLift2StateCorrectnessStackFun=>aux [] ψ  (stackfun currentTime₁ msg₁ stack₁) currentTime₁ msg₁ consis₁ (stackCorrectness currentTime₁ msg₁ stack₁ and3)
lift2StateCorrectnessStackFun=> (ifCase ∷ ifs) active φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ , .(ifCase ∷ ifs) , consis₁ ⟩  (conj and3 refl)
        = lemmaLift2StateCorrectnessStackFun=>aux (ifCase ∷ ifs) ψ  (stackfun  currentTime₁ msg₁ stack₁) currentTime₁ msg₁ consis₁ (stackCorrectness currentTime₁ msg₁ stack₁ and3)
lift2StateCorrectnessStackFun=> (elseCase ∷ ifs) active φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ , .(elseCase ∷ ifs)  , consis₁ ⟩ (conj and3 refl)
        = lemmaLift2StateCorrectnessStackFun=>aux (elseCase ∷ ifs) ψ  (stackfun  currentTime₁ msg₁ stack₁) currentTime₁ msg₁ consis₁ (stackCorrectness currentTime₁ msg₁ stack₁ and3)

lemmaLift2StateCorrectnessStackFun<=aux : (ifStack₁ ifStack₂ : IfStack)
     (φ ψ : StackPredicate)
     (active : IsActiveIfStack ifStack₂)
     (funRes : Maybe Stack)
     (currentTime₁ : Time)
     (msg₁ : Msg)
     (stack₁ : Stack)
     (consis₁ : IfStackConsis ifStack₁)
     (p : ((λ s → ψ (currentTime s) (msg s) (stack s) ∧ (ifStack s ≡ ifStack₂)) ⁺)
           (exeTransformerDepIfStack'
            (liftStackToStateTransformerAux' funRes)
            ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₁ , consis₁ ⟩))
     (q : liftPred2Maybe (ψ currentTime₁ msg₁) funRes → φ currentTime₁ msg₁ stack₁)
     → φ currentTime₁ msg₁ stack₁ ∧ (ifStack₁ ≡ ifStack₂)
lemmaLift2StateCorrectnessStackFun<=aux [] .[] φ ψ active (just x) currentTime₁ msg₁ stack₁ consis₁ (conj and3 refl) q
    = conj (q and3) refl
lemmaLift2StateCorrectnessStackFun<=aux (ifCase ∷ ifStack₁) .(ifCase ∷ ifStack₁) φ ψ active (just x) currentTime₁ msg₁ stack₁ consis₁ (conj and3 refl) q
    = conj (q and3) refl
lemmaLift2StateCorrectnessStackFun<=aux (elseCase ∷ ifStack₁) .(elseCase ∷ ifStack₁) φ ψ active (just x) currentTime₁ msg₁ stack₁ consis₁ (conj and3 refl) q
   = conj (q and3) refl
lemmaLift2StateCorrectnessStackFun<=aux (ifCase ∷ ifStack₁) ifStack₂ φ ψ active nothing currentTime₁ msg₁ stack₁ consis₁ () q
lemmaLift2StateCorrectnessStackFun<=aux (elseCase ∷ ifStack₁) ifStack₂ φ ψ active nothing currentTime₁ msg₁ stack₁ consis₁ () q
lemmaLift2StateCorrectnessStackFun<=aux (ifSkip ∷ ifStack₁) .(ifSkip ∷ ifStack₁) φ ψ () (just x) currentTime₁ msg₁ stack₁ consis₁ (conj and3 refl) q
lemmaLift2StateCorrectnessStackFun<=aux (elseSkip ∷ ifStack₁) .(elseSkip ∷ ifStack₁) φ ψ () (just x) currentTime₁ msg₁ stack₁ consis₁ (conj and3 refl) q
lemmaLift2StateCorrectnessStackFun<=aux (ifIgnore ∷ ifStack₁) .(ifIgnore ∷ ifStack₁) φ ψ () (just x) currentTime₁ msg₁ stack₁ consis₁ (conj and3 refl) q


-- Stack correctness implies correctness of the hoare triple
--   here direction <=
lift2StateCorrectnessStackFun<= : (ifStack₁ : IfStack)

                                  (active : IsActiveIfStack ifStack₁)
                                  (φ ψ : StackPredicate)
                                  (stackfun : StackTransformer)(stackCorrectness : (time : Time)(msg : Msg)(s : Stack)
                                  → liftPred2Maybe (ψ time msg) (stackfun time msg s) → φ time msg s)
                                  (s : State)
                                  → ((liftStackPred2Pred ψ ifStack₁ ) ⁺)
                                                    (stackTransform2StateTransform stackfun s)
                                  → liftStackPred2Pred φ ifStack₁  s
lift2StateCorrectnessStackFun<= [] active φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₁ , consis₁ ⟩ x
  = lemmaLift2StateCorrectnessStackFun<=aux ifStack₁ []  φ ψ active (stackfun currentTime₁ msg₁  stack₁) currentTime₁ msg₁ stack₁ consis₁ x  (stackCorrectness currentTime₁ msg₁ stack₁)
lift2StateCorrectnessStackFun<= (ifCase ∷ ifStack₂) active φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₁ , consis₁ ⟩ x
  = lemmaLift2StateCorrectnessStackFun<=aux ifStack₁ (ifCase ∷ ifStack₂) φ ψ active (stackfun currentTime₁ msg₁ stack₁) currentTime₁ msg₁ stack₁ consis₁ x
         (stackCorrectness currentTime₁ msg₁ stack₁)
lift2StateCorrectnessStackFun<= (elseCase ∷ ifStack₂) active φ ψ stackfun stackCorrectness ⟨ currentTime₁ , msg₁ , stack₁ , ifStack₁ , consis₁ ⟩ x
    = lemmaLift2StateCorrectnessStackFun<=aux ifStack₁ (elseCase ∷ ifStack₂) φ ψ active (stackfun currentTime₁ msg₁ stack₁) currentTime₁ msg₁ stack₁ consis₁ x
         (stackCorrectness currentTime₁ msg₁ stack₁)


-- Correctness of the stack function implies correctness of the Hoare triple
--    here generic

lemmaHoareTripleStackPartToHoareTripleGeneric :
     (stackfun : StackTransformer)
     (ifStack₁ : IfStack)
     (active : IsActiveIfStack ifStack₁)
     (φ ψ : StackPredicate)
     → < φ >gˢ stackfun  < ψ >
     → < liftStackPred2Pred φ ifStack₁ >gen
        stackTransform2StateTransform  stackfun
       < liftStackPred2Pred ψ ifStack₁ >
lemmaHoareTripleStackPartToHoareTripleGeneric stackfun ifStack₁ active φ ψ
    (hoareTripleStackGen ==>stg₁ <==stg₁) .==>g s p
     = lift2StateCorrectnessStackFun=> ifStack₁ active φ  ψ  stackfun ==>stg₁ s p
lemmaHoareTripleStackPartToHoareTripleGeneric stackfun ifStack₁ active φ ψ
    (hoareTripleStackGen ==>stg₁ <==stg₁) .<==g s p
     = lift2StateCorrectnessStackFun<= ifStack₁ active φ  ψ  stackfun <==stg₁ s p



-- Hoare triple correctness of the stack function of an instruction
-- implies correctness of the Hoare triple for that instruction

hoartTripleStackPartImpliesHoareTriple :
     (ifStack₁ : IfStack)
     (active : IsActiveIfStack ifStack₁)
     (instr : InstructionAll)
     (nonIf : NonIfInstr instr)
     (φ ψ : StackPredicate)
     → < φ >stack [ instr ] < ψ >
     → < liftStackPred2Pred φ ifStack₁  >ⁱᶠᶠ [ instr ]  < liftStackPred2Pred ψ ifStack₁   >

hoartTripleStackPartImpliesHoareTriple ifStack₁ active instr nonIf φ ψ x
   = lemmaGenericHoareTripleImpliesHoareTriple instr
      (liftStackPred2Pred φ ifStack₁ )
      (liftStackPred2Pred ψ ifStack₁ )
      (lemmaNonIfInstrGenericCondImpliesTripleaux instr nonIf
        (liftStackPred2Pred φ ifStack₁ )
        (liftStackPred2Pred ψ ifStack₁ )
        (lemmaHoareTripleStackPartToHoareTripleGeneric
           ⟦ [ instr ] ⟧stack ifStack₁ active φ ψ x))


