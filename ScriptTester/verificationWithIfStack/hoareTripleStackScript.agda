open import basicBitcoinDataType

module verificationWithIfStack.hoareTripleStackScript (param : GlobalParameters) where


open import Data.List.Base hiding (_++_)
open import Data.Nat  renaming (_≤_ to _≤'_ ; _<_ to _<'_)
open import Data.List hiding (_++_)
open import Data.Sum
open import Data.Unit  
open import Data.Empty
open import Data.Maybe
open import Data.Bool  hiding (_≤_ ; _<_ ; if_then_else_  )  renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_ ; _<_)
open import Data.List.NonEmpty hiding (head)
open import Data.Nat using (ℕ; _+_; _≥_; _>_; zero; suc; s≤s; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; module ≡-Reasoning; sym)
open ≡-Reasoning
open import Agda.Builtin.Equality
--open import Agda.Builtin.Equality.Rewrite

open import libraries.listLib
open import libraries.emptyLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.equalityLib
open import libraries.andLib

open import libraries.maybeLib

open import stack
open import stackPredicate
open import instruction
-- open import ledger param
open import stackSemanticsInstructions param
open import hoareTripleStack param

open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.semanticsInstructions param
open import verificationWithIfStack.stackSemanticsInstructionsLemma param
open import verificationWithIfStack.verificationLemmas param
open import verificationWithIfStack.hoareTriple param
open import verificationWithIfStack.hoareTripleStack2HoareTriple param
open import verificationWithIfStack.hoareTripleStackNonActiveIfStack param





lemmaStackSemIsSemScriptaux2 : (g' : Time → Msg → Stack → Maybe Stack)
                             (st : State) (mst : Maybe Stack)
   → (exeTransformerDepIfStack'  (liftStackToStateTransformerAux' mst )  st
       >>= λ s →  exeTransformerDepIfStack'
                    (liftStackToStateTransformerAux'
                    (g' (s .currentTime) (s .msg) (s .stack))) s)

      ≡
      exeTransformerDepIfStack'  (liftStackToStateTransformerAux'
             (mst >>= g' (st .currentTime) (st .msg))  ) st
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , [] , consis₁ ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ ifStack₁ , consis₁ ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , elseCase ∷ ifStack₁ , consis₁ ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , consis₁ ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , consis₁ ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , consis₁ ⟩ (just x) = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , [] , consis₁ ⟩ nothing = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ ifStack₁ , consis₁ ⟩ nothing = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , elseCase ∷ ifStack₁ , consis₁ ⟩ nothing = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , consis₁ ⟩ nothing = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , consis₁ ⟩ nothing = refl
lemmaStackSemIsSemScriptaux2 g' ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , consis₁ ⟩ nothing = refl


lemmaStackSemIsSemScriptaux : (f g : State → Maybe State)
                             (f' g' : Time → Msg → Stack → Maybe Stack)
                             (p : (s : State) → f s ≡ stackTransform2StateTransform f' s)
                             (q : (s : State) → g s ≡ stackTransform2StateTransform g' s)
                             (st : State)
                             →
              (f st >>= g)   ≡ stackTransform2StateTransform
                                   (λ time₁ msg stack₁ → (f' time₁ msg stack₁ >>= g' time₁ msg) )
                                   st
lemmaStackSemIsSemScriptaux f g f' g' p q st =
    (f st >>= g)
       ≡⟨ cong (λ x → x >>= g) (p st)  ⟩
    (stackTransform2StateTransform f' st >>= g )
       ≡⟨ lemmaEqualLift2Maybe g (stackTransform2StateTransform g' ) q (stackTransform2StateTransform f' st)  ⟩
    (stackTransform2StateTransform f' st >>= stackTransform2StateTransform g')
       ≡⟨⟩
     (exeTransformerDepIfStack'
         (liftStackToStateTransformerAux'  (f' (st .currentTime) (st .msg) (st .stack)))  st
        >>=
        λ s →   exeTransformerDepIfStack'
            (liftStackToStateTransformerAux'  (g' (s .currentTime) (s .msg) (s .stack))) s)

       ≡⟨ lemmaStackSemIsSemScriptaux2 g' st (f' (st .currentTime) (st .msg) (st .stack))  ⟩
    exeTransformerDepIfStack'
  (liftStackToStateTransformerAux'
   (f' (st .currentTime) (st .msg) (st .stack) >>= g' (st .currentTime) (st .msg)))  st  ∎



lemmaStackSemIsSemScript : (prog : BitcoinScript) (nonIfs : NonIfScript prog)
                           (state₁ : State)
                          → ⟦ prog ⟧ state₁  ≡ stackTransform2StateTransform ⟦ prog ⟧stack state₁
lemmaStackSemIsSemScript [] nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , [] , consis₁ ⟩ = refl
lemmaStackSemIsSemScript [] nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , ifCase ∷ ifStack₁ , consis₁ ⟩ = refl
lemmaStackSemIsSemScript [] nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , elseCase ∷ ifStack₁ , consis₁ ⟩ = refl
lemmaStackSemIsSemScript [] nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , ifSkip ∷ ifStack₁ , consis₁ ⟩ = refl
lemmaStackSemIsSemScript [] nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , elseSkip ∷ ifStack₁ , consis₁ ⟩ = refl
lemmaStackSemIsSemScript [] nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , ifIgnore ∷ ifStack₁ , consis₁ ⟩ = refl
lemmaStackSemIsSemScript (op ∷ []) nonIfs state1 rewrite lemmaStackSemIsSemantics op (nonIfScript2NonIf2Head op [] nonIfs )  = refl
lemmaStackSemIsSemScript (op ∷ rest@(x₁ ∷ prog)) nonIfs ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩ =
       (⟦ op ⟧s ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩ >>= ⟦ rest ⟧)
          ≡⟨ cong (λ x → (x ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩ >>= ⟦ rest ⟧ ))
                  (lemmaStackSemIsSemantics op (nonIfScript2NonIf2Head op rest nonIfs))  ⟩
       (stackTransform2StateTransform ⟦ op ⟧stacks  ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩
         >>= ⟦ rest ⟧)

          ≡⟨ lemmaEqualLift2Maybe  ⟦ rest ⟧  (stackTransform2StateTransform ⟦ rest ⟧stack )
            (lemmaStackSemIsSemScript rest (nonIfScript2NonIf2Tail op rest nonIfs))
            ((stackTransform2StateTransform ⟦ op ⟧stacks  ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩)) ⟩
       (stackTransform2StateTransform ⟦ op ⟧stacks  ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩
            >>= stackTransform2StateTransform ⟦ rest ⟧stack)
                ≡⟨ lemmaStackSemIsSemScriptaux2 ⟦ x₁ ∷ prog ⟧stack ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩
                   (⟦ op ⟧stacks currentTime₁ msg₁ stack₁) ⟩
      exeTransformerDepIfStack'
      (liftStackToStateTransformerAux'
       (⟦ op ⟧stacks currentTime₁ msg₁ stack₁ >>= ⟦ rest ⟧stack currentTime₁ msg₁))
      ⟨ currentTime₁ , msg₁ , stack₁ , ifstack₁ , consis₁ ⟩
    ∎









lemmaNonIfInstrGenericCondImpliesTripleaux' :
          (prog : BitcoinScript)(nonIf : NonIfScript prog)
          (φ ψ : Predicate)
          → < φ >gen stackTransform2StateTransform ⟦  prog  ⟧stack < ψ >
          → < φ >gen ⟦ prog ⟧ < ψ >
lemmaNonIfInstrGenericCondImpliesTripleaux' prog nonIf φ ψ x
    = lemmaTransferHoareTripleGen φ ψ (stackTransform2StateTransform ⟦  prog  ⟧stack) ⟦ prog ⟧
      (λ s → sym (lemmaStackSemIsSemScript prog nonIf ⟨ currentTime s , msg s , stack s , ifStack s , consis s ⟩)) x







lemmaGenericHoareTripleImpliesHoareTripleProg : (prog : BitcoinScript)
                                            (φ ψ : Predicate)
                                            → < φ >gen ⟦ prog ⟧ <  ψ >
                                            → < φ >ⁱᶠᶠ prog < ψ >
lemmaGenericHoareTripleImpliesHoareTripleProg prog φ ψ (hoareTripleGen ==>g₁ <==g₁) .==> = ==>g₁
lemmaGenericHoareTripleImpliesHoareTripleProg prog φ ψ (hoareTripleGen ==>g₁ <==g₁) .<== = <==g₁

lemmaNonIfInstrGenericCondImpliesTripleauxProg :
          (prog : BitcoinScript)(nonIf : NonIfScript prog)
          (φ ψ : Predicate)
          → < φ >gen stackTransform2StateTransform ⟦ prog ⟧stack < ψ >
          → < φ >gen ⟦ prog ⟧ < ψ >
lemmaNonIfInstrGenericCondImpliesTripleauxProg prog nonIf φ ψ x =
    lemmaTransferHoareTripleGen φ ψ
      (stackTransform2StateTransform ⟦ prog ⟧stack) ⟦ prog ⟧
      (λ s → sym (lemmaStackSemIsSemScript prog nonIf s)) x



hoareTripleStack2HoareTripleIfStack :
     (ifStack₁ : IfStack)
     (active : IsActiveIfStack ifStack₁)
     (prog : BitcoinScript)
     (nonIf : NonIfScript prog)
     (φ ψ : StackPredicate)
     → < φ >stack prog < ψ >
     → < liftStackPred2Pred φ ifStack₁  >ⁱᶠᶠ prog < liftStackPred2Pred ψ ifStack₁   >
hoareTripleStack2HoareTripleIfStack ifStack₁ active prog nonIf φ ψ x
   = lemmaGenericHoareTripleImpliesHoareTripleProg prog (liftStackPred2Pred φ ifStack₁) (liftStackPred2Pred ψ ifStack₁)
     (lemmaNonIfInstrGenericCondImpliesTripleauxProg prog nonIf (liftStackPred2Pred φ ifStack₁) (liftStackPred2Pred ψ ifStack₁)
     (lemmaHoareTripleStackPartToHoareTripleGeneric ⟦ prog ⟧stack ifStack₁ active φ  ψ
     x))



hoareTripleNonActiveIfStackIgnored :
     (ifStack₁ : IfStack)
     (nonactive : IsNonActiveIfStack ifStack₁)
     (instr : BitcoinScript)
     (nonIf : NonIfScript instr)
     (φ : StackPredicate)
     → < liftStackPred2Pred φ ifStack₁  >ⁱᶠᶠ instr  < liftStackPred2Pred φ ifStack₁  >
hoareTripleNonActiveIfStackIgnored ifStack₁ nonactive instr nonIf φ
   =  lemmaGenericHoareTripleImpliesHoareTriple'' instr
   (liftStackPred2Pred φ ifStack₁) (liftStackPred2Pred φ ifStack₁)
   (lemmaNonIfInstrGenericCondImpliesTripleaux' instr nonIf (liftStackPred2Pred φ ifStack₁)
   (liftStackPred2Pred φ ifStack₁)
   (lemmaHoareTripleStackPartToHoareTripleNonActiveGeneric ifStack₁ nonactive φ ⟦ instr ⟧stack))




