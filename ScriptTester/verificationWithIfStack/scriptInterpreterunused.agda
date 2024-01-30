--we don not need this file

open import basicBitcoinDataType

module verificationWithIfStack.scriptInterpreter (param : GlobalParameters) where

open import Data.Nat  hiding (_≤_)
open import Data.List hiding (_++_)
open import Data.Unit 
open import Data.Empty
open import Data.Bool  hiding (_≤_ ; if_then_else_ ) renaming (_∧_ to _∧b_ ; _∨_ to _∨b_ ; T to True)
open import Data.Product renaming (_,_ to _,,_ )
open import Data.Nat.Base hiding (_≤_)
open import Data.List.NonEmpty hiding (head)
open import Data.Maybe

open import libraries.listLib
open import libraries.natLib
open import libraries.boolLib
open import libraries.andLib
open import libraries.maybeLib

open import stack
open import instruction
open import ledger param
open import semanticBasicOperations param


open import verificationWithIfStack.ifStack
open import verificationWithIfStack.state
open import verificationWithIfStack.predicate
open import verificationWithIfStack.stackXIfStack param
-- open import verificationWithIfStack.semanticsInstructions hiding (executeOpIfBasic ; executeOpElseBasic ; executeOpEndIfBasic )

{-  This is an interpreter which is defined differently from the semantics
    it probably works in accordance with it, but this is not carefully checked

    so in verifications this file should not be used - it would be better to
    write an interpreter using directly the semantics

-}


------------------------------------------------------------------------------------------------

----lifting function for opEqual
executeStackEquality1 : StackXIfStack → Maybe StackXIfStack
executeStackEquality1  = liftToMaybeStack2 executeStackEquality

executeStackVerify1 : Maybe Stack → Bool
executeStackVerify1 nothing = false
executeStackVerify1 (just []) = false
executeStackVerify1 (just (zero ∷ x₁)) = false
executeStackVerify1 (just (suc x ∷ x₁)) = true

-- lifting function for opVerify
executeStackVerify2 : StackXIfStack → Maybe StackXIfStack
executeStackVerify2  = liftToMaybeStack2 executeStackVerify

-- lifting function for opCheckSig
executeStackCheckSig1 :  Msg →  StackXIfStack  → Maybe  StackXIfStack
executeStackCheckSig1  = liftToMaybeStack3 executeStackCheckSig


-- lifting function for opCheckSig3
executeStackCheckSig3 :  Msg →  StackXIfStack  → Maybe  StackXIfStack
executeStackCheckSig3  = liftToMaybeStack3 executeStackCheckSig3Aux


-- lifting function for opHash
executeHash1 :  StackXIfStack  → Maybe  StackXIfStack
executeHash1  = liftToMaybeStack2 executeOpHash


executeMultiSig1 :  Msg →  StackXIfStack  → Maybe  StackXIfStack
executeMultiSig1  = liftToMaybeStack3 executeMultiSig

-- lifting function for opSwap
executeStackSwap1 : StackXIfStack → Maybe StackXIfStack
executeStackSwap1  = liftToMaybeStack2 executeStackSwap


--lifting function for opAdd
executeStackAdd1 : StackXIfStack → Maybe  StackXIfStack
executeStackAdd1 = liftToMaybeStack2 executeStackAdd



--lifting function for opSub
executeStackSub1 :  StackXIfStack → Maybe  StackXIfStack
executeStackSub1 = liftToMaybeStack2 executeStackSub


--lifting function for opDup
executeStackDup1 : StackXIfStack → Maybe  StackXIfStack
executeStackDup1  = liftToMaybeStack2 executeStackDup


--lifting function for opDrop
executeStackDrop2 : StackXIfStack → Maybe StackXIfStack
executeStackDrop2  = liftToMaybeStack2 executeStackDrop




--lifting function for opPsuh
executeStackPush1 :  ℕ →  StackXIfStack → Maybe StackXIfStack
executeStackPush1 n  =  liftToMaybeStack2 (executeStackPush n)


executeHash : StackXIfStack → Maybe StackXIfStack -- State →  Maybe State
executeHash = liftToMaybeStack2  executeOpHash
-- executeHash st = exeTransformerDepIfStack (liftFromMsgToStateAssumeIfStack executeOpHash) st

executeCheckSig : State →  Maybe State
executeCheckSig  st = exeTransformerDepIfStack (liftFromMsgToStateAssumeIfStack executeStackCheckSig ) st

executeCheckSig3 : State →  Maybe State
executeCheckSig3  st = exeTransformerDepIfStack (liftFromMsgToStateAssumeIfStack executeStackCheckSig3Aux ) st



-- function that executes all the instructions
executeInstructionsAux3 : Time → Msg →  InstructionAll → StackXIfStack → Maybe   StackXIfStack
executeInstructionsAux3 time m opSub s =  executeStackSub1 s
executeInstructionsAux3 time m opAdd s =  executeStackAdd1 s
executeInstructionsAux3 time m opDup s =  executeStackDup1 s
executeInstructionsAux3 time m opDrop  s =   executeStackDrop2 s
executeInstructionsAux3 time m opVerify s =  executeStackVerify2 s
executeInstructionsAux3 time m opSwap  s =   executeStackSwap1 s
executeInstructionsAux3 time m opEqual s = executeStackEquality1 s
executeInstructionsAux3 time m (opPush x) s =( executeStackPush1 x) s
executeInstructionsAux3 time m opCheckSig s =  executeStackCheckSig1 m s
executeInstructionsAux3 time m opCheckSig3 s =  executeStackCheckSig3 m  s
executeInstructionsAux3 time m  opCHECKLOCKTIMEVERIFY  s =  executeOpCHECKLOCKTIMEVERIFY1 time  s
executeInstructionsAux3 time m opEqualVerify s = liftToMaybeStack1   executeStackVerify2  (executeStackEquality1 s)
executeInstructionsAux3 time m opHash s = executeHash1 s
executeInstructionsAux3 time m opMultiSig s = executeMultiSig1 m s

--here the opIf is defined and executed
executeInstructionsAux3 time m opIf s = executeOpIfBasic s

--here the opElse is defined and executed
executeInstructionsAux3 time m opElse s =  executeOpElseBasic s

--here the opEndif is defined and executed
executeInstructionsAux3 time m opEndIf s = executeOpEndIfBasic s




--auxiliary function for  executing  the instructions by constructing a list
executeInstructionAuxAll : Time → Msg → BitcoinScript → Maybe StackXIfStack → Maybe StackXIfStack
executeInstructionAuxAll time m [] s = s
executeInstructionAuxAll time m (y ∷ i) nothing = nothing
executeInstructionAuxAll time m (y ∷ i) (just y1) =  executeInstructionAuxAll time m i (executeInstructionsAux3 time m y y1)


--function that executes the list of instructions
executeInstructionsAuxAll :  Time → Msg → BitcoinScript → Maybe StackXIfStack → Maybe StackXIfStack
executeInstructionsAuxAll time m i nothing = nothing
executeInstructionsAuxAll time m i (just x) = executeInstructionAuxAll time m i (just x)

--function that executes the list of instructions with an empty start (stack is empty at the begining)
executeInstructionsAuxAllEmptyStart :  Time → Msg → BitcoinScript  → Maybe StackXIfStack
executeInstructionsAuxAllEmptyStart time m i  = executeInstructionAuxAll time m i (just ⟨ [] , [] , tt ⟩)


--function that interprets how the instructions are ran
checkContract : Time → Msg →   BitcoinScript → Bool
checkContract time m  l  =  checkStackXIfStack  (executeInstructionsAuxAllEmptyStart time m l)

--function that checks if the amount recived is less than the amount in the ledger, also checks if the concatenation of the input script and output script triggers errors
checkTXNewAux : Time → ℕ → ℕ → List InstructionAll →  Maybe  ledgerEntryNew →  Maybe  ledgerEntryNew  → Bool
checkTXNewAux time id amountRecived scriptSig nothing nothing = false
checkTXNewAux time id amountRecived scriptSig nothing (just x) = false
checkTXNewAux time id amountRecived scriptSig (just (ledgerEntrNew scriptPubKey amountInLedger))
                            nothing =  amountRecived  ≤b  amountInLedger
                                       ∧b checkContract time (nat id) (scriptSig ++ scriptPubKey)
checkTXNewAux time id amountRecived scriptSig (just (ledgerEntrNew scriptPubKey amountInLedger)) (just x) = false

-- function that outputs the outcome of a transaction ( succesful/not successful)
checkTXNew : transactionNew → LedgerNew → Bool
checkTXNew (transactNew id (txentryNew amou smartConIn addr)
           (txentryNew amount₁ smartContract₁ address₁))
           ledgerNew
     = checkTXNewAux (ledgerNew .currentTime) id amou smartConIn
                     (ledgerNew .entries addr) (ledgerNew .entries address₁)



--auxiliary  function used for outputing the stack after proccessing
runTXNewAux : Time → ℕ → ℕ → List InstructionAll →  Maybe  ledgerEntryNew →   Maybe StackXIfStack
runTXNewAux time id amountRecived scriptSig nothing = nothing
runTXNewAux time id amountRecived scriptSig
            (just (ledgerEntrNew scriptPubKey amountInLedger))
            = executeInstructionsAuxAllEmptyStart time (nat id) (scriptSig ++ scriptPubKey )

--function that outputs the stack after has been proccesed
runTXNew : transactionNew → LedgerNew →  Maybe StackXIfStack
runTXNew ( transactNew id ( txentryNew amou smartConIn addr ) output )
         ledgerNew
         = runTXNewAux (ledgerNew .currentTime) id  amou  smartConIn ( ledgerNew .entries addr)
