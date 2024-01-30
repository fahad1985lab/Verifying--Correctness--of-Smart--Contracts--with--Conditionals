open import basicBitcoinDataType

module guidelines (param : GlobalParameters) where


-- This file is guidelines for the code contained in the paper.
-- The authors:  Fahad Alhabardi, Bogdan Lazar, and Anton Setzer
-- The title of the paper: Verifying Correctness of Smart Contracts with Conditionals


-- Sect I introduction
-- Sect II related work



-- Sect III Introduction to the Proof Assistant to Agda

open import instruction
open import ledger param


-- Sect IV Operational Semantics for Bitcoin Script

-- Subsect A. Bitcoin Script - the language of Bitcoin for Smart Contracts

-- Subsect B. Operational Semantics

open import verificationWithIfStack.state
open import verificationWithIfStack.ifStack 
open import verificationWithIfStack.semanticsInstructions param



-- Sect V Hoare Logic

open import verificationWithIfStack.hoareTriple param


-- Sect VI Verification Condition for Conditionals

open import verificationWithIfStack.predicate
open import verificationWithIfStack.ifStack

-- Main ifthenelse-theorem (theoremIfThenElse)
open import verificationWithIfStack.ifThenElseTheoremPart4 param
-- Sect VII Conclusion and Future Work


-- ifthenelse-non-active
open import verificationWithIfStack.ifThenElseTheoremPart8nonActive param



