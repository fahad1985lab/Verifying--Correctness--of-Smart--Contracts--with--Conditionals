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

open import verificationBitcoinScripts.state
open import verificationBitcoinScripts.semanticsInstructions param


-- Sect V Hoare Logic

open import verificationBitcoinScripts.hoareTriple param


-- Sect VI Verification Condition for Conditionals

open import verificationBitcoinScripts.predicate
open import verificationBitcoinScripts.ifStack


-- Sect VII Conclusion and Future Work





