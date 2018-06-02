module GUI.LoadAllPODS4H where

-- this file loads the files containing the code examples in the
-- PODS4H'18 paper of Stephan Adelsberger, Claudio Di Ciccio,
--     Michael Gottsauner-Wolf, Vadim Savenkov,
--     Anton Setzer, Mark Warner

-- Abstract
-- 1. Introduction
-- 2. Case Study
-- 3. Appproach
-- 3.1 Implementation Overview
-- 3.2 NOAC Prescription Specification in Agda

-- Agda code defining Process

open import GUI.BusinessProcessVers3Paper

-- Agda code defining discharge, naiveDoseSelection

open import GUI.BusinessProcessMedExVers6Paper

-- Agda code defining enterWeight etc  (same file)

open import GUI.BusinessProcessMedExVers6Paper

-- Agda code defining theoremWarfarin

open import GUI.BusinessProcessMedExVers7VerifUsingDecPaper


-- Full version simple (no check functions for user input, no
--                      button for going back to beginning at the end
--                      easier to understand

-- code for example
open import GUI.BusinessProcessMedExVers7Example
-- verification of example
open import GUI.BusinessProcessMedExVers7VerifUsingDec
-- compiled code compile using agda->Compile chooose GHC as backend
open import GUI.BusinessProcessMedExVers7Compiled



-- Full version with check functions for examples:

-- code for example
open import GUI.BusinessProcessMedExVers9Example
-- verification of example
open import GUI.BusinessProcessMedExVers9VerifUsingDec
-- compiled code compile using agda->Compile chooose GHC as backend
open import GUI.BusinessProcessMedExVers9Compiled


-- Full version with check functions for examples and
--    going back button at the end

-- code for example
open import GUI.BusinessProcessMedExVers10Example
-- compiled code compile using agda->Compile chooose GHC as backend
open import GUI.BusinessProcessMedExVers10Compiled

-- 4. Evaluation and Future Work
-- 5. Related Work
-- 6. Conclusion
--
