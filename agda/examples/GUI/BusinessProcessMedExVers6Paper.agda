-- \BusinessProcessMedExVersSixPaper

module GUI.BusinessProcessMedExVers6Paper   where

-- Variant of BusinessProcessMedExVers3.agda
-- but using GUIDefinitionsVers2.agda--
-- This file is almost identical to BusinessProcessMedExVers5.agda
--    probably thought that BusinessProcessMedExVers5.agda was based on
--    BusinessProcessMedExVers2.agda

open import Data.Fin renaming (_+_ to _+fin_)
open import Data.Nat
open import Data.Empty
open import Data.List renaming (map to mapL)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Size
open import Data.Unit
open import Data.String renaming (_==_ to _==Str_)
open import Data.String

open import heap.libraryVec
open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ) renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
open import GUI.GUIDefinitionsVers2
open import GUI.GUIModelVers3 renaming (GuiState to State)
open import GUI.GUIExampleVers2
open import GUI.GUIExampleLibVers2
open import GUI.BusinessProcessVers3Paper
open import GUI.BusinessProcessMedExLib

open import SizedIO.Base hiding (_>>_)
open import SizedIO.Console hiding (main)


-- open import GUI.GUIExampleLib



discharge : Process
lowdoseSelection  : Process
highdoseSelection  : Process
naiveDoseSelection  : Process

-- \BusinessProcessMedExVersSixPaper
discharge           =  endEvent   "Discharge Patient"
naiveDoseSelection  =  xor  ("Low Dose"  , discharge) ("High Dose" , discharge)

lowdoseSelection   =  activity  "Low Dose"   discharge
highdoseSelection  =  activity  "High Dose"  discharge


patientHistory : Weight → Process
patientHistory w = endEvent "process used only for presentation in paper"



-- \BusinessProcessMedExVersSixPaper
mutual
  enterWeight : Process
  enterWeight = unaryInput "Enter patient weight"
                λ string  →  patientHistory (str2Weight string)

  NOACprescriptionA : Weight → Process
  NOACprescriptionA w = activity "Prescribe Apixaban" (doseSelectionA w)

  doseSelectionA : Weight → Process
  doseSelectionA ≤60 = lowdoseSelection
  doseSelectionA >60 = highdoseSelection

-- \Process
doseSelection¬A :  RenalCat≥30  →  AgeCat
                   → Process
doseSelection¬A  ≥30<50  <75  =  lowdoseSelection
doseSelection¬A  ≥50     <75  =  highdoseSelection
doseSelection¬A  r       ≥75  =  lowdoseSelection

-- Note above that RenalCat is always ≥30 (use of type RenalCat≥30)


NOACprescriptionD : RenalCat≥30 →  AgeCat → Process
NOACprescriptionD r a = activity "Med D" (doseSelection¬A r a)

-- \Process
NOACprescriptionAll : RenalCat≥30 →  AgeCat →  Weight → Process
NOACprescriptionAll r a w = xor ("Med A" , doseSelectionA   w)
                             ("Med D" , doseSelection¬A  r a)


warfarin : Process
warfarin  = activity "Prescribe warfarin"  discharge


medSelection : FallRisk → RenalCat → AgeCat → Weight → Process
medSelection any         <25     a w = warfarin
medSelection fallRisk    ≥25<30  a w = warfarin
medSelection fallRisk    ≥30<50  a w = NOACprescriptionD    ≥30<50  a
medSelection fallRisk    ≥50     a w = NOACprescriptionD    ≥50     a
medSelection noFallRisk  ≥25<30  a w = NOACprescriptionA    w
medSelection noFallRisk  ≥30<50  a w = NOACprescriptionAll  ≥30<50  a w
medSelection noFallRisk  ≥50     a w = NOACprescriptionAll  ≥50     a w

medicationSelection = medSelection

mdChoice : FallRisk → RenalCat → AgeCat → Weight → Process
mdChoice  f r a w = activity "MD Choice"
                     (medSelection f r a w)

diagnosis : FallRisk → RenalCat → AgeCat → Weight → Process
diagnosis f r a w =  activity "Diagnosis"
                    (activity "MD Choice"
                    (medSelection f r a w))


-- \Process
bloodTestRes :  FallRisk → AgeCat → Weight → Process
bloodTestRes f a w =
    unaryInput "Enter Bloodtest Result"  λ str →
    diagnosis f (str2RenalCat str ) a w

drawBlood : FallRisk → AgeCat → Weight → Process
drawBlood f a w = activity "Draw Blood" (bloodTestRes f a w)

patientHistory' : AgeCat → Weight → Process
patientHistory' a w =  input {2}  ("Enter fall/accident risk",
                                "Enter CHA2DS2-VASc-Score")
                                λ {(strFallR , strScore) →
                      drawBlood (patientHist2FallRisk strFallR) a w}

-- \Process
patientRegistration : Process
patientRegistration = input {2} ("Enter patient age" , "Enter Wght")
                                 λ {(strAge , strWght)  →
                                     patientHistory' (str2AgeCat strAge) (str2Weight strWght)}



-- \ProcessMedExVersThree
patientRegistrationGUI : GUI
patientRegistrationGUI = process2GUI patientRegistration


{- We define some states -}

--- BEGIN@ProcesstoState
-- process2State : Process → State
-- process2State b
--    = state (process2GUI b) notStarted
---END


dischargeState : State
dischargeState = process2State discharge

patientRegistrationState : State
patientRegistrationState = process2State patientRegistration

-- \BusinessProcessMedExVersSixPaper
NOACprescriptionAState : Weight → State
NOACprescriptionAState w = process2State (NOACprescriptionA w)

NOACprescriptionDState : RenalCat≥30 → AgeCat → State
NOACprescriptionDState r a = process2State (NOACprescriptionD r a)


warfarinState : State
warfarinState = process2State warfarin

medSelectionState : FallRisk → RenalCat → AgeCat → Weight → State
medSelectionState f r a w = process2State (medSelection f r a w)

mdChoiceState : FallRisk → RenalCat → AgeCat → Weight → State
mdChoiceState f r a w = process2State (mdChoice f r a w)

diagnosisState : FallRisk → RenalCat → AgeCat → Weight → State
diagnosisState f r a w = process2State (diagnosis f r a w)

{- *** here we have the state after all inputs *** -}


-- \Process
stateAfterBloodTest : (strAge strWght strFallR strScore strBlood : String) → State
stateAfterBloodTest  strAge strWght strFallR strScore strBlood
                     =  guiNexts
                        patientRegistrationState
                        (nilCmd
                         >>>    textboxInput2  strAge  strWght
                         >>>    textboxInput2  strFallR strScore
                         >>>    btnClick
                         >>>    textboxInput   strBlood)

{- we show that if the renalvalue was for category <25 then we will reach the
   state where warfarin is prescribed -}

-- \Process
theoremWarfarinAux :  (f : FallRisk)(r : RenalCat)(a : AgeCat)(w : Weight)
                      →  r ≡ <25
                      →  diagnosisState f r a w -eventually-> warfarinState
theoremWarfarinAux r .<25 a w refl =
      next (λ _ → next (λ _ → hasReached))



-- \Process
theoremWarfarin : (strAge strWght strFallR strScore strBlood : String)
      →  str2RenalCat strBlood ≡ <25
      →  stateAfterBloodTest strAge strWght strFallR strScore strBlood
          -eventually-> warfarinState
theoremWarfarin strAge strWght strFallR strScore strBlood  =
    theoremWarfarinAux (patientHist2FallRisk strFallR)
    (str2RenalCat strBlood) (str2AgeCat strAge)
    (str2Weight strWght)



{- a weaker statement which says that we reach Warfarin state in 2 button clicks -}

theoremWarfarinAux' : (f : FallRisk)(r : RenalCat) (a : AgeCat)(w : Weight)
                      → r ≡ <25
                     → diagnosisState f r a w -gui-> warfarinState
theoremWarfarinAux' r .<25 a w refl = step btnClick (step btnClick refl-gui->)


theoremWarfarin' : (strAge strWght strFallR strScore strBlood : String)
                  → str2RenalCat strBlood  ≡ <25
                  → stateAfterBloodTest strAge strWght strFallR strScore strBlood
                    -gui-> warfarinState
theoremWarfarin' strAge strWght strFallR strScore strBlood  = theoremWarfarinAux' (patientHist2FallRisk strFallR)
                                                     (str2RenalCat strBlood) (str2AgeCat strAge) (str2Weight strWght)



{- We show that if the renalvalue is <25, NOAC A state will not be reached -}
-- \Process
theoremNoNOACA<25Aux : (f : FallRisk)(r : RenalCat) (a : AgeCat)(w : Weight)
                      → r ≡ <25
                      → {s : State}
                      → diagnosisState f r a w -gui-> s
                      → (w' : Weight)
                      → ¬ (s  ≡ NOACprescriptionAState w')
theoremNoNOACA<25Aux f .<25 _ _ refl refl-gui-> _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ refl-gui->) _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ (step _ refl-gui->)) _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ (step _ (step _ refl-gui->))) _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ (step _ (step _ (step (() , _) _))))


-- \Process
theoremNoNOACA<25 :
   (strAge strWght strFallR strScore strBlood : String)
   →  str2RenalCat strBlood  ≡ <25
   →  {s : State}
   →  stateAfterBloodTest  strAge strWght strFallR
                           strScore strBlood
      -gui-> s
   →  (w' : Weight)
   →  ¬ (s  ≡ NOACprescriptionAState w')
theoremNoNOACA<25 strAge strWght strFallR strScore strBlood = theoremNoNOACA<25Aux (patientHist2FallRisk strFallR)
                                                      (str2RenalCat strBlood) (str2AgeCat strAge)(str2Weight strWght)


{- We show that if the renalvalue is <25, NOAC D state will not be reached -}

theoremNoNOACD<25Aux : (f : FallRisk)(r : RenalCat) (a : AgeCat)(w : Weight)
                      → r ≡ <25
                      → {s : State}
                      → diagnosisState f r a w -gui-> s
                      → (r' : RenalCat≥30) (a' : AgeCat)
                      → ¬ (s  ≡ NOACprescriptionDState r' a')
theoremNoNOACD<25Aux f .<25 _ _ refl refl-gui-> _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ refl-gui->) _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ (step _ refl-gui->)) _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ (step _ (step _ refl-gui->))) _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ (step _ (step _ (step (() , _) _))))

theoremNoNOACD<25 : (strAge strWght strFallR strScore strBlood : String)
                   → str2RenalCat strBlood  ≡ <25
                   → {s : State}
                   → stateAfterBloodTest strAge strWght strFallR strScore strBlood -gui-> s
                   → (r' : RenalCat≥30) (a' : AgeCat)
                   → ¬ (s  ≡ NOACprescriptionDState r' a')
theoremNoNOACD<25 strAge strWght strFallR strScore strBlood = theoremNoNOACD<25Aux (patientHist2FallRisk strFallR)
                                                      (str2RenalCat strBlood) (str2AgeCat strAge)(str2Weight strWght)

{- ####
###-}
