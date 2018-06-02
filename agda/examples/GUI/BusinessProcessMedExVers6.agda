-- \BusinessProcessMedExVersSix

module GUI.BusinessProcessMedExVers6   where

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
open import GUI.GUIModelVers3
open import GUI.GUIExampleVers2
open import GUI.GUIExampleLibVers2
open import GUI.BusinessProcessVers3
open import GUI.BusinessProcessMedExLib

open import SizedIO.Base hiding (_>>_)
open import SizedIO.Console hiding (main)


-- open import GUI.GUIExampleLib



discharge : BusinessProcess
lowdoseSelection  : BusinessProcess
highdoseSelection  : BusinessProcess

-- \BusinessProcess
discharge          =  endEvent "Discharge Patient"
lowdoseSelection   =  activity "Low Dose"   discharge
highdoseSelection  =  activity "High Dose"  discharge

-- \BusinessProcess
doseSelectionA : Weight → BusinessProcess
doseSelectionA ≤60 = lowdoseSelection
doseSelectionA >60 = highdoseSelection

-- \BusinessProcess
doseSelection¬A :  RenalCat≥30  →  AgeCat
                   → BusinessProcess
doseSelection¬A  ≥30<50  <75  =  lowdoseSelection
doseSelection¬A  ≥50     <75  =  highdoseSelection
doseSelection¬A  r       ≥75  =  lowdoseSelection

-- Note above that RenalCat is always ≥30 (use of type RenalCat≥30)

-- \BusinessProcess
NOACSelectionA : Weight → BusinessProcess
NOACSelectionA w = activity "Med A" (doseSelectionA w)

NOACSelectionD : RenalCat≥30 →  AgeCat → BusinessProcess
NOACSelectionD r a = activity "Med D" (doseSelection¬A r a)

-- \BusinessProcess
NOACSelectionAll : RenalCat≥30 →  AgeCat →  Weight → BusinessProcess
NOACSelectionAll r a w = xor (("Med A" , doseSelectionA   w) ∷
                              ("Med D" , doseSelection¬A  r a) ∷
                              [])


warfarin : BusinessProcess
warfarin  = activity "Prescribe warfarin"  discharge


medSelection : FallRisk → RenalCat → AgeCat → Weight → BusinessProcess
medSelection any         <25     a w = warfarin
medSelection fallRisk    ≥25<30  a w = warfarin
medSelection fallRisk    ≥30<50  a w = NOACSelectionD    ≥30<50  a
medSelection fallRisk    ≥50     a w = NOACSelectionD    ≥50     a
medSelection noFallRisk  ≥25<30  a w = NOACSelectionA    w
medSelection noFallRisk  ≥30<50  a w = NOACSelectionAll  ≥30<50  a w
medSelection noFallRisk  ≥50     a w = NOACSelectionAll  ≥50     a w

medicationSelection = medSelection

mdChoice : FallRisk → RenalCat → AgeCat → Weight → BusinessProcess
mdChoice  f r a w = activity "MD Choice"
                     (medicationSelection f r a w)

diagnosis : FallRisk → RenalCat → AgeCat → Weight → BusinessProcess
diagnosis f r a w =  activity "Diagnosis"
                    (activity "MD Choice"
                    (medicationSelection f r a w))


-- \BusinessProcess
bloodTestRes :  FallRisk → AgeCat → Weight
                → BusinessProcess
bloodTestRes f a w =
    input "Enter Bloodtest Result"  λ str  →
    diagnosis f (str2RenalCat str ) a w

drawBlood : FallRisk → AgeCat → Weight → BusinessProcess
drawBlood f a w = activity "Draw Blood" (bloodTestRes f a w)

patientHistory : AgeCat → Weight → BusinessProcess
patientHistory a w =  input {2} ("Enter fall/accident risk",
                                "Enter CHA2DS2-VASc-Score")
                                λ {(strFallR , strScore) →
                      drawBlood (patientHist2FallRisk strFallR) a w}

-- \BusinessProcess
patientRegistration : BusinessProcess
patientRegistration = input {2} ("Enter patient age" , "Enter Wght")
                                 λ {(strAge , strWght)  →
                                     patientHistory (str2AgeCat strAge) (str2Weight strWght)}

-- \BusinessProcessMedExVersThree
patientRegistrationGUI : GUI
patientRegistrationGUI = businessProcess2GUI patientRegistration


{- We define some states -}
{-
-- \BusinessProcess
-
businessProcess2State : BusinessProcess → GuiState
businessProcess2State b
    = state (businessProcess2GUI b) notStarted
-
-}

dischargeState : GuiState
dischargeState = businessProcess2State discharge

patientRegistrationState : GuiState
patientRegistrationState = businessProcess2State patientRegistration


NOACSelectionAState : Weight → GuiState
NOACSelectionAState w = businessProcess2State (NOACSelectionA w)

NOACSelectionDState : RenalCat≥30 → AgeCat → GuiState
NOACSelectionDState r a = businessProcess2State (NOACSelectionD r a)


warfarinState : GuiState
warfarinState = businessProcess2State warfarin

medicationSelectionState : FallRisk → RenalCat → AgeCat → Weight → GuiState
medicationSelectionState f r a w = businessProcess2State (medicationSelection f r a w)

mdChoiceState : FallRisk → RenalCat → AgeCat → Weight → GuiState
mdChoiceState f r a w = businessProcess2State (mdChoice f r a w)

diagnosisState : FallRisk → RenalCat → AgeCat → Weight → GuiState
diagnosisState f r a w = businessProcess2State (diagnosis f r a w)

{- *** here we have the state after all inputs *** -}


-- \BusinessProcess
stateAfterBloodTest : (strAge strWght strFallR strScore strBlood : String) → GuiState
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

-- \BusinessProcess
theoremWarfarinAux :  (f : FallRisk)(r : RenalCat)(a : AgeCat)(w : Weight)
                      →  r ≡ <25
                      →  diagnosisState f r a w -eventually-> warfarinState
theoremWarfarinAux r .<25 a w refl =
      next (λ _ → next (λ _ → hasReached))



-- \BusinessProcess
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
-- \BusinessProcess
theoremNoNOACA<25Aux : (f : FallRisk)(r : RenalCat) (a : AgeCat)(w : Weight)
                      → r ≡ <25
                      → {s : GuiState}
                      → diagnosisState f r a w -gui-> s
                      → (w' : Weight)
                      → ¬ (s  ≡ NOACSelectionAState w')
theoremNoNOACA<25Aux f .<25 _ _ refl refl-gui-> _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ refl-gui->) _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ (step _ refl-gui->)) _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ (step _ (step _ refl-gui->))) _ ()
theoremNoNOACA<25Aux f .<25 _ _ refl (step _ (step _ (step _ (step (() , _) _))))


-- \BusinessProcess`
theoremNoNOACA<25 :
   (strAge strWght strFallR strScore strBlood : String)
   →  str2RenalCat strBlood  ≡ <25
   →  {s : GuiState}
   →  stateAfterBloodTest  strAge strWght strFallR
                           strScore strBlood
      -gui-> s
   →  (w' : Weight)
   →  ¬ (s  ≡ NOACSelectionAState w')
theoremNoNOACA<25 strAge strWght strFallR strScore strBlood = theoremNoNOACA<25Aux (patientHist2FallRisk strFallR)
                                                      (str2RenalCat strBlood) (str2AgeCat strAge)(str2Weight strWght)


{- We show that if the renalvalue is <25, NOAC D state will not be reached -}

theoremNoNOACD<25Aux : (f : FallRisk)(r : RenalCat) (a : AgeCat)(w : Weight)
                      → r ≡ <25
                      → {s : GuiState}
                      → diagnosisState f r a w -gui-> s
                      → (r' : RenalCat≥30) (a' : AgeCat)
                      → ¬ (s  ≡ NOACSelectionDState r' a')
theoremNoNOACD<25Aux f .<25 _ _ refl refl-gui-> _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ refl-gui->) _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ (step _ refl-gui->)) _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ (step _ (step _ refl-gui->))) _ _ ()
theoremNoNOACD<25Aux f .<25 _ _ refl (step _ (step _ (step _ (step (() , _) _))))

theoremNoNOACD<25 : (strAge strWght strFallR strScore strBlood : String)
                   → str2RenalCat strBlood  ≡ <25
                   → {s : GuiState}
                   → stateAfterBloodTest strAge strWght strFallR strScore strBlood -gui-> s
                   → (r' : RenalCat≥30) (a' : AgeCat)
                   → ¬ (s  ≡ NOACSelectionDState r' a')
theoremNoNOACD<25 strAge strWght strFallR strScore strBlood = theoremNoNOACD<25Aux (patientHist2FallRisk strFallR)
                                                      (str2RenalCat strBlood) (str2AgeCat strAge)(str2Weight strWght)

{- ####
###-}
