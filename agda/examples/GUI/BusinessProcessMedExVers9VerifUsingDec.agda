-- \BusinessProcessMedExVersNineVerifUsingDec
{-# OPTIONS --allow-unsolved-metas #-}

module GUI.BusinessProcessMedExVers9VerifUsingDec  where

-- BusinessProcessMedExVers7VerifUsingDec.agda
-- for PODS4H'2018
-- but with check functions (as BusinessProcessMedExVers8.agda)

open import Data.Fin renaming (_+_ to _+fin_)
open import Data.Nat
open import Data.Empty
open import Data.List renaming (map to mapL)
open import Data.Product hiding (map) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Size
open import Data.Unit
open import Data.Maybe
open import Data.String renaming (_==_ to _==Str_)
open import Data.String
open import Data.Bool hiding (_∨_ ; _∧_)
open import Relation.Binary.PropositionalEquality hiding (setoid ; preorder ; decSetoid; [_])
open import Data.Sum hiding (map) renaming (_⊎_ to _∨_ ; inj₁ to or1 ; inj₂ to or2)

open import heap.libraryNat
open import heap.libraryFin
open import heap.libraryBool
open import heap.libraryVec
open import heap.libraryMaybe
open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ) renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
open import GUI.GUIDefinitionsVers2
open import GUI.GUIModelVers3
open import GUI.GUIExampleVers2
open import GUI.GUIExampleLibVers2
-- open import GUI.BusinessProcessDecProcVers1
open import GUI.BusinessProcessMedExLibVers2
open import GUI.BusinessProcessMedExPresentationLib
open import GUI.BusinessProcessVers4
open import GUI.BusinessProcessMedExVers9Example
open import GUI.BusinessProcessDecProcVers2

open import SizedIO.Base hiding (_>>_)
open import SizedIO.Console hiding (main)




patientRegistrationState : GuiState
patientRegistrationState = businessProcess2State patientRegistration

patientDiagnosedState : InputCats → GuiState
patientDiagnosedState (inputCats cC f sC a w has chad pgp b)
    = businessProcessDec2GuiState
     (patientDiagnosed cC f sC a w has chad pgp b)


record InputStrgsOk (strgs : InputStrgs) :  Set where
  constructor inputStrgsOk
  field
    patientRegistrationCheckOk : IsNothing (patientRegistrationCheck (strgs .strAge , strgs .strWght))
    patientHistoryCheckOk : IsNothing (patientHistoryCheck (strgs .strPgp , strgs .strHas ,
                                                            strgs .strChad , strgs .strFall))
    pulseCheckOk : IsNothing (enterPulseCheck (strgs .strPulse))
    bloodTestCheckOk : IsNothing (receiveBloodTestCheck ( strgs .strCrCl , strgs .strSC))


patientHistoryState : AgeCat → WghtCat → GuiState
patientHistoryState age wght = businessProcess2State (patientHistory age wght)

str2PatientHistoryState : String → String → GuiState
str2PatientHistoryState strAge strWght = patientHistoryState (str2AgeCat strAge) (str2WghtCat strWght)

ECGState : AgeCat → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
           → FallRisk → bleedVsStrokeRisk  → GuiState
ECGState age wght has chad pgp fall b =   businessProcess2State (ECG fall age wght has chad pgp b)

str2ECGState : (strAge strWght strHas strChad strPgp strFall : String) → GuiState
str2ECGState strAge strWght strHas strChad strPgp strFall =
                                    ECGState (str2AgeCat strAge)
                                             (str2WghtCat strWght)
                                             (str2Has-bledCat strHas)
                                             (str2ChadDsVasCat strChad)
                                             (str2P-gpInhibitCat strPgp)
                                             (patientHist2FallRisk strFall)
                                             (strHasbledChadDsVas2bleedVsStrokeRisk strHas strChad)


drawBloodState : AgeCat → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
                 → FallRisk → bleedVsStrokeRisk  → GuiState
drawBloodState  age wght has chad pgp fall b = businessProcess2State  (drawBlood fall age wght has chad pgp
                                                                       b)

str2DrawBloodState : (strAge strWght strHas strChad strPgp strFall : String) → GuiState
str2DrawBloodState strAge strWght strHas strChad strPgp strFall =
                                  drawBloodState (str2AgeCat strAge)
                                             (str2WghtCat strWght)
                                             (str2Has-bledCat strHas)
                                             (str2ChadDsVasCat strChad)
                                             (str2P-gpInhibitCat strPgp)
                                             (patientHist2FallRisk strFall)
                                             (strHasbledChadDsVas2bleedVsStrokeRisk strHas strChad)

diagnosisAtrialFibState : AgeCat → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
                 → FallRisk → bleedVsStrokeRisk  → CrClCat → SerumCreatinine≥133Cat → GuiState
diagnosisAtrialFibState  age wght has chad pgp fall b CrCl SC =
     businessProcess2State  (diagnosisAtrialFibNonDec CrCl fall SC age wght has chad pgp b)

str2DiagnosisAtrialFibState : (strAge strWght strHas strChad strPgp strFall strCrCl strSC : String) → GuiState
str2DiagnosisAtrialFibState strAge strWght strHas strChad strPgp strFall strCrCl strSC =
                     diagnosisAtrialFibState (str2AgeCat strAge)
                                             (str2WghtCat strWght)
                                             (str2Has-bledCat strHas)
                                             (str2ChadDsVasCat strChad)
                                             (str2P-gpInhibitCat strPgp)
                                             (patientHist2FallRisk strFall)
                                             (strHasbledChadDsVas2bleedVsStrokeRisk strHas strChad)
                                             (str2CrClCat strCrCl)
                                             (str2serumCreatinine<133 strSC)

patientHistoryStateReached :
         (strAge strWght : String)
         (patientRegistrationCheckOk' : IsNothing (patientRegistrationCheck (strAge , strWght)))
         → guiNext patientRegistrationState (textboxInput2 strAge strWght)
           ≡ str2PatientHistoryState strAge strWght
patientHistoryStateReached strAge strWght ageWeightOk with (patientRegistrationCheck (strAge , strWght))
patientHistoryStateReached strAge strWght () | just x
patientHistoryStateReached strAge strWght tt | nothing = refl


ECGStateReached :
         (strAge strWght strHas strChad strPgp strFall : String)
         (patientHistoryCheckOk' : IsNothing (patientHistoryCheck (strPgp , strHas , strChad , strFall)))
         → guiNext (str2PatientHistoryState strAge strWght)
                   (textboxInput4 strPgp strHas strChad strFall)
           ≡ str2ECGState strAge strWght strHas strChad strPgp strFall
ECGStateReached strAge strWght strHas strChad strPgp strFall patientHistoryCheckOk' with (patientHistoryCheck (strPgp , strHas , strChad , strFall))
ECGStateReached strAge strWght strHas strChad strPgp strFall () | just x
ECGStateReached strAge strWght strHas strChad strPgp strFall tt | nothing = refl

drawBloodStateReached :
         (strAge strWght strHas strChad strPgp strFall strPulse : String)
         (pulseCheckOk : IsNothing (enterPulseCheck strPulse))
         → guiNext (guiNext (str2ECGState strAge strWght strHas strChad strPgp strFall)
                            btnClick)
                   (textboxInput strPulse)
           ≡ str2DrawBloodState strAge strWght strHas strChad strPgp strFall
drawBloodStateReached strAge strWght strHas strChad strPgp strFall strPulse pulseCheckOk with (enterPulseCheck strPulse)
drawBloodStateReached strAge strWght strHas strChad strPgp strFall strPulse () | just x
drawBloodStateReached strAge strWght strHas strChad strPgp strFall strPule tt | nothing = refl

diagnosisAtrialFibStateReached :
         (strAge strWght strHas strChad strPgp strFall strCrCl strSC : String)
         (receiveBloodTestCheckOk : IsNothing (receiveBloodTestCheck (strCrCl , strSC)))
         → guiNext (guiNext (str2DrawBloodState strAge strWght strHas strChad strPgp strFall)
                            btnClick)
                   (textboxInput2 strCrCl strSC)
           ≡ str2DiagnosisAtrialFibState strAge strWght strHas strChad strPgp strFall strCrCl strSC
diagnosisAtrialFibStateReached strAge strWght strHas strChad strPgp strFall strCrCl strSC receiveBloodTestCheckOk with (receiveBloodTestCheck (strCrCl , strSC))
diagnosisAtrialFibStateReached strAge strWght strHas strChad strPgp strFall strCrCl strSC () | just x
diagnosisAtrialFibStateReached strAge strWght strHas strChad strPgp strFall strCrCl strSC tt | nothing = refl






stateAfterBloodTest : (strgs : InputStrgs)
                      (strgsOk : InputStrgsOk strgs)
                      → GuiState
stateAfterBloodTest (inputStrgs strCrCl strFall strSC strAge strWght strHas strChad strPgp strPulse)
                    (inputStrgsOk patientRegistrationCheckOk' patientHistoryCheckOk' pulseCheckOk'
                                  bloodTestCheckOk')
                     =  guiNexts
                        patientRegistrationState
                        (((((((nilCmd
                         >>>'   textboxInput2  strAge  strWght
                            wproof str2PatientHistoryState strAge strWght
                            ,,,    patientHistoryStateReached strAge strWght patientRegistrationCheckOk' )
                         >>>'   textboxInput4  strPgp  strHas strChad strFall
                            wproof str2ECGState strAge strWght strHas strChad strPgp strFall
                            ,,,    ECGStateReached strAge strWght strHas strChad strPgp strFall patientHistoryCheckOk' )
                         >>>  btnClick   )
                         >>>'   textboxInput  strPulse
                            wproof str2DrawBloodState strAge strWght strHas strChad strPgp strFall
                            ,,,    drawBloodStateReached strAge strWght strHas strChad strPgp strFall strPulse pulseCheckOk' )
                         >>>  btnClick   )
                         >>>'  textboxInput2  strCrCl strSC
                            wproof str2DiagnosisAtrialFibState strAge strWght strHas strChad strPgp strFall strCrCl strSC
                            ,,, diagnosisAtrialFibStateReached strAge strWght strHas strChad strPgp strFall strCrCl strSC  bloodTestCheckOk' )
                         >>>  btnClick   )



corrStateAfterBloodTest : (strs : InputStrgs)
                          (strsOk : InputStrgsOk strs)
                          → stateAfterBloodTest strs strsOk
                            ≡ patientDiagnosedState (inputStrgs2InputCats strs)
corrStateAfterBloodTest strs strOk = refl




isHW : GuiState → Bool
isHW = stateIsXorWithTexts prescribeHeparinText prescribeWarfarinText

chadCond≥2 : InputCats → Set
chadCond≥2 inp = (inp .chad ≡ chad≥3) ∨ (inp .chad ≡ chad=2 ∧ inp .bleedStrokeRisk ≡ bleed≤stroke)

strgsChadCond≥2 : InputStrgs → Set
strgsChadCond≥2 strs = input2Chad strs ≡ chad≥3
                       ∨ (input2Chad strs ≡ chad=2 ∧ input2BleedStrokeRisk strs ≡ bleed≤stroke)

theoremWarfarinAux : (inp : InputCats)
                     → inp .crCl ≡ ≤14
                     → chadCond≥2 inp
                     → patientDiagnosedState inp -eventuallyPb-> isHW
theoremWarfarinAux (inputCats ≤14 f sC a w has .chad≥3 pgp b) refl (or1 refl)
           = decProcExtr isHW (patientDiagnosed ≤14 f sC a w has chad≥3 pgp b) tt
theoremWarfarinAux (inputCats ≤14 f sC a w has .chad=2 pgp .bleed≤stroke) refl (or2 (refl , refl))
           = decProcExtr isHW (patientDiagnosed ≤14 f sC a w has chad=2 pgp bleed≤stroke) tt


theoremWarfarin : (strs : InputStrgs)
                  (strsOk : InputStrgsOk strs)
                  → input2crCl strs ≡ ≤14
                  → strgsChadCond≥2 strs
                  → stateAfterBloodTest strs strsOk -eventuallyPb-> isHW
theoremWarfarin strs  strsOk eq1 eq2
                = theoremWarfarinAux (inputStrgs2InputCats strs) eq1 eq2


isMedDOnly : GuiState → Bool
isMedDOnly =  stateIsSimpleText medDText

theoremMedDAux : (inp : InputCats)
                  → (inp .crCl ≡ ≥30≤49 ∨ inp .crCl ≡ =50 ∨ inp .crCl ≡ ≥51)
                  → inp .fallrisk ≡ fallRisk
                  → chadCond≥2 inp
                  → patientDiagnosedState inp  -eventuallyPb-> isMedDOnly
theoremMedDAux (inputCats .≥30≤49 fallRisk sC a w has chad≥3 pgp b)
                (or1 refl) refl (or1 refl)
                =   decProcExtr isMedDOnly
                    (patientDiagnosed ≥30≤49 fallRisk sC a w has chad≥3 pgp b) tt
theoremMedDAux (inputCats  .=50 fallRisk sC a w has chad≥3 pgp b)
                 (or2 (or1 refl)) refl (or1 refl)
                 = decProcExtr isMedDOnly
                  (patientDiagnosed =50 fallRisk sC a w has chad≥3 pgp b) tt
theoremMedDAux (inputCats .≥51 fallRisk sC a w has chad≥3 pgp b)
                 (or2 (or2 refl)) refl (or1 refl)
                 = decProcExtr isMedDOnly
                   (patientDiagnosed ≥51 fallRisk sC a w has chad≥3 pgp b) tt
theoremMedDAux (inputCats .≥30≤49 fallRisk sC a w has chad=2 pgp .bleed≤stroke)
                (or1 refl) refl (or2 (refl , refl))
                =   decProcExtr isMedDOnly
                    (patientDiagnosed ≥30≤49 fallRisk sC a w has chad=2 pgp bleed≤stroke) tt
theoremMedDAux (inputCats  .=50 fallRisk sC a w has chad=2 pgp .bleed≤stroke)
                 (or2 (or1 refl)) refl (or2 (refl , refl))
                 = decProcExtr isMedDOnly
                  (patientDiagnosed =50 fallRisk sC a w has chad=2 pgp bleed≤stroke) tt
theoremMedDAux (inputCats .≥51 fallRisk sC a w has chad=2 pgp .bleed≤stroke)
                 (or2 (or2 refl)) refl (or2 (refl , refl))
                 = decProcExtr isMedDOnly
                   (patientDiagnosed ≥51 fallRisk sC a w has chad=2 pgp bleed≤stroke) tt


theoremMedD : (strs : InputStrgs)
                  (strsOk : InputStrgsOk strs)
                  → (input2crCl strs ≡ ≥30≤49 ∨ input2crCl strs ≡ =50 ∨ input2crCl strs ≡ ≥51)
                  → (input2Fallrisk strs ≡ fallRisk)
                  → strgsChadCond≥2 strs
                  → stateAfterBloodTest strs strsOk -eventuallyPb-> isMedDOnly
theoremMedD strs  strOk eq1 eq2 eq3
     = theoremMedDAux (inputStrgs2InputCats strs) eq1 eq2 eq3



isNoMedication : GuiState → Bool
isNoMedication =  stateIsSimpleText noMedicationText

theoremNoMedicationAux : (inp : InputCats)
                  → (inp .chad ≡ chad≤1 ∨ (inp .chad ≡ chad=2 ∧ inp .bleedStrokeRisk ≡ bleed>stroke))
                  → patientDiagnosedState inp  -eventuallyPb-> isNoMedication
theoremNoMedicationAux
   (inputCats crCl₁ fallrisk₁ sC₁ age₁ wght₁ has₁ .chad≤1 pgp₁
    bleedStrokeRisk₁)
   (or1 refl)
    = decProcExtr isNoMedication
      (patientDiagnosed crCl₁ fallrisk₁ sC₁ age₁ wght₁ has₁ chad≤1 pgp₁
       bleedStrokeRisk₁) tt
theoremNoMedicationAux
   (inputCats crCl₁ fallrisk₁ sC₁ age₁ wght₁ has₁ .chad=2 pgp₁
    .bleed>stroke) (or2 (refl , refl))
   = decProcExtr isNoMedication
     (patientDiagnosed crCl₁ fallrisk₁ sC₁ age₁ wght₁ has₁ chad=2 pgp₁
      bleed>stroke) tt


theoremNoMedication : (strs : InputStrgs)
                  (strsOk : InputStrgsOk strs)
                  → (input2Chad strs ≡ chad≤1 ∨
                     (input2Chad strs ≡ chad=2 ∧ input2BleedStrokeRisk strs ≡ bleed>stroke))
                  → stateAfterBloodTest strs strsOk -eventuallyPb-> isNoMedication
theoremNoMedication strs  strsOk eq1
     = theoremNoMedicationAux (inputStrgs2InputCats strs) eq1


doesNotPrescribeD : GuiState → Bool
doesNotPrescribeD =  stateDoesNotContainTextButton medDText

theoremNotPrescribeMedDAux : (inp : InputCats)
                  → inp .crCl ≡ ≥15≤29
                  → forAllReachableb (patientDiagnosedState inp) doesNotPrescribeD
theoremNotPrescribeMedDAux
  (inputCats .≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad≤1 pgp₁
   bleedStrokeRisk₁) refl
  = decProcAllExtr doesNotPrescribeD
    (patientDiagnosed ≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad≤1 pgp₁
      bleedStrokeRisk₁) tt
theoremNotPrescribeMedDAux
   (inputCats .≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad=2 pgp₁ bleed≤stroke)
   refl
   = decProcAllExtr doesNotPrescribeD
     (patientDiagnosed ≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad=2 pgp₁
      bleed≤stroke) tt

theoremNotPrescribeMedDAux
   (inputCats .≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad=2 pgp₁ bleed>stroke)
   refl
   = decProcAllExtr doesNotPrescribeD (patientDiagnosed ≥15≤29 fallrisk₁ sC₁
     age₁ wght₁ has₁ chad=2 pgp₁ bleed>stroke) tt

theoremNotPrescribeMedDAux
  (inputCats .≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad≥3 pgp₁
    bleedStrokeRisk₁) refl
  = decProcAllExtr doesNotPrescribeD
    (patientDiagnosed ≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad≥3 pgp₁
     bleedStrokeRisk₁) tt


theoremNotPrescribeMedD : (strs : InputStrgs)
                  (strsOk : InputStrgsOk strs)
                  → input2crCl strs ≡ ≥15≤29
                  → forAllReachableb (stateAfterBloodTest strs strsOk) doesNotPrescribeD
theoremNotPrescribeMedD strs  strsOk eq1
     = theoremNotPrescribeMedDAux (inputStrgs2InputCats strs) eq1



doesPrescribeHW  : GuiState → Bool
doesPrescribeHW =  stateIsXorWithTexts prescribeHeparinText prescribeWarfarinText

theoremPrescribeHWAux : (inp : InputCats)
                  → inp .crCl ≡ ≤14
                  → (inp .chad ≡ chad≥3 ∨ (inp .chad ≡ chad=2 ∧ inp .bleedStrokeRisk ≡ bleed≤stroke))
                  → patientDiagnosedState inp -eventuallyPb->  doesPrescribeHW
theoremPrescribeHWAux (inputCats .≤14 fallrisk₁ sC₁ age₁ wght₁ has₁ .chad≥3 pgp₁ bleedStrokeRisk₁) refl (or1 refl) =
    decProcExtr doesPrescribeHW
       (patientDiagnosed ≤14 fallrisk₁ sC₁ age₁ wght₁ has₁ chad≥3 pgp₁
         bleedStrokeRisk₁) tt

theoremPrescribeHWAux (inputCats .≤14 fallrisk₁ sC₁ age₁ wght₁ has₁ .chad=2 pgp₁ .bleed≤stroke) refl (or2 (refl , refl)) =
        decProcExtr doesPrescribeHW (patientDiagnosed ≤14 fallrisk₁ sC₁ age₁ wght₁ has₁ chad=2 pgp₁ bleed≤stroke) tt



theoremPrescribeHW : (strs : InputStrgs)
                  (strsOk : InputStrgsOk strs)
                  → input2crCl strs ≡ ≤14
                  → strgsChadCond≥2 strs
                  → stateAfterBloodTest strs strsOk -eventuallyPb->  doesPrescribeHW
theoremPrescribeHW strs  strsOk eq1 eq2
     = theoremPrescribeHWAux (inputStrgs2InputCats strs) eq1 eq2





-- decProcAllExtr doesNotPrescribeD (patientDiagnosed ≥15≤29 fallrisk₁ sC₁ age₁ wght₁ has₁ chad₁ pgp₁ bleedStrokeRisk₁) {!chad₁!}


-- Next steps
-- MORE THEOREMS:
-- if medA is given then
--   med 2 von 3 sind korrekt zu niedriger dosis
--        2 von 3 sind
--    SerumCreatininine>=133 = serumCreatinine≥133
--    agecat80Test = ≥80
--    wgtat = ≤60
--   wenn stroke risk geq then no mediation unreachable

---   R E A    never reachable high/low dose
-- IMPORTANT (stephan)
--  Also, bei Apixaban, dass Alter>=80 alleine (d.h. ohne niedriger Kilos
--      bzw. hohem serum kreatinin) zur hohen Dosis führt.
--  DONE wenn crclcat <= 14  prescribeHW
--  DONE wenn crclcat >= 30 und fall risk     prescribeD
--  DONE when no medication is given
--  DONE when 15 - 29   no prescribeD
--  DONE prescribeHW
--  PROBABLY NOT the above so that we depend on crlcat>=30 directly
--    (which then becomes all the underconditions)
