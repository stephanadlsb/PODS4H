-- \BusinessProcessMedExVersSevenPaper

module GUI.BusinessProcessMedExVers7Paper   where

-- as BusinessProcessMedExVers7Example
-- but using Process instead of BusinessProcess

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
open import Data.Bool

open import heap.libraryNat
open import heap.libraryBool
open import heap.libraryVec
open import heap.libraryMaybe
open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ) renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
open import GUI.GUIDefinitionsVers2
open import GUI.GUIModelVers3
open import GUI.GUIExampleVers2
open import GUI.GUIExampleLibVers2
open import GUI.BusinessProcessVers3Paper
-- open import GUI.BusinessProcessDecProcVers1
open import GUI.BusinessProcessMedExLibVers2
open import GUI.BusinessProcessMedExPresentationLib

open import SizedIO.Base hiding (_>>_)
open import SizedIO.Console hiding (main)



-- patientDiagnosedText : String
-- patientDiagnosedText = "patient Diagnosed"

discharge : ProcessDec
discharge =  endEvent dischargePatientText

discussFollowUp : ProcessDec
discussFollowUp = activity discussFollowupText discharge

warfarin : ProcessDec
warfarin  = activity prescribeWarfarinText discussFollowUp


lowDoseSelection  : ProcessDec
lowDoseSelection   =  activity lowDoseSelectionText discussFollowUp

highDoseSelection  : ProcessDec
highDoseSelection   =  activity highDoseSelectionText discussFollowUp

lowOrHighDoseSelection  : ProcessDec
lowOrHighDoseSelection  = multiXor ((lowDoseSelectionText , discussFollowUp) ∷
                              (highDoseSelectionText , discussFollowUp) ∷
                              [])
-- \Process

doseSelectionA' : (CrCl≥30 : Bool) → SerumCreatinine≥133Cat → AgeCat80Test → WghtCat
                 → ProcessDec
doseSelectionA' false sC a w = lowDoseSelection
doseSelectionA' true sC ≥80 ≤60 = lowDoseSelection
doseSelectionA' true serumCreatinine≥133 ≤79 ≤60 = lowDoseSelection
doseSelectionA' true serumCreatinine<133 ≤79 ≤60 = highDoseSelection
doseSelectionA' true sC ≤79 ≥61 = highDoseSelection
doseSelectionA' true serumCreatinine<133 ≥80 ≥61 = highDoseSelection
doseSelectionA' true serumCreatinine≥133 ≥80 ≥61 = lowDoseSelection

doseSelectionA : CrClCat≥15 → SerumCreatinine≥133Cat → AgeCat → WghtCat
                 → ProcessDec
doseSelectionA cr sC a w = doseSelectionA' (CrCl≥30 cr)  sC (ageIs≥80 a) w



doseSelectionD' : CrClCatIs≤50  → AgeCat → Has-bledCat → bleedVsStrokeRisk
                 → ProcessDec
doseSelectionD' ≤50 ≥80 _ _ = lowDoseSelection
doseSelectionD' ≤50 ≥75≤79 _ _ = lowOrHighDoseSelection
doseSelectionD' ≤50 _ has≥3 _ = lowOrHighDoseSelection
doseSelectionD' ≤50 _ has≤2 _ = highDoseSelection

doseSelectionD' >50 ≥80 _ _ = lowOrHighDoseSelection
doseSelectionD' >50 ≥75≤79 _ bleed>stroke = lowOrHighDoseSelection
doseSelectionD' >50 ≥75≤79 _ bleed≤stroke = highDoseSelection

doseSelectionD' >50 ≤74 _ _ = highDoseSelection


doseSelectionD : CrClCat≥30 → AgeCat → Has-bledCat → bleedVsStrokeRisk
                 → ProcessDec
doseSelectionD cC = doseSelectionD' (crClCat≥30toIs≤50 cC)


doseSelectionR : CrClCat≥15 → ProcessDec
doseSelectionR =50 = highDoseSelection
doseSelectionR ≥51 = highDoseSelection
doseSelectionR ≥15≤29 =   lowDoseSelection
doseSelectionR ≥30≤49 =   lowDoseSelection

doseSelectionE : CrClCat≥15 → WghtCat → P-gpInhibitCat → ProcessDec
doseSelectionE ≥51 ≤60 _             = lowDoseSelection
doseSelectionE ≥51 _ P-gpInhibitYes  = lowDoseSelection
doseSelectionE ≥51 _ _               = highDoseSelection
doseSelectionE _ _ _                 = lowDoseSelection


-- Pattern match
--
prescribeD : CrClCat≥30 → AgeCat → Has-bledCat → bleedVsStrokeRisk
                 → ProcessDec
prescribeD c a h b = activity medDText (doseSelectionD c a h b)


prescribeA-E-R : CrClCat≥15 → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → P-gpInhibitCat
               → ProcessDec
prescribeA-E-R cr sc a w pgp =
       multiXor ((medAText , doseSelectionA cr sc a w) ∷
            (medEText , doseSelectionE cr w pgp) ∷
            (medRText , doseSelectionR cr) ∷
            [])

prescribeA-D-E-R : CrClCat≥30 → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat  → P-gpInhibitCat
               → bleedVsStrokeRisk
               → ProcessDec
prescribeA-D-E-R cr sc a w has pgp b-s-risk =
       multiXor ((medAText , doseSelectionA (crClCat≥30to≥15 cr) sc a w) ∷
            (medDText , doseSelectionD cr a has b-s-risk) ∷
            (medEText , doseSelectionE (crClCat≥30to≥15 cr) w pgp) ∷
            (medRText , doseSelectionR (crClCat≥30to≥15 cr)) ∷
            [])


prescribeNOACsel : CrClCat≥15 → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → P-gpInhibitCat
               → bleedVsStrokeRisk
               → ProcessDec
prescribeNOACsel ≥30≤49 fallRisk sc a w has pgp b = prescribeD ≥30≤49 a has b -- bleed≤stroke
prescribeNOACsel =50 fallRisk sc a w has pgp b = prescribeD =50 a has b -- bleed≤stroke
prescribeNOACsel ≥51 fallRisk sc a w has pgp b = prescribeD ≥51 a has b -- bleed≤stroke

prescribeNOACsel ≥15≤29 fr sc a w has pgp b = prescribeA-E-R ≥15≤29 sc a w pgp

prescribeNOACsel ≥30≤49 f sc a w has pgp b = prescribeA-D-E-R ≥30≤49 sc a w has pgp b
prescribeNOACsel =50 f sc a w has pgp b = prescribeA-D-E-R =50 sc a w has pgp b
prescribeNOACsel ≥51 f sc a w has pgp b = prescribeA-D-E-R ≥51 sc a w has pgp b


prescribeNOAC : CrClCat≥15 → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → P-gpInhibitCat
               → bleedVsStrokeRisk
               → ProcessDec
prescribeNOAC cC f sC a w has pgp b = activitySilent -- prescribeNOACText
                           (prescribeNOACsel cC f sC a w has pgp b)






prescribeHW : ProcessDec
prescribeHW = multiXor ((prescribeHeparinText , discussFollowUp) ∷
                   (prescribeWarfarinText , discussFollowUp) ∷
                   [])



prescribeH-W-NOAC  : CrClCat≥15 → FallRisk → SerumCreatinine≥133Cat → AgeCat
                    → WghtCat → Has-bledCat → P-gpInhibitCat
                    → bleedVsStrokeRisk
                    → ProcessDec
prescribeH-W-NOAC cC f sC a w has pgp b
                   = multiXor ((prescribeHeparinText , discussFollowUp) ∷
                          (prescribeWarfarinText , discussFollowUp) ∷
                          (prescribeNOACText ,
                           prescribeNOACsel cC f sC a w has pgp b) ∷                                              [])

noMedication : ProcessDec
noMedication = activity noMedicationText discussFollowUp

prescribeMed  : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk
               → ProcessDec
prescribeMed cC f sC a w has chad≤1 pgp b = noMedication
prescribeMed cC f sC a w has chad=2 pgp bleed>stroke = noMedication
prescribeMed ≤14 f sC a w has _ pgp _ = prescribeHW
prescribeMed ≥15≤29 f sC a w has _ pgp b = prescribeH-W-NOAC ≥15≤29 f sC a w has pgp b
prescribeMed ≥30≤49 f sC a w has _ pgp b = prescribeNOAC ≥30≤49 f sC a w has pgp b
prescribeMed =50 f sC a w has _ pgp b = prescribeNOAC =50 f sC a w has pgp b
prescribeMed ≥51 f sC a w has _ pgp b = prescribeNOAC ≥51 f sC a w has pgp b


seriousPatientTreatment : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk
               → ProcessDec
seriousPatientTreatment  cC f sC a w has chad pgp b
           = multiXor ((cardioVersionText , prescribeMed cC f sC a w has chad pgp b) ∷
                  (paceMakerText , prescribeMed cC f sC a w has chad pgp b) ∷
                  (conservativeText , prescribeMed cC f sC a w has chad pgp b) ∷
                  [])


seriousNotSerious : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → ProcessDec
seriousNotSerious cC f sC a w has chad pgp b
           = multiXor ((seriousText , seriousPatientTreatment cC f sC a w has chad pgp b) ∷
                  (notSeriousText , prescribeMed cC f sC a w has chad pgp b) ∷
                  [] )


patientDiagnosed : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → ProcessDec
patientDiagnosed cC f sC a w has chad pgp b
           = activitySilent (seriousNotSerious cC f sC a w has chad pgp b)


diagnosisAtrialFib : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → ProcessDec
diagnosisAtrialFib cC f sC a w has chad pgp b
   = activity diagnosisAtrialFibText (patientDiagnosed cC f sC a w has chad pgp b)

receiveBloodTestResults : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → Process
receiveBloodTestResults f a w has chad pgp b =
      input {2} (createnineClearanceText , serumCreatenineText)
                 λ {( strCrCl , strSC) →
                    liftProcessDec
                    (diagnosisAtrialFib (str2CrClCat strCrCl) f (str2serumCreatinine<133 strSC) a w has chad pgp b)}


drawBlood : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → Process
drawBlood f a w has chad pgp b = activity drawBloodText
                                     (receiveBloodTestResults f a w has chad pgp b)


enterPulse : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → Process
enterPulse f a w has chad pgp b = input pulseText λ _ →
                                     drawBlood f a w has chad pgp b

ECG : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → Process
ECG f a w has chad pgp b = activity ECGtext (enterPulse f a w has chad pgp b)


patientHistory : AgeCat → WghtCat → Process
patientHistory a w = input {4} ( pgpText , hasBledText , chadDsVasText , fallRiskText)
                               λ { (strPgp , strHas , strChad , strFall)  →
                                      ECG
                                     (patientHist2FallRisk strFall)
                                     a w
                                     (str2Has-bledCat strHas)
                                     (str2ChadDsVasCat  strChad)
                                     (str2P-gpInhibitCat strPgp)
                                     (hasbledChadDsVas2bleedVsStrokeRisk
                                        (str2ℕ strHas)
                                        (str2ℕ strChad))  }



patientRegistration : Process
patientRegistration  = input {2}
                       (( ageText , wghtText))
                       λ { (strAge , strWght) →
                       patientHistory
                          (str2AgeCat strAge)
                          (str2WghtCat strWght) }

patientRegistrationGUI : GUI
patientRegistrationGUI = process2GUI patientRegistration
