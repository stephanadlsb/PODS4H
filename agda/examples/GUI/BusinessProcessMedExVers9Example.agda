-- \BusinessProcessMedExVersNineExample

module GUI.BusinessProcessMedExVers9Example   where

-- as BusinessProcessMedExVers7Example
-- but adding check conditions

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
open import Data.Maybe

open import heap.libraryNat
open import heap.libraryBool
open import heap.libraryVec
open import heap.libraryMaybe
open import heap.libraryNatPart2
open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ) renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
open import GUI.GUIDefinitionsVers2
open import GUI.GUIModelVers3
open import GUI.GUIExampleVers2
open import GUI.GUIExampleLibVers2
open import GUI.BusinessProcessVers4
-- open import GUI.BusinessProcessDecProcVers1
open import GUI.BusinessProcessMedExLibVers2
open import GUI.BusinessProcessMedExPresentationLib

open import SizedIO.Base hiding (_>>_)
open import SizedIO.Console hiding (main)



-- patientDiagnosedText : String
-- patientDiagnosedText = "patient Diagnosed"

discharge : BusinessProcessDec
discharge =  endEvent dischargePatientText

discussFollowUp : BusinessProcessDec
discussFollowUp = activity discussFollowupText discharge

warfarin : BusinessProcessDec
warfarin  = activity prescribeWarfarinText discussFollowUp


lowDoseSelection  : BusinessProcessDec
lowDoseSelection   =  activity lowDoseSelectionText discussFollowUp

highDoseSelection  : BusinessProcessDec
highDoseSelection   =  activity highDoseSelectionText discussFollowUp

lowOrHighDoseSelection  : BusinessProcessDec
lowOrHighDoseSelection  = xor ((lowDoseSelectionText , discussFollowUp) ∷
                              (highDoseSelectionText , discussFollowUp) ∷
                              [])
-- \BusinessProcess

doseSelectionA' : (CrCl≥30 : Bool) → SerumCreatinine≥133Cat → AgeCat80Test → WghtCat
                 → BusinessProcessDec
doseSelectionA' false sC a w = lowDoseSelection
doseSelectionA' true sC ≥80 ≤60 = lowDoseSelection
doseSelectionA' true serumCreatinine≥133 ≤79 ≤60 = lowDoseSelection
doseSelectionA' true serumCreatinine<133 ≤79 ≤60 = highDoseSelection
doseSelectionA' true sC ≤79 ≥61 = highDoseSelection
doseSelectionA' true serumCreatinine<133 ≥80 ≥61 = highDoseSelection
doseSelectionA' true serumCreatinine≥133 ≥80 ≥61 = lowDoseSelection

doseSelectionA : CrClCat≥15 → SerumCreatinine≥133Cat → AgeCat → WghtCat
                 → BusinessProcessDec
doseSelectionA cr sC a w = doseSelectionA' (CrCl≥30 cr)  sC (ageIs≥80 a) w



doseSelectionD' : CrClCatIs≤50  → AgeCat → Has-bledCat → bleedVsStrokeRisk
                 → BusinessProcessDec
doseSelectionD' ≤50 ≥80 _ _ = lowDoseSelection
doseSelectionD' ≤50 ≥75≤79 _ _ = lowOrHighDoseSelection
doseSelectionD' ≤50 _ has≥3 _ = lowOrHighDoseSelection
doseSelectionD' ≤50 _ has≤2 _ = highDoseSelection

doseSelectionD' >50 ≥80 _ _ = lowOrHighDoseSelection
doseSelectionD' >50 ≥75≤79 _ bleed>stroke = lowOrHighDoseSelection
doseSelectionD' >50 ≥75≤79 _ bleed≤stroke = highDoseSelection

doseSelectionD' >50 ≤74 _ _ = highDoseSelection


doseSelectionD : CrClCat≥30 → AgeCat → Has-bledCat → bleedVsStrokeRisk
                 → BusinessProcessDec
doseSelectionD cC = doseSelectionD' (crClCat≥30toIs≤50 cC)


doseSelectionR : CrClCat≥15 → BusinessProcessDec
doseSelectionR =50 = highDoseSelection
doseSelectionR ≥51 = highDoseSelection
doseSelectionR ≥15≤29 =   lowDoseSelection
doseSelectionR ≥30≤49 =   lowDoseSelection

doseSelectionE : CrClCat≥15 → WghtCat → P-gpInhibitCat → BusinessProcessDec
doseSelectionE ≥51 ≤60 _             = lowDoseSelection
doseSelectionE ≥51 _ P-gpInhibitYes  = lowDoseSelection
doseSelectionE ≥51 _ _               = highDoseSelection
doseSelectionE _ _ _                 = lowDoseSelection


-- Pattern match
--
prescribeD : CrClCat≥30 → AgeCat → Has-bledCat → bleedVsStrokeRisk
                 → BusinessProcessDec
prescribeD c a h b = activity medDText (doseSelectionD c a h b)


prescribeA-E-R : CrClCat≥15 → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → P-gpInhibitCat
               → BusinessProcessDec
prescribeA-E-R cr sc a w pgp =
       xor ((medAText , doseSelectionA cr sc a w) ∷
            (medEText , doseSelectionE cr w pgp) ∷
            (medRText , doseSelectionR cr) ∷
            [])

prescribeA-D-E-R : CrClCat≥30 → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat  → P-gpInhibitCat
               → bleedVsStrokeRisk
               → BusinessProcessDec
prescribeA-D-E-R cr sc a w has pgp b-s-risk =
       xor ((medAText , doseSelectionA (crClCat≥30to≥15 cr) sc a w) ∷
            (medDText , doseSelectionD cr a has b-s-risk) ∷
            (medEText , doseSelectionE (crClCat≥30to≥15 cr) w pgp) ∷
            (medRText , doseSelectionR (crClCat≥30to≥15 cr)) ∷
            [])


prescribeNOACsel : CrClCat≥15 → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → P-gpInhibitCat
               → bleedVsStrokeRisk
               → BusinessProcessDec
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
               → BusinessProcessDec
prescribeNOAC cC f sC a w has pgp b = activitySilent -- prescribeNOACText
                           (prescribeNOACsel cC f sC a w has pgp b)






prescribeHW : BusinessProcessDec
prescribeHW = xor ((prescribeHeparinText , discussFollowUp) ∷
                   (prescribeWarfarinText , discussFollowUp) ∷
                   [])



prescribeH-W-NOAC  : CrClCat≥15 → FallRisk → SerumCreatinine≥133Cat → AgeCat
                    → WghtCat → Has-bledCat → P-gpInhibitCat
                    → bleedVsStrokeRisk
                    → BusinessProcessDec
prescribeH-W-NOAC cC f sC a w has pgp b
                   = xor ((prescribeHeparinText , discussFollowUp) ∷
                          (prescribeWarfarinText , discussFollowUp) ∷
                          (prescribeNOACText ,
                           prescribeNOACsel cC f sC a w has pgp b) ∷                                              [])

noMedication : BusinessProcessDec
noMedication = activity noMedicationText discussFollowUp

prescribeMed  : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk
               → BusinessProcessDec
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
               → BusinessProcessDec
seriousPatientTreatment  cC f sC a w has chad pgp b
           = xor ((cardioVersionText , prescribeMed cC f sC a w has chad pgp b) ∷
                  (paceMakerText , prescribeMed cC f sC a w has chad pgp b) ∷
                  (conservativeText , prescribeMed cC f sC a w has chad pgp b) ∷
                  [])


seriousNotSerious : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcessDec
seriousNotSerious cC f sC a w has chad pgp b
           = xor ((seriousText , seriousPatientTreatment cC f sC a w has chad pgp b) ∷
                  (notSeriousText , prescribeMed cC f sC a w has chad pgp b) ∷
                  [] )


patientDiagnosed : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcessDec
patientDiagnosed cC f sC a w has chad pgp b
           = activitySilent (seriousNotSerious cC f sC a w has chad pgp b)


diagnosisAtrialFib : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcessDec
diagnosisAtrialFib cC f sC a w has chad pgp b
   = activity diagnosisAtrialFibText (patientDiagnosed cC f sC a w has chad pgp b)

diagnosisAtrialFibNonDec : CrClCat → FallRisk → SerumCreatinine≥133Cat → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcess
diagnosisAtrialFibNonDec cC f sC a w has chad pgp b
     = liftBusinessProcessDec (diagnosisAtrialFib cC f sC a w has chad pgp b )



receiveBloodTestCheck : Tuple String 2 → Maybe String
receiveBloodTestCheck (strCrCl , strSC) =
     if (not (checkStrIsNum strCrCl) )
     then just "Enter a number for createnineClearance"
     else (if (not (checkStrIsNum strSC) )
     then just "Enter a number for serumCreatenine"
     else (if (not (checkStrAsNumInRange strCrCl 0 150))
     then just "createnineClearance should be <= 150"
     else (if (not (checkStrAsNumInRange strSC 0 400))
     then just "serumCreatenine should be <= 400"
     else nothing) ))

receiveBloodTestResults : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcess
receiveBloodTestResults f a w has chad pgp b =
      input {2} (createnineClearanceText , serumCreatenineText)
                receiveBloodTestCheck
                λ {( strCrCl , strSC) →
                    (diagnosisAtrialFibNonDec (str2CrClCat strCrCl) f (str2serumCreatinine<133 strSC) a w has chad pgp b)}




drawBlood : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcess
drawBlood f a w has chad pgp b = activity drawBloodText
                                     (receiveBloodTestResults f a w has chad pgp b)

enterPulseCheck : String  → Maybe String
enterPulseCheck strPulse =
     if (not (checkStrIsNum strPulse) )
     then just "Enter a number for Pulse"
     else (if not (checkStrAsNumInRange strPulse 0 400)
     then just "Enter a value <= 400"
     else nothing)

enterPulse : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcess
enterPulse f a w has chad pgp b = input pulseText enterPulseCheck λ _ →
                                     drawBlood f a w has chad pgp b

ECG : FallRisk → AgeCat
               → WghtCat → Has-bledCat → chadDsVasCat → P-gpInhibitCat
               → bleedVsStrokeRisk  → BusinessProcess
ECG f a w has chad pgp b = activity ECGtext (enterPulse f a w has chad pgp b)

patientHistoryCheck : Tuple String 4 → Maybe String
patientHistoryCheck ( strPgp , strHas , strChad , strFall)
   = if (not (checkStrIsYesNo strPgp))
     then just "P-gp-inhitor should be yes or no"
     else (if (not (checkStrIsNum strHas) )
     then just "Enter a number for HASBLED score"
     else (if (not (checkStrIsNum strChad) )
     then just "Enter a number for CHA2DS2-VASc"
     else (if (not (checkStrIsYesNo strFall))
     then just "Fall Risk should be yes or no"
     else ((if (not (checkStrAsNumInRange strHas 0 9))
     then just "HASBLED score should be <= 9"
     else (if (not (checkStrAsNumInRange strChad 0 9))
     then just "CHA2DS2-VASc score should be <= 9"
     else nothing) )))))


patientHistory : AgeCat → WghtCat → BusinessProcess
patientHistory a w = input {4} ( pgpText , hasBledText , chadDsVasText , fallRiskText)
                               patientHistoryCheck
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


patientRegistrationCheck : Tuple String 2 → Maybe String
patientRegistrationCheck (strAge , strWght)
  =  if (not (checkStrIsNum strAge) )
     then just "Age should be a number"
     else (if (not (checkStrIsNum strWght) )
     then just "Weight should be a number"
     else nothing)

patientRegistration : BusinessProcess
patientRegistration  = input {2}
                       (ageText , wghtText)
                       patientRegistrationCheck
                       λ { (strAge , strWght) →
                       patientHistory
                          (str2AgeCat strAge)
                          (str2WghtCat strWght) }

patientRegistrationGUI : GUI
patientRegistrationGUI = businessProcess2GUI patientRegistration
