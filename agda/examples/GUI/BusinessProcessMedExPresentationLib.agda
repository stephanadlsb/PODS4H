-- \BusinessProcessMedExPresentationLib

module GUI.BusinessProcessMedExPresentationLib   where

open import Data.String

dischargePatientText : String
dischargePatientText = "Discharge Patient"

discussFollowupText : String
discussFollowupText = "Disucss Follow-Up"

prescribeWarfarinText : String
prescribeWarfarinText = "Prescribe warfarin"

prescribeHeparinText : String
prescribeHeparinText = "Prescribe Heparin"

prescribeNOACText : String
prescribeNOACText = "Prescribe NOAC"


lowDoseSelectionText : String
lowDoseSelectionText = "Low Dose"

highDoseSelectionText : String
highDoseSelectionText = "High Dose"

medAText : String
medAText = "Apixaban" -- "Med A"

medDText : String
medDText = "Dabigatran" -- "Med D"

medEText : String
medEText = "Edoxaban" -- Med E"

medRText : String
medRText = "Rivaroxaban" -- Med R"

noMedicationText : String
noMedicationText = "No Medication"


cardioVersionText : String
cardioVersionText = "Cardioversion"

paceMakerText : String
paceMakerText = "Pacemaker"

conservativeText : String
conservativeText = "Conservative"

seriousText : String
seriousText = "serious"

notSeriousText : String
notSeriousText = "not serious"


diagnosisAtrialFibText : String
diagnosisAtrialFibText = "Diagnosis (AF)"

createnineClearanceText : String
createnineClearanceText = "Enter Createnine Clearance"

serumCreatenineText : String
serumCreatenineText = "Enter Serum Createnine (µmol/l)"

drawBloodText : String
drawBloodText = "Draw blood"

pulseText : String
pulseText = "Enter Pulse"

ECGtext : String
ECGtext = "ECG"

hasBledText : String
hasBledText = "Enter HASBLED score (0 - 9)"

chadDsVasText : String
chadDsVasText = "Enter CHA2DS2-VASc score (0 - 9)"

fallRiskText : String
fallRiskText = "Enter Fall Risk (yes/no)"

pgpText : String
pgpText = "Takes potent P-gp-inhibitor (yes/no)"

ageText : String
ageText = "Enter Age"

wghtText : String
wghtText = "Enter Weight"
