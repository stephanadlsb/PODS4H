-- \BusinessProcessMedExLibVers2

module GUI.BusinessProcessMedExLibVers2   where

open import  heap.libraryNat

open import Data.Nat
open import Data.Bool
open import Data.String renaming (_==_ to _==Str_)

-- for business process in PODS4H'18 paper

{- CrCl  (German:  KrCl) -}

CrClValue : Set
CrClValue = ℕ

data  CrClCat : Set where
      ≤14  ≥15≤29 ≥30≤49 =50 ≥51  : CrClCat

{- We start by defining the values involved -}


crcl2CrClCat  : ℕ → CrClCat
crcl2CrClCat  n = if (n <ℕb  14) then ≤14
                    else (if (n <ℕb  30) then ≥15≤29
                    else (if (n <ℕb  50) then ≥30≤49
                    else (if (n <ℕb  51) then =50
                    else ≥51)))

str2CrClCat : String → CrClCat
str2CrClCat str = crcl2CrClCat (str2ℕ str)


data CrClCat≥15  : Set where
      ≥15≤29 ≥30≤49 =50 ≥51  : CrClCat≥15

data CrClCatIs≤50 : Set where
  ≤50 >50 :  CrClCatIs≤50

crClCat≥15toIs≤50 : CrClCat≥15 → CrClCatIs≤50
crClCat≥15toIs≤50 ≥15≤29 = ≤50
crClCat≥15toIs≤50 ≥30≤49 = ≤50
crClCat≥15toIs≤50 =50 = ≤50
crClCat≥15toIs≤50 ≥51 = >50

CrCl≥30 : CrClCat≥15 → Bool
CrCl≥30 ≥15≤29 = false
CrCl≥30 _      = true

data CrClCat≥30  : Set where
      ≥30≤49 =50 ≥51  : CrClCat≥30

crClCat≥30toIs≤50 : CrClCat≥30 → CrClCatIs≤50
crClCat≥30toIs≤50 ≥30≤49 = ≤50
crClCat≥30toIs≤50 =50 = ≤50
crClCat≥30toIs≤50 ≥51 = >50



crClCat≥30to≥15 : CrClCat≥30 → CrClCat≥15
crClCat≥30to≥15 ≥30≤49 = ≥30≤49
crClCat≥30to≥15 =50 = =50
crClCat≥30to≥15 ≥51 = ≥51


{-
data  CrClCat≥30  : Set where
      ≥30≤50 >50  : CrClCat≥30
-}

-- measured in μm/l
data SerumCreatinine≥133Cat : Set where
  serumCreatinine<133  serumCreatinine≥133 : SerumCreatinine≥133Cat

serumCreatinineIs≥133 : SerumCreatinine≥133Cat → Bool
serumCreatinineIs≥133 serumCreatinine<133 = false
serumCreatinineIs≥133 serumCreatinine≥133 = true

ℕ2serumCreatinine<133  : ℕ → SerumCreatinine≥133Cat
ℕ2serumCreatinine<133  n = if (n <ℕb  133) then serumCreatinine<133
                    else serumCreatinine≥133

str2serumCreatinine<133 : String → SerumCreatinine≥133Cat
str2serumCreatinine<133 str = ℕ2serumCreatinine<133 (str2ℕ str)



data AgeCat80Test : Set where
    ≤79  ≥80  : AgeCat80Test

data AgeCat : Set where
    ≤74  ≥75≤79 ≥80 : AgeCat



ageIs≥80 : AgeCat → AgeCat80Test
ageIs≥80 ≤74 = ≤79
ageIs≥80 ≥75≤79 = ≤79
ageIs≥80 ≥80 = ≥80

age2AgeCat  : ℕ → AgeCat
age2AgeCat  n = if (n <ℕb  75) then ≤74
                else (if (n <ℕb  80) then ≥75≤79
                               else ≥80)

str2AgeCat : String → AgeCat
str2AgeCat str = age2AgeCat (str2ℕ str)


{-
renalCat≥25-2-renalCat :  RenalCat≥25 → RenalCat
renalCat≥25-2-renalCat ≥25<30  = ≥25<30
renalCat≥25-2-renalCat ≥30     = ≥30
-}




data WghtCat : Set where
   ≤60  ≥61 : WghtCat

wghtIs≤60 : WghtCat → Bool
wghtIs≤60 ≤60 = true
wghtIs≤60 ≥61 = false

wght2WghtCat  : ℕ → WghtCat
wght2WghtCat  n = if (n ≦ℕb  60) then ≤60
                                 else ≥61
str2WghtCat :  String → WghtCat
str2WghtCat str = wght2WghtCat (str2ℕ str)

data FallRisk : Set where
  fallRisk noFallRisk : FallRisk

patientHist2FallRisk : String → FallRisk
patientHist2FallRisk str = if primStringEquality str "yes" then fallRisk
                           else noFallRisk

-- HAS-BLED
-- for check function max value is 9
has-bledValue : Set
has-bledValue = ℕ



-- bleeding risk
data Has-bledCat : Set where
   has≤2 has≥3 :  Has-bledCat

ℕ2Has-bledCat  : has-bledValue → Has-bledCat
ℕ2Has-bledCat n = if (n ≦ℕb  2) then has≤2
                                     else has≥3

str2Has-bledCat  : String → Has-bledCat
str2Has-bledCat str = ℕ2Has-bledCat (str2ℕ str)

-- CHAD_2DS_2-VASc - Score
-- for check function max value is 9
chadDsVascValue : Set
chadDsVascValue = ℕ

-- stroke risk
data chadDsVasCat : Set where
   chad≤1 chad=2 chad≥3 :  chadDsVasCat


chadDsVas2Cat : chadDsVascValue → chadDsVasCat
chadDsVas2Cat n = if (n ≦ℕb  1) then chad≤1
                  else (if (n ≦ℕb  2) then chad=2
                        else chad≥3)

str2ChadDsVasCat : String → chadDsVasCat
str2ChadDsVasCat str = chadDsVas2Cat (str2ℕ str)



-- bleedVsStrokeRisk
data bleedVsStrokeRisk : Set where
  bleed≤stroke bleed>stroke   :   bleedVsStrokeRisk


hasbledChadDsVas2bleedVsStrokeRisk : has-bledValue → chadDsVascValue → bleedVsStrokeRisk
hasbledChadDsVas2bleedVsStrokeRisk has-bled chadDs =
    if (has-bled ≦ℕb chadDs) then bleed≤stroke
                             else bleed>stroke

strHasbledChadDsVas2bleedVsStrokeRisk : (has chad : String) → bleedVsStrokeRisk
strHasbledChadDsVas2bleedVsStrokeRisk has  chad =
     hasbledChadDsVas2bleedVsStrokeRisk (str2ℕ  has)
                                        (str2ℕ  chad)

pulseValue : Set
pulseValue = ℕ

data pulseCat : Set where
  ≤49 ≥50≤110  ≥111 :   pulseCat

pulse2Cat : pulseValue → pulseCat
pulse2Cat pul = if (pul ≦ℕb 49) then ≤49
                   else (if (pul ≦ℕb 110) then ≥50≤110
                             else ≥111 )

-- prexisting conditions (German:  Vorerkrankungn)

-- TODO: this is likely source of specification errors
-- needs to be check futher to be 100% sure!
--

-- severe liver disease
data sevLiverDisCat : Set where
  sevLiverDisYes  sevLiverDisNo : sevLiverDisCat

-- check again; perhaps other disease better
--
data gastritisCat : Set where
  gastritisYes gastritisNo : gastritisCat

-- Medication taking

data chinidinCat : Set where
  chinidinYes chinidinNo : chinidinCat

data P-gpInhibitCat : Set where
   P-gpInhibitYes P-gpInhibitNo : P-gpInhibitCat

str2P-gpInhibitCat : String → P-gpInhibitCat
str2P-gpInhibitCat str = if primStringEquality str "yes" then P-gpInhibitYes
                           else P-gpInhibitNo


record InputStrgs : Set where
  constructor inputStrgs
  field
    strCrCl strFall strSC strAge strWght strHas strChad
                       strPgp strPulse : String
  input2crCl      : CrClCat
  input2crCl      = str2CrClCat strCrCl
  input2Fallrisk  : FallRisk
  input2Fallrisk  = patientHist2FallRisk strFall
  input2sC        : SerumCreatinine≥133Cat
  input2sC        = str2serumCreatinine<133 strSC
  input2Age       : AgeCat
  input2Age       = str2AgeCat strAge
  input2Wght      : WghtCat
  input2Wght      = str2WghtCat strWght
  input2Has       : Has-bledCat
  input2Has       = str2Has-bledCat strHas
  input2Chad      : chadDsVasCat
  input2Chad      = str2ChadDsVasCat  strChad
  input2Pgp       : P-gpInhibitCat
  input2Pgp       = str2P-gpInhibitCat strPgp
  input2BleedStrokeRisk  : bleedVsStrokeRisk
  input2BleedStrokeRisk  = hasbledChadDsVas2bleedVsStrokeRisk
                           (str2ℕ strHas)(str2ℕ strChad)


open InputStrgs public

record InputCats : Set where
  constructor inputCats
  field
    crCl    : CrClCat
    fallrisk  : FallRisk
    sC     : SerumCreatinine≥133Cat
    age    : AgeCat
    wght   : WghtCat
    has    : Has-bledCat
    chad   : chadDsVasCat
    pgp    : P-gpInhibitCat
    bleedStrokeRisk  : bleedVsStrokeRisk

open InputCats public

inputStrgs2InputCats : InputStrgs → InputCats
inputStrgs2InputCats (inputStrgs strCrCl strFall strSC strAge strWght strHas strChad
                                         strPgp strPulse)
       = inputCats
         (str2CrClCat strCrCl)
         (patientHist2FallRisk strFall)
         (str2serumCreatinine<133 strSC)
         (str2AgeCat strAge)
         (str2WghtCat strWght)
         (str2Has-bledCat strHas)
         (str2ChadDsVasCat  strChad)
         (str2P-gpInhibitCat strPgp)
         (hasbledChadDsVas2bleedVsStrokeRisk
           (str2ℕ strHas)(str2ℕ strChad))
