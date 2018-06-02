-- \BusinessProcessVersThreePaper

module GUI.BusinessProcessVers3Paper where

-- Version like BusinessProcess.agda
-- but usinig the simplified version from
--   GUIDefinitionsVers2.agdao

open import Data.String
open import Data.Unit
open import Data.List renaming (map to mapL; length to lengthL)
open import Data.Product hiding (map)
open import Data.Nat
open import Size
open import Data.Fin renaming (_+_ to _+fin_)
open import Relation.Binary.PropositionalEquality


open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import heap.libraryVec
open import GUI.GUIDefinitionsVers2
-- open import GUI.GUIDefinitionsBase
open import GUI.GUIExampleLibVers2
open import StateSizedIO.GUI.BaseStateDependent
open import GUI.GUIModelVers3

-- \BusinessProcessVersThreePaper
data Process : Set where
  endEvent    :  String → Process
  activity    :  String → Process → Process
  xor         :  (String ×  Process) →  (String ×  Process) → Process
  unaryInput  :  String → (String → Process) → Process
  startEvent  :  String → Process → Process
  multiXor        :  List (String ×  Process) →  Process
  startEventSilent :  Process → Process
  input      :  {n : ℕ} → Tuple String n
                →  (Tuple String n → Process)
                →  Process
  activitySilent    :  Process → Process

process2GUIxorFrame : (l : List (String × Process))
                               → Frame
process2GUIxorFrame [] = emptyFrame
process2GUIxorFrame ((str , p) ∷ l) = addButton str (process2GUIxorFrame l)


{-
discharge : Process
discharge  =  endEvent "Discharge Patient"

treatPatient : Process
treatPatient = activity "Treat Patient" discharge

patientRegistersAtER : Process
patientRegistersAtER = startEvent "PatientRegisters at ER" treatPatient
-}
-- Sequence of Activities, xor gives us a tree
--

activityExample : Process
activityExample = startEvent "PatientRegisters at ER"
                          (activity "Treat Patient"
                                     (endEvent "Discharge Patient"))
xorExample : Process
xorExample = startEvent "PatientRegisters at ER"
               (xor ("Give Medication A" , endEvent "Discharge Patient")
                    ("Give Medication B" , endEvent "Discharge Patient"))




-- with Tuple slit m into (str' , m)
--  and used str' for the first two and m for the last goal



mutual
  process2GUI : ∀ {i}  → Process
                             → GUI {i}
  process2GUI (endEvent x) = endEventGUI x
  process2GUI (multiXor l) = process2GUIxor l
  process2GUI (xor  l l') = process2GUIBinaryXor l l'
  process2GUI (input {n} str f) = multiTextboxGUI n str (λ v → process2GUI (f v))
  process2GUI (startEvent start b) = onebuttonStrGUI start (process2GUI b)  -- endEventGUI x -- TODO ERROR STEPHAN
  process2GUI (startEventSilent b)  =   process2GUI b
  process2GUI (activity str b)  =   onebuttonStrGUI str (process2GUI b)
  process2GUI (activitySilent b)  =   process2GUI b
  process2GUI (unaryInput  str f) = multiTextboxGUI 1 str (λ v → process2GUI (f v))

-- an unsized version for presentation purposes

  process2Gui : Process → GUI
  process2Gui = process2GUI {∞}

  process2GUIxorHandl : {i : Size} → (l : List (String × Process))
                              → (m : FrameMethod (process2GUIxorFrame l))
                              → GUI {i}
  process2GUIxorHandl [] (() , _)
  process2GUIxorHandl ((str , g) ∷ l) (zero , _) = process2GUI g
  process2GUIxorHandl ((str , g) ∷ l) (suc m , s) = process2GUIxorHandl l (m , s)

  process2GUIxor : {i : Size} → List (String × Process) → GUI {i}
  process2GUIxor l .gui = process2GUIxorFrame l
  process2GUIxor l .method m =  return' (process2GUIxorHandl l m)
{-
  process2GUIxor : {i : Size} → List (String × Process) → GUI {i}
  process2GUIxor [] .gui = emptyFrame
  process2GUIxor [] .method ()
  process2GUIxor ((str , _) ∷ l) .gui = addButton str (process2GUIxor l .gui)
  process2GUIxor ((str , g) ∷ l) .method (zero , _) = return'  (process2GUI g)
  process2GUIxor ((str , _) ∷ l) .method (suc m , s) = process2GUIxor l .method (m , s)
-}

  process2GUIBinaryXor : {i : Size} → String × Process → String × Process → GUI {i}
  process2GUIBinaryXor (str , g) (str' , g') .gui = addButton str (addButton str' emptyFrame)
  process2GUIBinaryXor (str , g) (str' , g') .method (zero , tt) = return'  (process2GUI g)
  process2GUIBinaryXor (str , g) (str' , g') .method (suc zero , tt) = return'  (process2GUI g')
  process2GUIBinaryXor (str , g) (str' , g') .method (suc (suc ()) , tt)

data ProcessDec : Set where
  startEvent :  String → ProcessDec → ProcessDec
  startEventSilent :  ProcessDec → ProcessDec
  endEvent  :  String → ProcessDec
  multiXor        :  List (String ×  ProcessDec)
                →  ProcessDec
  activity     :  String → ProcessDec → ProcessDec
  activitySilent :  ProcessDec → ProcessDec


mutual
  liftProcessDecl : List (String ×  ProcessDec)
                                       → List (String ×  Process)
  liftProcessDecl [] = []
  liftProcessDecl ((str , p) ∷ l) =
             (str , liftProcessDec p)
             ∷ liftProcessDecl l


  liftProcessDec : ProcessDec → Process
  liftProcessDec (endEvent x) = endEvent x
  liftProcessDec (multiXor l) = multiXor (liftProcessDecl l)
  liftProcessDec (activity str p) = activity str (liftProcessDec p)
  liftProcessDec (activitySilent p) = activitySilent (liftProcessDec p)
  liftProcessDec (startEvent str p) = startEvent str (liftProcessDec p)
  liftProcessDec (startEventSilent p) = startEventSilent (liftProcessDec p)


processDec2GUI : ∀ {i}  → ProcessDec → GUI {i}
processDec2GUI {i} p = process2GUI (liftProcessDec p)

processDec2GuiState : ProcessDec → GuiState
processDec2GuiState p = state (processDec2GUI {∞} p) notStarted


processDec2GUIxor : {i : Size} → List (String × ProcessDec) → GUI {i}
processDec2GUIxor {i} l = process2GUIxor {i} (liftProcessDecl l)

processDec2GUIxorState : List (String × ProcessDec)
                                 → GuiState
processDec2GUIxorState l = state (processDec2GUIxor l) notStarted



processDec2GUIxorNrButtons : {i : Size}
                                (l : List (String × ProcessDec))
                                → (frame2NrButtons (processDec2GUIxor {i} l .gui))
                                  ≡ (lengthL l)
processDec2GUIxorNrButtons {i} [] = refl
processDec2GUIxorNrButtons {i} (x ∷ l) = cong suc (processDec2GUIxorNrButtons l)


processDec2GUIxorNrTextboxes : {i : Size}
                                (l : List (String × ProcessDec))
                                → (frame2NrTextboxes (processDec2GUIxor {i} l .gui))
                                  ≡ 0
processDec2GUIxorNrTextboxes {i} [] = refl
processDec2GUIxorNrTextboxes {i} (x ∷ l) = processDec2GUIxorNrTextboxes l


process2State : Process → GuiState
process2State b
    = state (process2GUI b) notStarted
