-- \BusinessProcessVersThree

module GUI.BusinessProcessVers3 where

-- Version like BusinessProcess.agda
-- but usinig the simplified version from
--   GUIDefinitionsVers2.agdao

open import Data.String -- hiding (length)
open import Data.List renaming (map to mapL ; length to lengthL)
open import Data.Product hiding (map)
open import Data.Nat
open import Size
open import Data.Fin renaming (_+_ to _+fin_)
open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import Relation.Binary.PropositionalEquality hiding (setoid ; preorder ; decSetoid; [_])
open import Data.Sum hiding (map)


open import heap.libraryVec
open import GUI.GUIDefinitionsVers2
-- open import GUI.GUIDefinitionsBase
open import GUI.GUIExampleLibVers2
open import StateSizedIO.GUI.BaseStateDependent
open import GUI.GUIModelVers3


-- \BusinessProcess
data BusinessProcess : Set where
  startEvent :  String → BusinessProcess → BusinessProcess
  startEventSilent :  BusinessProcess → BusinessProcess
  endEvent  :  String → BusinessProcess
  xor        :  List (String ×  BusinessProcess)
                →  BusinessProcess
{-  input1     : String → (String → BusinessProcess)
               → BusinessProcess-}
  input      :  {n : ℕ} → Tuple String n
                →  (Tuple String n → BusinessProcess)
                →  BusinessProcess
  activity     :  String → BusinessProcess → BusinessProcess
  activitySilent :  BusinessProcess → BusinessProcess

-- with Tuple slit m into (str' , m)
--  and used str' for the first two and m for the last goal


businessProcess2GUIxorFrame : (l : List (String × BusinessProcess))
                               → Frame
businessProcess2GUIxorFrame [] = emptyFrame
businessProcess2GUIxorFrame ((str , p) ∷ l) = addButton str (businessProcess2GUIxorFrame l)


mutual
  businessProcess2GUI : ∀ {i}  → BusinessProcess
                             → GUI {i}
  businessProcess2GUI (endEvent x) = endEventGUI x
  businessProcess2GUI (xor l) = businessProcess2GUIxor l
  businessProcess2GUI (input {n} str f) = multiTextboxGUI n str (λ v → businessProcess2GUI (f v))
  businessProcess2GUI (startEvent str b)  =   onebuttonStrGUI str (businessProcess2GUI b)
  businessProcess2GUI (startEventSilent b)  =   businessProcess2GUI b
  businessProcess2GUI (activity str b)  =   onebuttonStrGUI str (businessProcess2GUI b)
  businessProcess2GUI (activitySilent b)  =   businessProcess2GUI b


  businessProcess2Gui : BusinessProcess → GUI
  businessProcess2Gui = businessProcess2GUI {∞}

  businessProcess2GUIxorHandl : {i : Size} → (l : List (String × BusinessProcess))
                              → (m : FrameMethod (businessProcess2GUIxorFrame l))
                              → GUI {i}
  businessProcess2GUIxorHandl [] (() , _)
  businessProcess2GUIxorHandl ((str , g) ∷ l) (zero , _) = businessProcess2GUI g
  businessProcess2GUIxorHandl ((str , g) ∷ l) (suc m , s) = businessProcess2GUIxorHandl l (m , s)

  businessProcess2GUIxor : {i : Size} → List (String × BusinessProcess) → GUI {i}
  businessProcess2GUIxor l .gui = businessProcess2GUIxorFrame l
  businessProcess2GUIxor l .method m =  return' (businessProcess2GUIxorHandl l m)


{-
-- an unsized version for presentation purposes
-- \BusinessProcess
--BEGINBusinessProcesstoGUI
  businessProcess2Gui : BusinessProcess → GUI
--END
  businessProcess2Gui = businessProcess2GUI {∞}

  businessProcess2GUIxor : {i : Size} → List (String × BusinessProcess) → GUI {i}
  businessProcess2GUIxor [] .gui = emptyFrame
  businessProcess2GUIxor [] .method ()
  businessProcess2GUIxor ((str , _) ∷ l) .gui = addButton str (businessProcess2GUIxor l .gui)
  businessProcess2GUIxor ((str , g) ∷ l) .method (zero , _) = return'  (businessProcess2GUI g)
  businessProcess2GUIxor ((str , _) ∷ l) .method (suc m , s) = businessProcess2GUIxor l .method (m , s)
-}




data BusinessProcessDec : Set where
  startEvent :  String → BusinessProcessDec → BusinessProcessDec
  startEventSilent :  BusinessProcessDec → BusinessProcessDec
  endEvent  :  String → BusinessProcessDec
  xor        :  List (String ×  BusinessProcessDec)
                →  BusinessProcessDec
  activity     :  String → BusinessProcessDec → BusinessProcessDec
  activitySilent :  BusinessProcessDec → BusinessProcessDec


mutual
  liftBusinessProcessDecl : List (String ×  BusinessProcessDec)
                                       → List (String ×  BusinessProcess)
  liftBusinessProcessDecl [] = []
  liftBusinessProcessDecl ((str , p) ∷ l) =
             (str , liftBusinessProcessDec p)
             ∷ liftBusinessProcessDecl l


  liftBusinessProcessDec : BusinessProcessDec → BusinessProcess
  liftBusinessProcessDec (endEvent x) = endEvent x
  liftBusinessProcessDec (xor l) = xor (liftBusinessProcessDecl l)
  liftBusinessProcessDec (activity str p) = activity str (liftBusinessProcessDec p)
  liftBusinessProcessDec (activitySilent p) = activitySilent (liftBusinessProcessDec p)
  liftBusinessProcessDec (startEvent str p) = startEvent str (liftBusinessProcessDec p)
  liftBusinessProcessDec (startEventSilent p) = startEventSilent (liftBusinessProcessDec p)


businessProcessDec2GUI : ∀ {i}  → BusinessProcessDec → GUI {i}
businessProcessDec2GUI {i} p = businessProcess2GUI (liftBusinessProcessDec p)

businessProcessDec2GuiState : BusinessProcessDec → GuiState
businessProcessDec2GuiState p = state (businessProcessDec2GUI {∞} p) notStarted


businessProcessDec2GUIxor : {i : Size} → List (String × BusinessProcessDec) → GUI {i}
businessProcessDec2GUIxor {i} l = businessProcess2GUIxor {i} (liftBusinessProcessDecl l)

businessProcessDec2GUIxorState : List (String × BusinessProcessDec)
                                 → GuiState
businessProcessDec2GUIxorState l = state (businessProcessDec2GUIxor l) notStarted



businessProcessDec2GUIxorNrButtons : {i : Size}
                                (l : List (String × BusinessProcessDec))
                                → (frame2NrButtons (businessProcessDec2GUIxor {i} l .gui))
                                  ≡ (lengthL l)
businessProcessDec2GUIxorNrButtons {i} [] = refl
businessProcessDec2GUIxorNrButtons {i} (x ∷ l) = cong suc (businessProcessDec2GUIxorNrButtons l)


businessProcessDec2GUIxorNrTextboxes : {i : Size}
                                (l : List (String × BusinessProcessDec))
                                → (frame2NrTextboxes (businessProcessDec2GUIxor {i} l .gui))
                                  ≡ 0
businessProcessDec2GUIxorNrTextboxes {i} [] = refl
businessProcessDec2GUIxorNrTextboxes {i} (x ∷ l) = businessProcessDec2GUIxorNrTextboxes l


businessProcess2State : BusinessProcess → GuiState
businessProcess2State b
    = state (businessProcess2GUI b) notStarted
