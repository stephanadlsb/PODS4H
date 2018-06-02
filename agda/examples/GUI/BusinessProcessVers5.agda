-- \BusinessProcessVersFive

module GUI.BusinessProcessVers5 where

-- version contains business processes where inputs are checked and
--        if inptus are not valid one goes back to the input GUI.
--   there is a back button
-- and uses simplifed version as
-- GUIDefinitionsVers2.agda

open import Data.String hiding (length)
open import Data.List renaming (map to mapL)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Maybe
open import Data.Unit
open import Size
open import Data.Fin renaming (_+_ to _+fin_)
open import Relation.Binary.PropositionalEquality

open import heap.libraryVec
open import SizedIO.Console
open import GUI.GUIDefinitionsVers2
open import GUI.GUIExampleLibVers2
open import GUI.GUIExampleLibVers2Part2
open import StateSizedIO.GUI.BaseStateDependent
open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import GUI.GUIModelVers3

-- Call it business process

-- \BusinessProcess
data BusinessProcess : Set where
  startEvent :  String → BusinessProcess → BusinessProcess
  startEventSilent :  BusinessProcess → BusinessProcess
  endEvent  :  String → BusinessProcess
  xor        :  List (String ×  BusinessProcess)
                →  BusinessProcess
  input      :  {n : ℕ} → Tuple String n
                →  (Tuple String n → Maybe String)
                →  (Tuple String n → BusinessProcess)
                →  BusinessProcess
  activity     :  String → BusinessProcess → BusinessProcess
  activitySilent :  BusinessProcess → BusinessProcess


-- with Tuple slit m into (str' , m)
--  and used str' for the first two and m for the last goal

-- stopProcess is a temporary place holder - it should
--   be replaced by something which kills the window

endOfGuiMsg : String
endOfGuiMsg = "GUI has terminated"

killMsg : String
killMsg = "Finish"

goBackMsg : String
goBackMsg = "Start Again"

killWindow : {i : Size} →  GUI {i}
killWindow = endEventGUI endOfGuiMsg

handlerEndEventGUIWithLoopBack : {i : Size}(restartGui : GUI {i}) →
     (s : Fin 2 × ⊤) → IO consoleI ∞ (GUI {i})
handlerEndEventGUIWithLoopBack restartGui (zero , tt) = return' killWindow
handlerEndEventGUIWithLoopBack restartGui (suc zero , tt) = return' restartGui
handlerEndEventGUIWithLoopBack restartGui (suc (suc ()) , tt)
endEventGUIWithLoopBack  :   {i : Size}
                             (killMsg goBackMsg : String)
                             (restartGui : {j : Size< i} → GUI {j})
                              → GUI {i}
endEventGUIWithLoopBack {i} killMsg goBackMsg restartGui .gui = addButton goBackMsg (addButton killMsg emptyFrame)
endEventGUIWithLoopBack {i} killMsg goBackMsg restartGui .method m  =
            handlerEndEventGUIWithLoopBack restartGui m



endEventGUIWithLoopBackAndMsg : {i : Size}
                                (endMsg : String)
                                (restartGui : {j : Size< i} → GUI {j})
                                → GUI {i}
endEventGUIWithLoopBackAndMsg  endMsg restartGui =
   onebuttonStrGUI endMsg (endEventGUIWithLoopBack killMsg goBackMsg restartGui)


businessProcess2GUIxorFrame : (l : List (String × BusinessProcess))
                               → Frame
businessProcess2GUIxorFrame [] = emptyFrame
businessProcess2GUIxorFrame ((str , p) ∷ l) = addButton str (businessProcess2GUIxorFrame l)


mutual

  businessProcess2GUIaux : ∀ {i}  → (endProcess : GUI {i}) → (current : BusinessProcess) →
                               GUI {i}
  businessProcess2GUIaux endProcess (endEvent endMsg) = endProcess
--         endEventGUIWithLoopBackAndMsg  endMsg (businessProcess2GUIaux  endProcess)
  businessProcess2GUIaux endProcess (xor l) = businessProcess2GUIxor endProcess l
{-
  businessProcess2GUIaux (input {n} str g f) = guic  (multiTextboxFrame n str)
                                                (
              multiTextboxGUIWithCheckFunObj' n str (λ v → businessProcess2GUIaux (f v))
               g
               (businessProcess2GUIaux (input {n} str g f)))
-}
  businessProcess2GUIaux endProcess (input {n} str g f) .gui = multiTextboxFrame n str
  businessProcess2GUIaux endProcess (input {n} str g f) .method {j}
             = multiTextboxGUIWithCheckFunObj n str (λ v → businessProcess2GUIaux endProcess (f v))
               g
               (businessProcess2GUIaux endProcess (input {n} str g f)) {j}
  businessProcess2GUIaux endProcess(startEventSilent b)  =   businessProcess2GUIaux endProcess b
  businessProcess2GUIaux endProcess (startEvent str b)  =   onebuttonStrGUI str  (businessProcess2GUIaux endProcess b)
  businessProcess2GUIaux endProcess (activity str b)  =   onebuttonStrGUI str  (businessProcess2GUIaux endProcess b)
  businessProcess2GUIaux endProcess (activitySilent b)  =   businessProcess2GUIaux endProcess b

-- an unsized version for presentation purposes
-- \BusinessProcess
  businessProcess2Gui : (endProcess : GUI)(current : BusinessProcess) → GUI
  businessProcess2Gui endProcess current = businessProcess2GUIaux {∞} endProcess current

  businessProcess2GUIxorHandl : {i : Size} → (endProcess : GUI {i})
                              → (l : List (String × BusinessProcess))
                              → (m : FrameMethod (businessProcess2GUIxorFrame l))
                              → GUI {i}
  businessProcess2GUIxorHandl endProcess [] (() , _)
  businessProcess2GUIxorHandl endProcess ((str , g) ∷ l) (zero , _) = businessProcess2GUIaux endProcess g
  businessProcess2GUIxorHandl endProcess ((str , g) ∷ l) (suc m , s) = businessProcess2GUIxorHandl endProcess l (m , s)

  businessProcess2GUIxor : {i : Size} → (endProcess : GUI {i}) → List (String × BusinessProcess) → GUI {i}
  businessProcess2GUIxor endProcess l .gui = businessProcess2GUIxorFrame l
  businessProcess2GUIxor endProcess l .method m =  return' (businessProcess2GUIxorHandl endProcess  l m)


{-
  businessProcess2GUIxor : {i : Size} → List (String × BusinessProcess) → GUI {i}
  businessProcess2GUIxor [] .gui = emptyFrame
  businessProcess2GUIxor [] .method ()
  businessProcess2GUIxor ((str , _) ∷ l) .gui = addButton str (businessProcess2GUIxor l .gui)
  businessProcess2GUIxor ((str , g) ∷ l) .method (zero , _) =  return'  {!(businessProcess2GUI g)!}
  businessProcess2GUIxor ((str , _) ∷ l) .method (suc m , s) = businessProcess2GUIxor l .method (m , s)
-}

mutual
  businessProcess2GUI : ∀ {i}  → (current : BusinessProcess) →
                                  GUI {i}
  businessProcess2GUI {i} current = businessProcess2GUIaux (businessProcess2GUIend {i} current) current

  businessProcess2GUIend : ∀{i} → (current : BusinessProcess) →  GUI {i}
  businessProcess2GUIend {i} current .gui = addButton goBackMsg (addButton killMsg emptyFrame)
  businessProcess2GUIend {i} current .method {j} m   = businessProcess2GUIendHandler {j} current m


  businessProcess2GUIendHandler : {i : Size}(current : BusinessProcess) → (s : Fin 2 × ⊤) → IO consoleI ∞ (GUI {i})
  businessProcess2GUIendHandler current (zero , tt) = return' (businessProcess2GUIaux' current)
  businessProcess2GUIendHandler current (suc zero , tt) = return' killWindow
  businessProcess2GUIendHandler current (suc (suc ()) , tt)

{-
  businessProcess2GUIend : ∀{i} → (current : BusinessProcess) →  GUI {i}
  businessProcess2GUIend {i} current = endEventGUIWithLoopBackAndMsg "end" (businessProcess2GUIaux' {i} current)
-}

  businessProcess2GUIaux' : ∀ {i}  → (current : BusinessProcess) →
                                     {j : Size< i} → GUI {j}
  businessProcess2GUIaux' {i} current {j} = businessProcess2GUI {j} current

businessProcess2GUIxorNrButtons : {i : Size}→ (endProcess : GUI {i})
                                (l : List (String × BusinessProcess))
                                → (frame2NrButtons (businessProcess2GUIxor {i} endProcess l .gui))
                                  ≡ (length l)
businessProcess2GUIxorNrButtons {i} endProcess [] = refl
businessProcess2GUIxorNrButtons {i} endProcess (x ∷ l) = cong suc (businessProcess2GUIxorNrButtons endProcess l)


businessProcess2GUIxorNrTextboxes : {i : Size}→ (endProcess : GUI {i})
                                (l : List (String × BusinessProcess))
                                → (frame2NrTextboxes (businessProcess2GUIxor {i} endProcess l .gui))
                                  ≡ 0
businessProcess2GUIxorNrTextboxes {i} endProcess [] = refl
businessProcess2GUIxorNrTextboxes {i} endProcess (x ∷ l) = businessProcess2GUIxorNrTextboxes endProcess l


-- the subset of business processes for which we can have a decision procedure
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


businessProcessDec2GUIaux : ∀ {i}  → (endProcess : GUI {i}) → BusinessProcessDec → GUI {i}
businessProcessDec2GUIaux {i} endProcess p = businessProcess2GUIaux endProcess (liftBusinessProcessDec p)

businessProcessDec2GUI : ∀ {i}  → BusinessProcessDec → GUI {i}
businessProcessDec2GUI {i} p = businessProcess2GUI (liftBusinessProcessDec p)

businessProcessDec2GuiStateaux : (endProcess : GUI {∞ }) → BusinessProcessDec → GuiState
businessProcessDec2GuiStateaux endProcess p = state (businessProcessDec2GUIaux {∞} endProcess p) notStarted

businessProcessDec2GuiState : BusinessProcessDec → GuiState
businessProcessDec2GuiState p = state (businessProcessDec2GUI {∞}  p) notStarted


businessProcessDec2GUIxor : {i : Size} → (endProcess : GUI {i}) → List (String × BusinessProcessDec) → GUI {i}
businessProcessDec2GUIxor {i} endProcess l = businessProcess2GUIxor {i} endProcess (liftBusinessProcessDecl l)

businessProcessDec2GUIxorState : (endProcess : GUI {∞}) → List (String × BusinessProcessDec)
                                 → GuiState
businessProcessDec2GUIxorState endProcess l = state (businessProcessDec2GUIxor endProcess l) notStarted



businessProcessDec2GUIxorNrButtons : {i : Size}
                                (endProcess : GUI {i}) →
                                (l : List (String × BusinessProcessDec))
                                → (frame2NrButtons (businessProcessDec2GUIxor {i} endProcess l .gui))
                                  ≡ (length l)
businessProcessDec2GUIxorNrButtons {i} endProcess [] = refl
businessProcessDec2GUIxorNrButtons {i} endProcess (x ∷ l) = cong suc (businessProcessDec2GUIxorNrButtons endProcess l)




businessProcessDec2GUIxorNrTextboxes : {i : Size}
                                (endProcess : GUI {i}) →
                                (l : List (String × BusinessProcessDec))
                                → (frame2NrTextboxes (businessProcessDec2GUIxor {i} endProcess l .gui))
                                  ≡ 0
businessProcessDec2GUIxorNrTextboxes {i} endProcess [] = refl
businessProcessDec2GUIxorNrTextboxes {i} endProcess (x ∷ l) = businessProcessDec2GUIxorNrTextboxes endProcess l


businessProcess2State : (endProcess : GUI {∞}) → BusinessProcess → GuiState
businessProcess2State endProcess b
    = state (businessProcess2GUIaux endProcess b) notStarted
