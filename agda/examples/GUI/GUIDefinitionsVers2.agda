module GUI.GUIDefinitionsVers2 where

-- simplifed verison of GUIDefinitions.agda and GUIDefinitionsBase.agda
-- where
--    the GUI data type is defined inductively and not generically
--     (simpler to use)
-- the handler is directly an io program returning the next GUI rather
--    than being an object.

open import Data.String
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Size

open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import SizedIO.Console using (consoleI; translateIOConsole)
open import heap.libraryVec

data Frame  : Set where
  emptyFrame  :  Frame
  addButton   :  String → Frame → Frame
  addLabel    :  String → Frame → Frame
  addTextbox  :  String → Frame → Frame


frame2NrButtons : (f : Frame) → ℕ
frame2NrButtons emptyFrame = 0
frame2NrButtons (addButton _ f) = suc (frame2NrButtons f)
frame2NrButtons (addLabel _ f) = frame2NrButtons f
frame2NrButtons (addTextbox _ f) = frame2NrButtons f

frame2NrTextboxes : (f : Frame) → ℕ
frame2NrTextboxes emptyFrame = 0
frame2NrTextboxes (addButton _ f) = frame2NrTextboxes f
frame2NrTextboxes (addLabel _ f) = frame2NrTextboxes f
frame2NrTextboxes (addTextbox _ f) = suc (frame2NrTextboxes f)

FrameMethod : Frame → Set
FrameMethod f = Fin (frame2NrButtons f) ×  Tuple String (frame2NrTextboxes f)


mutual
  record GUI {i : Size} : Set where
    coinductive
    constructor guic
    field
      gui     : Frame
      method  : {j : Size< i} → GUIObj {j} gui -- (m : FrameMethod gui) → IO consoleI ∞ (GUI {j})

  GUIObj : {i : Size} → Frame → Set
  GUIObj {i} f = {j : Size< i}(m : FrameMethod f) → IO consoleI ∞ (GUI {j})

open GUI public


GUIMethod : {i : Size} (g : GUI {i}) → Set
GUIMethod g = FrameMethod (g .gui)
