module GUI.GUIExampleLibVers2Part2 where

open import Size
open import Data.Nat
open import Data.String
open import Data.Maybe.Base
open import StateSizedIO.GUI.BaseStateDependent
-- open import SizedIO.Base using (IOInterface; Command; Response; IO; return)
open import Data.Product
open import Relation.Binary.PropositionalEquality


open import heap.libraryVec
open import SizedIO.Console using (consoleI; translateIOConsole)
open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import GUI.GUIExampleLibVers2
open import GUI.GUIDefinitionsVers2

multiTextboxFrameNrBtns : (n : ℕ)(l : Tuple String (suc n))
                          → frame2NrButtons (multiTextboxFrame (suc n) l ) ≡ 1
multiTextboxFrameNrBtns zero l = refl
multiTextboxFrameNrBtns (suc n) (s , l) = multiTextboxFrameNrBtns n l


multiTextboxFrameNrTextboxes : (n : ℕ)(l : Tuple String n)
                          → frame2NrTextboxes (multiTextboxFrame n l ) ≡ n
multiTextboxFrameNrTextboxes zero l = refl
multiTextboxFrameNrTextboxes (suc zero) l = refl
multiTextboxFrameNrTextboxes (suc (suc n)) (s , l) = cong suc (multiTextboxFrameNrTextboxes (suc n) l)


transferNrTextboxesMultiTextBoxFrame : {A : Set}(n : ℕ) (str : Tuple String n)
                                       (check : Tuple String n → Maybe A)
                                       → Tuple String (frame2NrTextboxes (multiTextboxFrame n str))
                                       → Maybe A
transferNrTextboxesMultiTextBoxFrame n str check t rewrite  (multiTextboxFrameNrTextboxes n str)
             = check t


conditionalIO : {i : Size}
                (str : Maybe String) -- just s means input was wrong and an error message with this string is returned
                                     -- and you return to original gui
                                     -- nothing means was okay
                (originalGUI : GUI {i})
                (nextGUI     : IO consoleI ∞ (GUI {i}))
                → IO consoleI ∞ (GUI {i})
conditionalIO (just error) originalGUI nextGUI = return' (onebuttonStrGUI error originalGUI)
conditionalIO nothing originalGUI nextGUI = nextGUI

multiTextboxGUIWithCheckFunObj
    : {i : Size} (n : ℕ) (v : Tuple String n)
      (f : Tuple String n → GUI {i})
      (check : Tuple String n  → Maybe String)
      (originalGui : GUI {i})
       →   GUIObj {↑ i} (multiTextboxFrame n v)
multiTextboxGUIWithCheckFunObj {i} n v f check originalGui (k , str) =
     conditionalIO (transferNrTextboxesMultiTextBoxFrame n v check str) originalGui (multiTextboxHandler n 0 v (λ v _ → f v) _ (k , str))


multiTextboxGUIWithCheckFunObj'
    : {i : Size} (n : ℕ) (v : Tuple String n)
      (f : Tuple String n → GUI {i})
      (check : Tuple String n  → Maybe String)
      (originalGui : GUI {i})
      {j : Size< i}
       →   GUIObj {↑ i} (multiTextboxFrame n v)
multiTextboxGUIWithCheckFunObj' {i} n v f check originalGui {j} (k , str)  =
     conditionalIO (transferNrTextboxesMultiTextBoxFrame n v check str) originalGui (multiTextboxHandler n 0 v (λ v _ → f v) _ (k , str))





multiTextboxGUIWithCheckFun
    : {i : Size} (n : ℕ) (v : Tuple String n)
      (f : Tuple String n → GUI {i})
      (check : Tuple String n  → Maybe String)
      (originalGui : GUI {i})
       →   GUI {↑ i}
multiTextboxGUIWithCheckFun n v f check originalGui  .gui = multiTextboxFrame n v
multiTextboxGUIWithCheckFun {i} n v f check originalGui .method (k , str) =
     conditionalIO (transferNrTextboxesMultiTextBoxFrame n v check str) originalGui (multiTextboxHandler n 0 v (λ v _ → f v) _ (k , str))
-- (guiEl2NrTextboxes frameCmpStruc frame (multiTextboxFrame n v))
