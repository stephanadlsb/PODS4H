module GUI.GUIExampleLibVers2 where

open import Data.List
open import Data.String
open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Size
open import Relation.Binary.PropositionalEquality

open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import SizedIO.Console using (putStrLn; consoleI; translateIOConsole)
open import heap.libraryVec

open import GUI.GUIDefinitionsVers2
open import SizedIO.Console using (consoleI; translateIOConsole)


buttonStr : String → Frame
buttonStr str = addButton str emptyFrame

{-
onebuttonStrGUI : {i : Size} → String → GUI {i} → GUI {↑ i}
onebuttonStrGUI str f .gui = buttonStr str
onebuttonStrGUI str f .method m = return' f
-}
onebuttonStrGUIHandler : {i : Size} → (str : String) (g : GUI {i}) → GUIObj {i} (buttonStr str)
onebuttonStrGUIHandler {i} str g {j} m = return' g

onebuttonStrGUI : {i : Size} → String → GUI {i} → GUI {↑ i}
onebuttonStrGUI {i} str g = guic (buttonStr str) (onebuttonStrGUIHandler {i} str g)
{-onebuttonStrGUI {i} str g .gui = buttonStr str
onebuttonStrGUI {i} str g .method =  onebuttonStrGUIHandler {i} str g-}



endEventGUI : String → GUI {∞}
endEventGUI str  = guic (addLabel str emptyFrame) (λ {()})

xorGUI : List (String × GUI {∞}) → GUI {∞}
xorGUI [] .gui = emptyFrame
xorGUI [] .method ()
xorGUI ((str , g) ∷ l) .gui = addButton str (xorGUI l .gui)
xorGUI ((str , g) ∷ l) .method (zero , _) = return' g
xorGUI ((str , g) ∷ l) .method (suc m , x) = xorGUI l .method (m , x)



multiTextboxFrame : (n : ℕ) → Tuple String n → Frame
multiTextboxFrame 0 v = (addButton "Continue" emptyFrame)
multiTextboxFrame 1 str = addLabel str (addTextbox "" (addButton "Continue" emptyFrame))
multiTextboxFrame (suc (suc n)) (str , v) =
                  addLabel str
                  (addTextbox ""
                  (multiTextboxFrame (suc n) v  ))


{-
multiTextboxFrame : (n : ℕ) → Tuple String n → Frame
multiTextboxFrame 0 v = emptyFrame
multiTextboxFrame 1 str = addTextbox (addLabel str (addButton "Continue" emptyFrame))
multiTextboxFrame (suc (suc n)) (str , v) =
                  addTextbox
                  (addLabel str
                  (multiTextboxFrame (suc n) v  ))
-}
{-
test : IO {!!} {!!} {!!}
test = {!!}
-}

multiTextboxHandler : {i : Size}(n k : ℕ) (v : Tuple String n)
                      (f : Tuple String n → Tuple String k → GUI {i})
                      → Tuple String k
                      → GUIObj {↑ i} (multiTextboxFrame n v)
multiTextboxHandler 0 k v f v' (_ , str) = return' (f  str v' )
multiTextboxHandler 1 k v f v' ( _ ,  str )  =
   exec' (putStrLn "Handler is activated >>") λ _ → return (f  str v' )
   --returnGUI (f  str v' )
multiTextboxHandler (suc (suc n)) k (str , v) f v' ( l  , m) =
            multiTextboxHandler (suc n) (suc k) v
             (λ v'' → λ v''' → f (headTuple m , v'')
                                 (tailTuple {String} v''') )
             (consVec {String} (headTuple m)  v')
             (l , tailTuple {String}  m)


multiTextboxGUI : ∀{i} → (n : ℕ) → (v : Tuple String n) → (f : Tuple String n → GUI {i}) →
  GUI {↑ i}
multiTextboxGUI n v f .gui    = multiTextboxFrame n v
multiTextboxGUI n v f .method = multiTextboxHandler n 0 v (λ v _ → f v) _
