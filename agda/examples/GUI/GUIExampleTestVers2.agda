open import Data.Bool

module GUI.GUIExampleTestVers2   where

-- open import GUIgeneric.Prelude renaming (inj₁ to secondBtn; inj₂ to firstBtn)

-- open import GUIgeneric.PreludeGUI renaming (WxColor to Color) hiding ( _>>_)

open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ) renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
open import GUI.GUIDefinitionsVers2
open import SizedIO.Console
open import SizedIO.Base renaming (IO to IO∞; IO' to IO) hiding (_>>_)

open import Data.String
open import GUI.GUIExampleLibVers2

open import Data.Fin

open import Size
open import Data.Unit
open import Data.Product

-- TODO later Properties of Buttons?
--

twoBtnGUI : Frame
twoBtnGUI = addButton "OK" (addButton "dummy" emptyFrame)

threeBtnGUI : Frame
threeBtnGUI = addButton "OK" (addButton "Chancel" (addButton "dummy" emptyFrame))


putStrLine' : {A : Set} → String → (f : IO∞ consoleI ∞ A) →
           IO consoleI ∞ A
putStrLine' s f = exec' (putStrLn s) (λ _ → f)

syntax putStrLine' s f = putStrLine s >> f

mutual
 obj3Btnaux  : {i : Size}{j : Size< i} → GUI {j}
 obj3Btnaux {i}{j} .gui = threeBtnGUI
 obj3Btnaux {i}{j} .method = obj3Btn {j}


 obj3Btn : ∀ {i} → GUIObj{i} threeBtnGUI
 obj3Btn (suc (suc zero) , _) = putStrLine "OK! Changing Gui!" >>
                                    return (guic twoBtnGUI  obj2Btn)
 obj3Btn {i} {j} (suc zero , _) = putStrLine "Cancel! No change!" >>
                              return (obj3Btnaux {i} {j}) -- (guic threeBtnGUI  (obj3Btn {j}))
 obj3Btn {i} {j} (zero , _)  = putStrLine ">>>>>>>>>>> zero button [NOT WORKING]" >>
                               return (obj3Btnaux {i} {j}) -- return (guic threeBtnGUI  ({!obj3Btn {j}!}))

 obj3Btn (suc (suc (suc ())) , _)

 obj2Btnaux  : {i : Size}{j : Size< i} → GUI {j}
 obj2Btnaux {i}{j} .gui = twoBtnGUI
 obj2Btnaux {i}{j} .method = obj2Btn {j}

 obj2Btn : ∀ {i} → GUIObj {i} twoBtnGUI
 obj2Btn (zero , _) = putStrLine ">>>>>>>>>>> zero button [NOT WORKING]" >>
                        return obj2Btnaux
 obj2Btn (suc zero , _) = putStrLine "OK! Changing Gui!" >>
                          return    obj2Btnaux
 obj2Btn (suc (suc ()), _ )

