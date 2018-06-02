
module GUI.GUIModelVers3 where

-- like GUIModelVers2.agda
-- but using GUIDefinitionsVers2.agda


open import StateSizedIO.GUI.BaseStateDependent
open import StateSizedIO.writingOOsUsingIOVers4ReaderMethods hiding (nˢ) renaming(execˢⁱ to execᵢ ; returnˢⁱ to returnᵢ)
open import GUI.GUIDefinitionsVers2
open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import SizedIO.Console
open import heap.libraryVec
-- open IOInterfaceˢ public

open import Relation.Nullary
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.String
open import Data.Unit
open import Data.Maybe
open import Size
open import Relation.Binary.PropositionalEquality.Core -- public
open import Relation.Binary.PropositionalEquality hiding (setoid ; preorder ; decSetoid; [_]) -- public
open import Data.Sum hiding (map) -- public
open import Data.Bool.Base renaming (T to IsTrue)
open import Function

-- infix 3 _goesThru_

infixl 3 _>>>_

-- How many trivial io commands such as putStrLn are ignored in the model
skippedIOcmds : ℕ
skippedIOcmds = 2

IOCommand = ConsoleCommand
IOResponse = ConsoleResponse

-- test = _×_

-- cmpStruc : CompStruc
-- cmpStruc = compStrucEx

-- c : Components compStrucEx
-- c = frame


-- StateAndGuiObj : Set
-- StateAndGuiObj = Σ[ s ∈ Frame ] (FrameObj {∞} s )

-- was Σ[ s ∈ GUIStateˢ compStrucEx frame ] (GUIel compStrucEx c) × (FrameGUIObj {∞} s )

-- 

-- data MethodStarted (s : GUIStateˢ compStrucEx c)
--                    (obj : FrameGUIObj {∞} s) : Set where
--    notStarted : MethodStarted s obj
--    started :    (m    : GUIMethodˢ compStrucEx frame s) (pr : IO consoleI ∞ StateAndGuiObj)
--                 → MethodStarted s obj

-- 

data MethodStarted (g : GUI) : Set where
   notStarted : MethodStarted g
   started :   (m    : GUIMethod g)
               (pr : IO consoleI ∞ GUI)
               → MethodStarted g

data GuiState : Set where
   state : (g       : GUI)
           (m       : MethodStarted g) → GuiState



GuiCmd : (s : GuiState) → Set
GuiCmd  (state g notStarted)
       = GUIMethod g
GuiCmd  (state g (started m (exec' c f)))
       = IOResponse c
GuiCmd  (state g (started m (return' a)))
       = ⊤

-- modelGuiResponse : Set
-- modelGuiResponse = ⊤




{-
handlerReturnTypeToGUI :
          (g       : GUI)
          (m       : GUIMethod  g)
          (res :  Σ[ r ∈ GUIResult g m ]
                  FrameObj {∞} (nextGUIFrame g m r))
           → GUI
handlerReturnTypeToGUI g m (r , obj') = guic (nextGUIFrame g m r)  obj'

--  handlerReturnTypeToGUI g prop obj (changedAttributes prop' , obj') = g , prop' , obj'
--   handlerReturnTypeToGUI g prop obj (changedGUI g' prop' , obj') = g' , prop' , obj'

-- Old name in old code was: "HandlerIOType"
--



GUIObjIOType : (i : Size)(s : Frame)
               (m : FrameMethod  s)
               → Set
GUIObjIOType i s m = IO∞ consoleI ∞
                        (Σ[ r ∈ FrameResult s m ]
                           FrameObj  {∞} (nextFrame s m r))


guiNextProgramStarted : (g : GUI)
                        (m : GUIMethod g)
                        → IO consoleI ∞ GUI
guiNextProgramStarted g m =
     force (fmap ∞  (handlerReturnTypeToGUI g m) (g .obj .method m))

-}

guiNextaux : (s : GUI)
                  (m : GUIMethod s)
                  (pr : IO consoleI ∞ GUI)
                  (skippedCms : ℕ)
                  → GuiState
guiNextaux g m (exec' (putStrLn s₁) f) (suc n) =
    guiNextaux g m (force (f _)) n
guiNextaux g m  (exec' c' f) n =
        state g (started m (exec' c' f))
guiNextaux g m  (return' g' ) n =
        state g' notStarted

{- (guic sNew  objNew) -}


guiNext : (g : GuiState) → GuiCmd g →  GuiState
guiNext (state g notStarted) m     =
       guiNextaux g m  (g .method m)  skippedIOcmds
guiNext (state g (started m (exec' c' f))) c =
       guiNextaux g m (force (f c)) skippedIOcmds
guiNext (state g (started m (return' g'))) c =
         state g' notStarted

mutual
--\GUIModel
   data GuiCmds : GuiState → Set where
     nilCmd : {g : GuiState} →  GuiCmds g
     _>>>_ :  {g : GuiState} (l : GuiCmds g)
              (c : GuiCmd (guiNexts g l))
              → GuiCmds g
     _>>>'_wproof_,,,_ :  {g : GuiState} (l : GuiCmds g)
              (c : GuiCmd (guiNexts g l))
              (g' : GuiState)
              (p : guiNext (guiNexts g l) c ≡  g')
              → GuiCmds g

   guiNexts : (g : GuiState) → GuiCmds g → GuiState
   guiNexts g nilCmd = g
   guiNexts g (l >>> c') = guiNext (guiNexts g l) c'
   guiNexts g (l >>>' c' wproof g' ,,, p) = g'

data _-gui->_ (s : GuiState) :
              (s' : GuiState ) → Set where
 refl-gui-> :  s -gui-> s
 step       :  {s' : GuiState}(c : GuiCmd s)
               (next : guiNext s c -gui-> s')
               → s -gui-> s'


data _-gui->¹_ (s : GuiState )
               : (s' : GuiState)→ Set where
   step :  (c : GuiCmd s)
           → s -gui->¹ guiNext s c






nextGui : (s : GuiState)(c : GuiCmd s) → GuiState
nextGui s c = guiNext s c



modelToIOprog : (g : GuiState) → Maybe (IO consoleI ∞ GUI)
modelToIOprog (state g notStarted) = nothing
modelToIOprog (state g (started s₁ pr)) = just pr


nextGuiProg : (s : GuiState)(c : GuiCmd s)
              → Maybe (IO consoleI ∞ GUI)
nextGuiProg s c = modelToIOprog (nextGui s c)



guiNext' : (s : GuiState)(c : GuiCmd s)
               → GuiState
guiNext' (state g notStarted) m     =
       state g (started m (g .method m) )
guiNext' (state g (started m (exec' c' f))) c =
       state g (started m (force (f c)))
guiNext' (state g (started m (return' g'))) c =
       state g'  notStarted



data _-gui->¹'_ (m : GuiState ) : (m' : GuiState)→ Set where
   step : (c : GuiCmd m) → m -gui->¹' guiNext' m c

nextGui' : (m : GuiState)(c : GuiCmd m) → GuiState
nextGui' m c = guiNext' m c



--
-- This is from GUIModelAdvancedsimplified in old code:
--

_goesThru_ :  {s s' : GuiState}
              (q : s -gui-> s')
              (t : GuiState) → Set
_goesThru_ {s} (step c q) t   =  s ≡ t ⊎ q goesThru t
_goesThru_ {s} refl-gui-> t   =  s ≡ t



-- _goesThru_ {s} (execᵢ c f) t = s ≡ t ⊎ (f _) goesThru t
-- _goesThru_ {s} (returnᵢ a) t = s ≡ t


goesThruSelf : {s s' : GuiState} (q : s -gui-> s')
               → q goesThru s

goesThruSelf (step c next) = inj₁ refl
goesThruSelf refl-gui->    = refl

-- goesThruSelf (execᵢ c f) = inj₁ refl
-- goesThruSelf (returnᵢ a) = refl

--\GUIModel
data  _-eventually->_ :
      (start final : GuiState) → Set where
  hasReached  :  {s : GuiState} → s -eventually-> s
  next :  {start final : GuiState}
          (fornext :  (m :  GuiCmd start)
                      →  (guiNext start m) -eventually-> final)
          → start -eventually-> final

-- We define short forms for inputs used in the model
--    used as GuiCmd
--    in  guiNext  and guiNexts

--    start -eventuallyP-> P
--  expresses that from start one reaches eventually a state which fulfiles P

data  _-eventuallyP->_ : (start : GuiState)(P     : GuiState → Set)  →  Set where
  hasReached  :  {s  : GuiState}{P     : GuiState → Set}
                 → P s → s -eventuallyP-> P
  next :  {start  : GuiState}{P : GuiState → Set}
          (fornext :  (m :  GuiCmd start)
                      →  (guiNext start m) -eventuallyP-> P)
          → start -eventuallyP-> P

_-eventuallyPb->_ : (start : GuiState)(P     : GuiState → Bool)  →  Set
start -eventuallyPb-> P = start -eventuallyP-> (IsTrue ∘ P)


data  _-eventuallyP'->_avoiding_ : (start : GuiState)(P  Q   : GuiState → Set)
                                   →  Set where
  hasReached  :  {s  : GuiState}{P   Q  : GuiState → Set}
                 → ¬ (Q s) → P s → s -eventuallyP'-> P avoiding Q
  next :  {start  : GuiState}{P Q : GuiState → Set}
          → ¬ (Q start)
          → (fornext :  (m :  GuiCmd start)
                      →  (guiNext start m) -eventuallyP'-> P avoiding Q)
          → start -eventuallyP'-> P avoiding Q

_-eventuallyPb'->_avoiding_ : (start : GuiState)(P   Q  : GuiState → Bool)  →  Set
start -eventuallyPb'-> P avoiding Q = start -eventuallyP'-> (IsTrue ∘ P) avoiding (IsTrue ∘ Q)




-- inductive version of forAllReachable
-- should be equivalent to forAllReachable of GUIModelInductionTheoremsVers3

data forAllReachable : (s : GuiState)(P : GuiState → Set)  → Set where
  forAllReach : {s : GuiState}{P : GuiState → Set}(p : P s)
                (fornext : (m : GuiCmd s) → forAllReachable (guiNext s m) P)
                → forAllReachable s P

forAllReachableb :  (s : GuiState) (P : GuiState → Bool) → Set
forAllReachableb s P = forAllReachable s (IsTrue ∘ P)



data forAllReachableAvoiding : (s : GuiState)(P Q : GuiState → Set)  → Set where
  forAllReach : {s : GuiState}{P Q : GuiState → Set}
                (q : ¬ (Q s))
                (p : P s)
                (fornext : (m : GuiCmd s) → forAllReachableAvoiding (guiNext s m) P Q)
                → forAllReachableAvoiding s P Q

forAllReachableAvoidingb :  (s : GuiState) (P Q : GuiState → Bool) → Set
forAllReachableAvoidingb s P Q = forAllReachableAvoiding s (IsTrue ∘ P) (IsTrue ∘ Q)



btnClick : Fin 1 × ⊤
btnClick = (zero , _)

textboxInput : String → Fin 1 × String
textboxInput str = (zero , str)

textboxInput2 : (str1 str2 : String) → Fin 1 × String × String
textboxInput2 str1 str2 = (zero , str1 , str2)

textboxInput3 : (str1 str2  str3 : String) → Fin 1 × String × String ×  String
textboxInput3 str1 str2  str3 = (zero , str1 , str2 , str3)

textboxInput4 : (str1 str2  str3 str4 : String) → Fin 1 × String × String ×  String × String
textboxInput4 str1 str2  str3 str4 = (zero , str1 , str2 , str3 , str4)


frameProp2StateProp : (f : Frame →  Bool)
                      → GuiState → Bool
frameProp2StateProp f (state g notStarted) = f (g .gui)
frameProp2StateProp f (state g (started m pr)) = false

-- decide whether frame is a  frame
-- consisting of a single button with label str and no other elements only
frameIsSimpleText : String → Frame → Bool
frameIsSimpleText str (addButton str' emptyframe) =  primStringEquality str str'
frameIsSimpleText str fr = false

frameIsXorWithTexts : (str1 str2 : String) → Frame → Bool
frameIsXorWithTexts str1 str2 (addButton str1' (addButton str2' emptyframe))
                         =  primStringEquality str1 str1'
                            ∧ primStringEquality str2 str2'
frameIsXorWithTexts str str2 fr = false

-- property that the frame doesn't not contain a button with a
--  specific string
frameDoesNotContainTextButton : String → Frame → Bool
frameDoesNotContainTextButton str emptyFrame = true
frameDoesNotContainTextButton str (addButton btnStr fr) = not (primStringEquality str btnStr) ∧ frameDoesNotContainTextButton str fr
frameDoesNotContainTextButton str (addLabel x fr) = frameDoesNotContainTextButton str fr
frameDoesNotContainTextButton str (addTextbox x fr) = frameDoesNotContainTextButton str fr



-- decide whether guiState consists of
-- a single button with label str and no other elements only
stateIsSimpleText : String → GuiState → Bool
stateIsSimpleText str = frameProp2StateProp (frameIsSimpleText str)

stateIsXorWithTexts : (str1 str2 : String) → GuiState → Bool
stateIsXorWithTexts str1 str2  = frameProp2StateProp (frameIsXorWithTexts str1 str2)

stateDoesNotContainTextButton : String → GuiState → Bool
stateDoesNotContainTextButton str = frameProp2StateProp (frameDoesNotContainTextButton str)

-- if guistate consists of a single button with label str1
-- then the handler has no interaction and returns directly
--  a state with a single button with label str2

-- aux2 :
--   handler p resturns directly and ends with a frame with one button with
--     label str2
ifFrameIsSmplTxt1NextIsSmplTxt2aux2 : (str2 : String)
            (p : IO consoleI ∞ GUI)
            → Bool
ifFrameIsSmplTxt1NextIsSmplTxt2aux2 str2 (exec' c f) = false
ifFrameIsSmplTxt1NextIsSmplTxt2aux2 str2 (return' g) = frameIsSimpleText str2 (g .gui)


-- aux1 :
--   if fr is a frame consisting of a single button with string str1
--   then the next state is reached with no interaction is a
--   frame with single button with string str2
ifFrameIsSmplTxt1NextIsSmplTxt2aux1 : (str1 str2 : String)
            (fr : Frame)
            (m  : GUIObj fr) → Bool
ifFrameIsSmplTxt1NextIsSmplTxt2aux1 str1 str2 (addButton str3 emptyFrame) hand = not (primStringEquality str1 str2) ∨ ifFrameIsSmplTxt1NextIsSmplTxt2aux2 str2 (hand {∞} ( zero , tt ))
ifFrameIsSmplTxt1NextIsSmplTxt2aux1 str1 str2 fr m = true

test = emptyFrame


ifFrameIsSmplTxt1NextIsSmplTxt2 : (str1 str2 : String)(g : GuiState) → Bool
ifFrameIsSmplTxt1NextIsSmplTxt2 str1 str2
                                (state g notStarted)
                                = ifFrameIsSmplTxt1NextIsSmplTxt2aux1 str1 str2 (g .gui) (g .method)
ifFrameIsSmplTxt1NextIsSmplTxt2 str1 str2 g = true
