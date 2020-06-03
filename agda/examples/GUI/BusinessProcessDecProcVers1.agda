module GUI.BusinessProcessDecProcVers1 where

-- contains a decision procedure for Business processes
-- Based on BusinessProcessVers3  and GUIDefinitionsVers2.agda

open import Data.String hiding (length)
open import Data.List renaming (map to mapL)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.Maybe
open import Size
open import Relation.Nullary using ( ¬_ )
open import lib.libraryDec
open import Data.Fin renaming (_+_ to _+fin_)
open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import GUI.BusinessProcessVers3
open import GUI.GUIModelVers3
open import GUI.GUIExampleLibVers2Part2
open import Relation.Binary.PropositionalEquality
open import Function

open import heap.libraryMaybe
open import heap.libraryBool
open import heap.libraryVec
open import heap.libraryFin
open import GUI.GUIDefinitionsVers2
-- open import GUI.GUIDefinitionsBase
open import GUI.GUIExampleLibVers2
open import StateSizedIO.GUI.BaseStateDependent

-- the subset of business processes for which we can have a decision procedure
mutual
  decBusProc : (Q : GuiState → Bool)
               (p : BusinessProcessDec)
               → Maybe ( businessProcessDec2GuiState p -eventuallyPb-> Q)
  decBusProc Q (activitySilent p)  = decBusProc Q p
  decBusProc Q (startEventSilent p)  = decBusProc Q p
  decBusProc Q p with (bool2Dec (Q (businessProcessDec2GuiState p)))
  decBusProc Q p            | yes p' = just (hasReached p')
  decBusProc Q (activitySilent p) | no ¬p  = decBusProc Q p
  decBusProc Q (startEventSilent p) | no ¬p  = decBusProc Q p
  decBusProc Q (endEvent x) | no ¬p = nothing
  decBusProc Q (xor x) | no ¬p = decBusProcaux5 Q x (decBusProcaux4 Q x)
  decBusProc Q (activity x p) | no ¬p with decBusProc Q p
  decBusProc Q (activity x p) | no ¬p | just q  = just (next λ {(zero , tt) → q ;
                                (suc () , tt) } )
  decBusProc Q (activity x p) | no ¬p | nothing  = nothing
  decBusProc Q (startEvent x p) | no ¬p with decBusProc Q p
  decBusProc Q (startEvent x p) | no ¬p | just q  = just (next λ {(zero , tt) → q ;
                                (suc () , tt) } )
  decBusProc Q (startEvent x p) | no ¬p | nothing  = nothing



  decBusProcaux1 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  (k : Fin (length l))
                  → Maybe(businessProcessDec2GuiState (proj₂ (lookup l k))
                          -eventuallyPb-> Q)
  decBusProcaux1 Q [] ()
  decBusProcaux1 Q ((str , p) ∷ l) zero = decBusProc Q p
  decBusProcaux1 Q (x ∷ l) (suc k) = decBusProcaux1 Q l k


  decBusProcaux2 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  → Maybe((k : Fin (length l))
                           → businessProcessDec2GuiState (proj₂ (lookup l k))
                             -eventuallyPb-> Q)
  decBusProcaux2 Q l = maybeLiftFin
                       (λ k → businessProcessDec2GuiState (proj₂ (lookup l k))
                             -eventuallyPb-> Q)
                       (decBusProcaux1 Q l)

  decBusProcaux3 : (P : GuiState → Set)
                   (l : List (String × BusinessProcessDec))
                   (f : (k : Fin (length l))
                           → P (businessProcessDec2GuiState (proj₂ (lookup l k))))
                   (m : (Fin (frame2NrButtons
                             (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                   → P (guiNextaux (businessProcess2GUIxor (liftBusinessProcessDecl l))
                       m (businessProcess2GUIxor (liftBusinessProcessDecl l) .method m)
                     skippedIOcmds)
  decBusProcaux3 P [] f (() , _)
  decBusProcaux3 P ((str , p) ∷ l) f (zero , str') = f zero
  decBusProcaux3 P ((str , p) ∷ l) f (suc k , str') = decBusProcaux3 P l (f ∘ suc) (k , str')



  decBusProcaux4 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  → Maybe ((m : (Fin (frame2NrButtons
                             (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                   → (guiNextaux (businessProcess2GUIxor (liftBusinessProcessDecl l))
                       m (businessProcess2GUIxor (liftBusinessProcessDecl l) .method m)
                       skippedIOcmds)
                      -eventuallyPb-> Q)
  decBusProcaux4 Q l = maybeFunctor (decBusProcaux3
                                     (λ s → s -eventuallyPb-> Q)
                                     l)
                                     (decBusProcaux2 Q l)


  decBusProcaux5 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  (may : Maybe ((m : (Fin (frame2NrButtons
                             (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                   → (guiNextaux (businessProcess2GUIxor (liftBusinessProcessDecl l))
                       m (businessProcess2GUIxor (liftBusinessProcessDecl l) .method m)
                       skippedIOcmds)
                      -eventuallyPb-> Q))
                   →    Maybe ( (state (businessProcess2GUIxor (liftBusinessProcessDecl l))
       notStarted
       -eventuallyPb-> Q))
  decBusProcaux5 Q l (just x) = just (next x )
  decBusProcaux5 Q l nothing = nothing


decProcExtr : (Q : GuiState → Bool)
              (p : BusinessProcessDec)
              (q : IsJust (decBusProc Q p))
              → businessProcessDec2GuiState p -eventuallyPb-> Q
decProcExtr Q p q = just2Value q




mutual
  decBusProcAll : (Q : GuiState → Bool)
               (p : BusinessProcessDec)
               → Maybe (forAllReachableb (businessProcessDec2GuiState p) Q)
  decBusProcAll Q (activitySilent p)  = decBusProcAll Q p
  decBusProcAll Q (startEventSilent p)  = decBusProcAll Q p
  decBusProcAll Q p with (bool2Dec (Q (businessProcessDec2GuiState p)))
  ... | no  p' = nothing
  decBusProcAll Q (endEvent x) | yes p' = just (forAllReach p' λ {()})
  decBusProcAll Q (startEventSilent p) | yes p' = decBusProcAll Q p
  decBusProcAll Q (activitySilent p) | yes p' = decBusProcAll Q p
  decBusProcAll Q (activity x p) | yes p' with decBusProcAll Q p
  decBusProcAll Q (activity x p) | yes p' | just q =
           just (forAllReach p' λ {(zero , tt) → q ;
                                   (suc () , tt) } )
  decBusProcAll Q (activity x p) | yes p' | nothing = nothing
  decBusProcAll Q (startEvent x p) | yes p' with decBusProcAll Q p
  decBusProcAll Q (startEvent x p) | yes p' | just q =
           just (forAllReach p' λ {(zero , tt) → q ;
                                   (suc () , tt) } )
  decBusProcAll Q (startEvent x p) | yes p' | nothing = nothing
  decBusProcAll Q (xor x) | yes p' = decBusProcAllaux5 Q x p' (decBusProcAllaux4 Q x)


  decBusProcAllaux1 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  (k : Fin (length l))
                  → Maybe(forAllReachableb (businessProcessDec2GuiState (proj₂ (lookup l k))) Q)
  decBusProcAllaux1 Q [] ()
  decBusProcAllaux1 Q ((str , p) ∷ l) zero = decBusProcAll Q p
  decBusProcAllaux1 Q (x ∷ l) (suc k) = decBusProcAllaux1 Q l k


  decBusProcAllaux2 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  → Maybe((k : Fin (length l))
                           → forAllReachableb (businessProcessDec2GuiState (proj₂ (lookup l k))) Q )
  decBusProcAllaux2 Q l = maybeLiftFin
                       (λ k → forAllReachableb (businessProcessDec2GuiState (proj₂ (lookup l k))) Q)
                       (decBusProcAllaux1 Q l)


  decBusProcAllaux4 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  → Maybe ((m : (Fin (frame2NrButtons
                             (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                   → (forAllReachableb
                         (guiNextaux (businessProcess2GUIxor (liftBusinessProcessDecl l))
                          m (businessProcess2GUIxor (liftBusinessProcessDecl l) .method m)
                       skippedIOcmds) Q))
  decBusProcAllaux4 Q l = maybeFunctor (decBusProcaux3
                                     (λ s → forAllReachableb s Q)
                                     l)
                                     (decBusProcAllaux2 Q l)


  decBusProcAllaux5 : (Q : GuiState → Bool)
                  (l : List (String × BusinessProcessDec))
                  (nowQ : T     (Q
                        (state (businessProcess2GUIxor (liftBusinessProcessDecl l))
                                notStarted)))
                  (may : Maybe ((m : (Fin (frame2NrButtons
                             (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (businessProcess2GUIxor (liftBusinessProcessDecl l) .gui)))
                   → forAllReachableb (guiNextaux (businessProcess2GUIxor (liftBusinessProcessDecl l))
                       m (businessProcess2GUIxor (liftBusinessProcessDecl l) .method m)
                       skippedIOcmds) Q))
                   →    Maybe ( forAllReachableb
                                (businessProcessDec2GUIxorState l) Q)

  decBusProcAllaux5 Q l nowQ (just x) = just (forAllReach nowQ x )
  decBusProcAllaux5 Q l nowQ nothing = nothing

{-
  decBusProcAllaux1 Q [] ()
  decBusProcAllaux1 Q ((str , p) ∷ l) zero = decBusProcAll Q p
  decBusProcAllaux1 Q (x ∷ l) (suc k) = decBusProcAllaux1 Q l k
-}

decProcAllExtr : (Q : GuiState → Bool)
              (p : BusinessProcessDec)
              (q : IsJust (decBusProcAll Q p))
              → forAllReachableb (businessProcessDec2GuiState p) Q
decProcAllExtr Q p q = just2Value q
