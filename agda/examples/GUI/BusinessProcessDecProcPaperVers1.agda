module GUI.BusinessProcessDecProcPaperVers1 where

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
open import Relation.Nullary
open import Data.Fin renaming (_+_ to _+fin_)
open import SizedIO.Base renaming (IO to IO∞; IO' to IO)
open import GUI.BusinessProcessVers3Paper
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
               (p : ProcessDec)
               → Maybe ( processDec2GuiState p -eventuallyPb-> Q)
  decBusProc Q (activitySilent p)  = decBusProc Q p
  decBusProc Q (startEventSilent p)  = decBusProc Q p
  decBusProc Q p with (bool2Dec (Q (processDec2GuiState p)))
  decBusProc Q p            | yes p' = just (hasReached p')
  decBusProc Q (activitySilent p) | no ¬p  = decBusProc Q p
  decBusProc Q (startEventSilent p) | no ¬p  = decBusProc Q p
  decBusProc Q (endEvent x) | no ¬p = nothing
  decBusProc Q (multiXor x) | no ¬p = decBusProcaux5 Q x (decBusProcaux4 Q x)
  decBusProc Q (activity x p) | no ¬p with decBusProc Q p
  decBusProc Q (activity x p) | no ¬p | just q  = just (next λ {(zero , tt) → q ;
                                (suc () , tt) } )
  decBusProc Q (activity x p) | no ¬p | nothing  = nothing
  decBusProc Q (startEvent x p) | no ¬p with decBusProc Q p
  decBusProc Q (startEvent x p) | no ¬p | just q  = just (next λ {(zero , tt) → q ;
                                (suc () , tt) } )
  decBusProc Q (startEvent x p) | no ¬p | nothing  = nothing



  decBusProcaux1 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  (k : Fin (length l))
                  → Maybe(processDec2GuiState (proj₂ (lookup l k))
                          -eventuallyPb-> Q)
  decBusProcaux1 Q [] ()
  decBusProcaux1 Q ((str , p) ∷ l) zero = decBusProc Q p
  decBusProcaux1 Q (x ∷ l) (suc k) = decBusProcaux1 Q l k


  decBusProcaux2 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  → Maybe((k : Fin (length l))
                           → processDec2GuiState (proj₂ (lookup l k))
                             -eventuallyPb-> Q)
  decBusProcaux2 Q l = maybeLiftFin
                       (λ k → processDec2GuiState (proj₂ (lookup l k))
                             -eventuallyPb-> Q)
                       (decBusProcaux1 Q l)

  decBusProcaux3 : (P : GuiState → Set)
                   (l : List (String × ProcessDec))
                   (f : (k : Fin (length l))
                           → P (processDec2GuiState (proj₂ (lookup l k))))
                   (m : (Fin (frame2NrButtons
                             (process2GUIxor (liftProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (process2GUIxor (liftProcessDecl l) .gui)))
                   → P (guiNextaux (process2GUIxor (liftProcessDecl l))
                       m (process2GUIxor (liftProcessDecl l) .method m)
                     skippedIOcmds)
  decBusProcaux3 P [] f (() , _)
  decBusProcaux3 P ((str , p) ∷ l) f (zero , str') = f zero
  decBusProcaux3 P ((str , p) ∷ l) f (suc k , str') = decBusProcaux3 P l (f ∘ suc) (k , str')



  decBusProcaux4 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  → Maybe ((m : (Fin (frame2NrButtons
                             (process2GUIxor (liftProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (process2GUIxor (liftProcessDecl l) .gui)))
                   → (guiNextaux (process2GUIxor (liftProcessDecl l))
                       m (process2GUIxor (liftProcessDecl l) .method m)
                       skippedIOcmds)
                      -eventuallyPb-> Q)
  decBusProcaux4 Q l = maybeFunctor (decBusProcaux3
                                     (λ s → s -eventuallyPb-> Q)
                                     l)
                                     (decBusProcaux2 Q l)


  decBusProcaux5 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  (may : Maybe ((m : (Fin (frame2NrButtons
                             (process2GUIxor (liftProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (process2GUIxor (liftProcessDecl l) .gui)))
                   → (guiNextaux (process2GUIxor (liftProcessDecl l))
                       m (process2GUIxor (liftProcessDecl l) .method m)
                       skippedIOcmds)
                      -eventuallyPb-> Q))
                   →    Maybe ( (state (process2GUIxor (liftProcessDecl l))
       notStarted
       -eventuallyPb-> Q))
  decBusProcaux5 Q l (just x) = just (next x )
  decBusProcaux5 Q l nothing = nothing


decProcExtr : (Q : GuiState → Bool)
              (p : ProcessDec)
              (q : IsJust (decBusProc Q p))
              → processDec2GuiState p -eventuallyPb-> Q
decProcExtr Q p q = just2Value q




mutual
  decBusProcAll : (Q : GuiState → Bool)
               (p : ProcessDec)
               → Maybe (forAllReachableb (processDec2GuiState p) Q)
  decBusProcAll Q (activitySilent p)  = decBusProcAll Q p
  decBusProcAll Q (startEventSilent p)  = decBusProcAll Q p
  decBusProcAll Q p with (bool2Dec (Q (processDec2GuiState p)))
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
  decBusProcAll Q (multiXor x) | yes p' = decBusProcAllaux5 Q x p' (decBusProcAllaux4 Q x)


  decBusProcAllaux1 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  (k : Fin (length l))
                  → Maybe(forAllReachableb (processDec2GuiState (proj₂ (lookup l k))) Q)
  decBusProcAllaux1 Q [] ()
  decBusProcAllaux1 Q ((str , p) ∷ l) zero = decBusProcAll Q p
  decBusProcAllaux1 Q (x ∷ l) (suc k) = decBusProcAllaux1 Q l k


  decBusProcAllaux2 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  → Maybe((k : Fin (length l))
                           → forAllReachableb (processDec2GuiState (proj₂ (lookup l k))) Q )
  decBusProcAllaux2 Q l = maybeLiftFin
                       (λ k → forAllReachableb (processDec2GuiState (proj₂ (lookup l k))) Q)
                       (decBusProcAllaux1 Q l)


  decBusProcAllaux4 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  → Maybe ((m : (Fin (frame2NrButtons
                             (process2GUIxor (liftProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (process2GUIxor (liftProcessDecl l) .gui)))
                   → (forAllReachableb
                         (guiNextaux (process2GUIxor (liftProcessDecl l))
                          m (process2GUIxor (liftProcessDecl l) .method m)
                       skippedIOcmds) Q))
  decBusProcAllaux4 Q l = maybeFunctor (decBusProcaux3
                                     (λ s → forAllReachableb s Q)
                                     l)
                                     (decBusProcAllaux2 Q l)


  decBusProcAllaux5 : (Q : GuiState → Bool)
                  (l : List (String × ProcessDec))
                  (nowQ : T     (Q
                        (state (process2GUIxor (liftProcessDecl l))
                                notStarted)))
                  (may : Maybe ((m : (Fin (frame2NrButtons
                             (process2GUIxor (liftProcessDecl l) .gui)))
                        ×
                        Tuple String (frame2NrTextboxes
                           (process2GUIxor (liftProcessDecl l) .gui)))
                   → forAllReachableb (guiNextaux (process2GUIxor (liftProcessDecl l))
                       m (process2GUIxor (liftProcessDecl l) .method m)
                       skippedIOcmds) Q))
                   →    Maybe ( forAllReachableb
                                (processDec2GUIxorState l) Q)

  decBusProcAllaux5 Q l nowQ (just x) = just (forAllReach nowQ x )
  decBusProcAllaux5 Q l nowQ nothing = nothing

{-
  decBusProcAllaux1 Q [] ()
  decBusProcAllaux1 Q ((str , p) ∷ l) zero = decBusProcAll Q p
  decBusProcAllaux1 Q (x ∷ l) (suc k) = decBusProcAllaux1 Q l k
-}

decProcAllExtr : (Q : GuiState → Bool)
              (p : ProcessDec)
              (q : IsJust (decBusProcAll Q p))
              → forAllReachableb (processDec2GuiState p) Q
decProcAllExtr Q p q = just2Value q
