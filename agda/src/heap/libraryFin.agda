module heap.libraryFin where
open import Data.Nat
open import Data.Maybe
open import Data.Fin hiding (lift)
open import Data.Bool.Base
open import heap.libraryNat using (_≦ℕb_)
open import Relation.Binary.PropositionalEquality hiding (sym)
open import Function

createFinn : {n : ℕ} → (notzero : T (1 ≦ℕb n)) → Fin n
createFinn {zero} ()
createFinn {suc n} notzero = zero


{-
_==fin_ : {n : ℕ}  → Fin n → Fin n → Bool
zero ==fin zero = true
suc k ==fin suc l = k ==fin l
_ ==fin _ = false
-}


liftFunFinn : {n : ℕ}
              (A : Fin (suc n) → Set)
              (a : A zero)
              (f : (k : Fin n) → A (suc k))
              (k : Fin (suc n))
              → A k
liftFunFinn A a f zero = a
liftFunFinn A a f (suc k) = f k

maybeLiftFin : {n : ℕ}
               (A : Fin n → Set)
               (f : (k : Fin n) → Maybe (A k))
               → Maybe ( (k : Fin n) → A k)
maybeLiftFin {zero} A f = just λ {()}
maybeLiftFin {suc n} A f with (f zero) | maybeLiftFin (A ∘ suc) (f ∘ suc)
maybeLiftFin {suc n} A f | just a | just g = just (liftFunFinn A a g)
maybeLiftFin {suc n} A f | just _ | nothing = nothing
maybeLiftFin {suc n} A f | nothing | _ = nothing
