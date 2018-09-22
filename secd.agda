module secd where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Fin using (Fin; fromℕ; zero)
open import Data.Vec using (Vec; [])
open import Data.List using (List; []; [_]; _∷_; length; lookup)
open import Data.Nat using (ℕ; _≤_)
open import Data.Integer using (ℤ; +_)


data Const : Set where
  nil : Const
  int : ℤ → Const

mutual
  Env = List Type

  data Type : Set where
    nilT intT : Type
    funT : Type → Type → Type
    env : Env → Type
    list : List Type → Type

typeof : Const → Type
typeof nil     = nilT
typeof (int x) = intT


Stack = List Type
Dump  = List (Stack × Env)

record State : Set where
  constructor _#_
  field
    s : Stack
    e : Env

infix 5 ⊢_↝_
infixr 5 _>>_
data ⊢_↝_ : State → State → Set where
  _>>_ : ∀ {s e s' e' s'' e''}
       → ⊢ s # e ↝ s' # e'
       → ⊢ s' # e' ↝ s'' # e''
       → ⊢ s # e ↝ s'' # e''
  nil  : ∀ {s e}
       → ⊢ s # e ↝ (nilT ∷ s) # e
  ldc  : ∀ {s e}
       → (const : Const)
       → ⊢ s # e ↝ (typeof const ∷ s) # e
  ld   : ∀ {s e}
       → (at : Fin (length e))
       → ⊢ s # e ↝ (lookup e at ∷ s) # e
  ldf  : ∀ {s e s' e' from to}
       → (f : ⊢ [] # (from ∷ e) ↝ (to ∷ s') # e')
       → ⊢ s # e ↝ (funT from to ∷ env e ∷ s) # e
  ap   : ∀ {s e e' from to}
       → ⊢ (from ∷ funT from to ∷ env e' ∷ s) # e ↝ [ to ] # e
  rtn  : ∀ {s e s' e' x}
       → ⊢ (x ∷ s') # e' ↝ (x ∷ s) # e
  add  : ∀ {s e}
       → ⊢ (intT ∷ intT ∷ s) # e ↝ (intT ∷ s) # e

_⇒_ : Type → Type → Set
from ⇒ to = ∀ {s e e'} → ⊢ [] # (from ∷ e') ↝ (to ∷ s) # e

fromNada : Type → Set
fromNada t = ⊢ [] # [] ↝ [ t ] # []

-- 2 + 3
_ : fromNada intT
_ =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >> add

-- λx.x + 1
inc : intT ⇒ intT
inc =
    ld zero
 >> ldc (int (+ 1))
 >> add
 >> rtn

-- Apply 2 to the above.
_ : fromNada intT
_ =
    ldf inc
 >> ldc (int (+ 2))
 >> ap
