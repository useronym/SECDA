module secd where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Fin using (Fin; fromℕ; zero)
open import Data.Vec using (Vec; [])
open import Data.List using (List; []; [_]; _∷_; length) renaming (lookup to lookupˡ)
open import Data.Nat using (ℕ; _≤_)
open import Data.Integer using (ℤ; +_)


data Const : Set where
  nil : Const
  int : ℤ → Const
  idx : ℕ → Const

mutual
  Env = List (List Type)

  data Type : Set where
    nilT intT idxT funT : Type
    env : Env → Type
    list : List Type → Type

envIdx : Env → Set
envIdx e = Σ (Fin (length e)) (λ x → Fin (length (lookupˡ e x)))

lookup : (e : Env) → envIdx e → Type
lookup e (x , y) = lookupˡ (lookupˡ e x) y

typeof : Const → Type
typeof nil     = nilT
typeof (int x) = intT
typeof (idx x) = idxT


Stack = List Type
Dump  = List (Stack × Env)

record State : Set where
  constructor _#_#_
  field
    s : Stack
    e : Env
    d : Dump

infix 5 ⊢_↝_
infixr 5 _>>_
data ⊢_↝_ : State → State → Set where
  _>>_ : ∀ {s e d s' e' d' s'' e'' d''}
       → ⊢ s # e # d ↝ s' # e' # d'
       → ⊢ s' # e' # d' ↝ s'' # e'' # d''
       → ⊢ s # e # d ↝ s'' # e'' # d''
  nil  : ∀ {s e d}
       → ⊢ s # e # d ↝ (nilT ∷ s) # e # d
  ldc  : ∀ {s e d}
       → (const : Const)
       → ⊢ s # e # d ↝ (typeof const ∷ s) # e # d
  ld   : ∀ {s e d}
       → (at : envIdx e)
       → ⊢ s # e # d ↝ (lookup e at ∷ s) # e # d
  ldf  : ∀ {s e d s' e' d' x}
       → (f : ⊢ [] # e # d ↝ (x ∷ s') # e' # d')
       → ⊢ s # e # d ↝ (funT ∷ env e ∷ s) # e # d
  ap   : ∀ {s e e' d l}
       → ⊢ (funT ∷ env e' ∷ list l ∷ s) # e # d ↝ [] # (l ∷ e') # ((s , e) ∷ d)
  rtn  : ∀ {s e d s' e' x}
       → ⊢ (x ∷ s') # e' # ((s , e) ∷ d) ↝ (x ∷ s) # e # d
  add  : ∀ {s e d}
       → ⊢ (intT ∷ intT ∷ s) # e # d ↝ (intT ∷ s) # e # d

_⇒_ : List Type → Type → Set
from ⇒ to = ∀ {s e e' d} → ⊢ [] # (from ∷ e') # (((s , e) ∷ d)) ↝ (to ∷ s) # e # d

fromNada : Type → Set
fromNada t = ⊢ [] # [] # [] ↝ [ t ] # [] # []


-- 2 + 3
_ : fromNada intT
_ =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >> add

-- λx.x + 1
inc : [ intT ] ⇒ intT
inc =
    ld (zero , zero)
 >> ldc (int (+ 1))
 >> add
 >> rtn

-- Apply 2 to the above.
_ : fromNada intT
_ = 
    ldf {!!}
 >> {!!}
