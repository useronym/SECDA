module secd where

open import Data.Product
open import Data.Vec
open import Data.List
open import Data.List.All
open import Data.Nat using (ℕ; _≤_)
open import Data.Integer using (ℤ)


data Const : Set where
  nil : Const
  int : ℤ → Const
  idx : ℕ → Const

data Type : Set where
  nilT intT idxT funT envT : Type
  listT : Type → Type

typeof : Const → Type
typeof nil     = nilT
typeof (int x) = intT
typeof (idx x) = idxT

data Ins : Set where
  nil ld ldc ldf ap : Ins
  add : Ins
  cc : Const → Ins


Stack   = List Type

Env : ℕ → ℕ → Set
Env x y = Vec (Vec Type y) x

Control = List Ins

Dump : ℕ → ℕ → Set -- TODO: fix
Dump e1 e2 = List (Stack × Env e1 e2 × Control)

record SECD {e₁ e₂ : ℕ} : Set where
  constructor _#_#_#_
  field
    s : Stack
    e : Env e₁ e₂
    c : Control
    d : Dump e₁ e₂

newSECD : Control → SECD {0} {0}
newSECD c = [] # [] # c # []

infix 10 ⊢_
data ⊢_ {e₁ e₂} : SECD {e₁} {e₂} → Set where
  stop : ∀ {s e d}
       → ⊢ s # e # [] # d
  tnil : ∀ {s e c d}
       → ⊢ (nilT ∷ s) # e # c # d
       → ⊢ s # e # (nil ∷ c) # d
  tldc : ∀ {s e c d x}
       → ⊢ (typeof x ∷ s) # e # c # d
       → ⊢ s # e # (ldc ∷ cc x ∷ c) # d
  tld  : ∀ {s e c d} {x y : ℕ} {_ : x ≤ e₁} {_ : y ≤ e₂}
       → ⊢ (s) # e # c # d
       → ⊢ s # e # (ld ∷ cc (idx x) ∷ cc (idx y) ∷ c) # d
  tldf : ∀ {s e c d}
       → ⊢ (funT ∷ envT ∷ s) # e # c # d
       → ⊢ s # e # (ldf ∷ c) # d
--  tap  : ∀ {s e c d} {a : Type} {args : listT a}
--       → ⊢ [] # (args ∷ e) # c # ((s , e , c) ∷ d)
--       → ⊢ (funT ∷ envT ∷ args ∷ s) # e # (ap ∷ c) # d
  tadd : ∀ {s e c d}
       → ⊢ (intT ∷ s) # e # c # d
       → ⊢ (intT ∷ intT ∷ s) # e # (add ∷ c) # d

test : SECD
test = newSECD
  ( ldc ∷ cc (int (ℤ.pos 2))
  ∷ ldc ∷ cc (int (ℤ.pos 3))
  ∷ add ∷ [])

_ : ⊢ test
_ = tldc (tldc (tadd stop))
