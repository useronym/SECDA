module Syntax where

open import Prelude

-- Type of atomic constants. These can be loaded directly from a single instruction.
data Const : Set where
  true false : Const
  int : ℤ → Const

mutual
  -- Environment stores the types of bound variables.
  Env = List Type

  -- Types that our machine recognizes.
  data Type : Set where
    intT boolT : Type
    pairT : Type → Type → Type
    funT : Type → Type → Type
    closureT : Type → Type → Env → Type
    envT : Env → Type
    listT : Type → Type

_⇒_ : Type → Type → Type
_⇒_ = funT
infixr 15 _⇒_

-- Assignment of types to constants.
typeof : Const → Type
typeof true    = boolT
typeof false   = boolT
typeof (int x) = intT

-- Stack stores the types of values on the machine's stack.
Stack = List Type

-- Special kind of closure we use to allow recursive calls.
data ClosureT : Set where
  mkClosureT : Type → Type → Env → ClosureT

-- Boilerplate.
mkFrom : ClosureT → Type
mkFrom (mkClosureT from _ _) = from
mkTo : ClosureT → Type
mkTo (mkClosureT _ to _) = to
mkEnv : ClosureT → Env
mkEnv (mkClosureT _ _ env) = env

-- This is pretty much the call stack, allowing us to make recursive calls.
FunDump = List ClosureT

-- A state of our machine.
record State : Set where
  constructor _#_#_
  field
    s : Stack
    e : Env
    f : FunDump

-- The typing relation.
infix 5 ⊢_↝_
infix 5 ⊢_⊳_
mutual
  ⊢_↝_ : State → State → Set
  ⊢ s₁ ↝ s₂ = Path ⊢_⊳_ s₁ s₂

  data ⊢_⊳_ : State → State → Set where
    ldf  : ∀ {s e f from to}
         → (⊢ [] # (from ∷ e) # (mkClosureT from to e ∷ f) ↝ [ to ] # [] # f)
         → ⊢ s # e # f ⊳ (closureT from to e ∷ s) # e # f
    lett : ∀ {s e f x}
         → ⊢ (x ∷ s) # e # f ⊳ s # (x ∷ e) # f
    ap   : ∀ {s e e' f from to}
         → ⊢ (from ∷ closureT from to e' ∷ s) # e # f ⊳ (to ∷ s) # e # f
    tc   : ∀ {s e f}
         → (at : Fin (length f))
         → let cl = lookup f at in
           ⊢ (mkFrom cl ∷ s) # e # f ⊳ (mkTo cl ∷ s) # e # f
    rtn  : ∀ {s e e' a b f}
         → ⊢ (b ∷ s) # e # (mkClosureT a b e' ∷ f) ⊳ [ b ] # [] # f
    nil  : ∀ {s e f a}
         → ⊢ s # e # f ⊳ (listT a ∷ s) # e # f
    ldc  : ∀ {s e f}
         → (const : Const)
         → ⊢ s # e # f ⊳ (typeof const ∷ s) # e # f
    ld   : ∀ {s e f}
         → (at : Fin (length e))
         → ⊢ s # e # f ⊳ (lookup e at ∷ s) # e # f
    flp  : ∀ {s e f a b}
         → ⊢ (a ∷ b ∷ s) # e # f ⊳ (b ∷ a ∷ s) # e # f
    cons : ∀ {s e f a}
         → ⊢ (a ∷ listT a ∷ s) # e # f ⊳ (listT a ∷ s) # e # f
    head : ∀ {s e f a}
         → ⊢ (listT a ∷ s) # e # f ⊳ (a ∷ s) # e # f
    tail : ∀ {s e f a}
         → ⊢ (listT a ∷ s) # e # f ⊳ (listT a ∷ s) # e # f
    pair : ∀ {s e f a b}
         → ⊢ (a ∷ b ∷ s) # e # f ⊳ (pairT a b ∷ s) # e # f
    fst  : ∀ {s e f a b}
         → ⊢ (pairT a b ∷ s) # e # f ⊳ (a ∷ s) # e # f
    snd  : ∀ {s e f a b}
         → ⊢ (pairT a b ∷ s) # e # f ⊳ (b ∷ s) # e # f
    add  : ∀ {s e f}
         → ⊢ (intT ∷ intT ∷ s) # e # f ⊳ (intT ∷ s) # e # f
    nil? : ∀ {s e f a}
         → ⊢ (listT a ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
    not  : ∀ {s e f}
         → ⊢ (boolT ∷ s) # e # f ⊳ (boolT ∷ s) # e # f
    if   : ∀ {s s' e e' f f'}
         → ⊢ s # e # f ↝ s' # e' # f'
         → ⊢ s # e # f ↝ s' # e' # f'
         → ⊢ (boolT ∷ s) # e # f ⊳ s' # e' # f'

record Comp : Set where
  constructor makeComp
  field
    {s s'} : Stack
    {e e'} : Env
    {f f'} : FunDump
    c      : ⊢ s # e # f ↝ s' # e' # f'

-- This syntactic sugar makes writing out SECD types easier.
-- Doesn't play nice with Agda polymorphism?
withEnv : Env → Type → Type
withEnv e (pairT t u)       = pairT (withEnv e t) (withEnv e u)
withEnv e (funT a b)        = let aWithE = (withEnv e a) in closureT aWithE (withEnv (aWithE ∷ e) b) e
withEnv e (listT t)         = listT (withEnv e t)
withEnv e intT              = intT
withEnv e boolT             = boolT
withEnv e (closureT a b e') = closureT a b e'
withEnv e (envT x)          = envT x
