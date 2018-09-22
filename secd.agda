module secd where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; [_]; _∷_; length; lookup)
open import Data.Integer using (ℤ; +_)


data Const : Set where
  nil : Const
  true false : Const
  int : ℤ → Const

mutual
  Env = List Type

  data Type : Set where
    intT boolT : Type
    pairT : Type → Type → Type
    funT : Type → Type → Type
    envT : Env → Type
    listT : Type → Type

closureT : Type → Type → Env → Type
closureT a b env = pairT (funT a b) (envT env)

typeof : Const → Type
typeof nil     = listT intT --TODO: fix!!!
typeof true    = boolT
typeof false   = boolT
typeof (int x) = intT

Stack = List Type
--Dump  = List (Stack × Env)

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
  nil  : ∀ {s e a}
       → ⊢ s # e ↝ (listT a ∷ s) # e
  ldc  : ∀ {s e}
       → (const : Const)
       → ⊢ s # e ↝ (typeof const ∷ s) # e
  ld   : ∀ {s e}
       → (at : Fin (length e))
       → ⊢ s # e ↝ (lookup e at ∷ s) # e
  ldf  : ∀ {s e from to}
       → (f : ⊢ [] # (from ∷ e) ↝ [ to ] # [])
       → ⊢ s # e ↝ (closureT from to e ∷ s) # e
  ap   : ∀ {s e e' from to}
       → ⊢ (from ∷ closureT from to e' ∷ s) # e ↝ [ to ] # e
  rtn  : ∀ {s e x}
       → ⊢ (x ∷ s) # e ↝ [ x ] # []
  cons : ∀ {s e a}
       → ⊢ (a ∷ listT a ∷ s) # e ↝ (listT a ∷ s) # e
  head : ∀ {s e a}
       → ⊢ (listT a ∷ s) # e ↝ (a ∷ s) # e
  tail : ∀ {s e a}
       → ⊢ (listT a ∷ s) # e ↝ (listT a ∷ s) # e
  pair : ∀ {s e a b}
       → ⊢ (a ∷ b ∷ s) # e ↝ (pairT a b ∷ s) # e
  fst  : ∀ {s e a b}
       → ⊢ (pairT a b ∷ s) # e ↝ (a ∷ s) # e
  snd  : ∀ {s e a b}
       → ⊢ (pairT a b ∷ s) # e ↝ (b ∷ s) # e
  add  : ∀ {s e}
       → ⊢ (intT ∷ intT ∷ s) # e ↝ (intT ∷ s) # e
  nil? : ∀ {s e a}
       → ⊢ (listT a ∷ s) # e ↝ (boolT ∷ s) # e
  not  : ∀ {s e}
       → ⊢ (boolT ∷ s) # e ↝ (boolT ∷ s) # e
  if   : ∀ {s s' e e' x}
       → ⊢ s # e ↝ s' # e'
       → ⊢ s # e ↝ s' # e'
       → ⊢ (x ∷ s) # e ↝ s' # e'


-- 2 + 3
_ : ⊢ [] # [] ↝ [ intT ] # []
_ =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >> add

-- λx.x + 1
inc : ⊢ [] # [ intT ] ↝ [ intT ] # []
inc =
    ld zero
 >> ldc (int (+ 1))
 >> add
 >> rtn

-- Apply 2 to the above.
_ : ⊢ [] # [] ↝ [ intT ] # []
_ =
    ldf inc
 >> ldc (int (+ 2))
 >> ap

-- Partial application test.
_ : ⊢ [] # [] ↝ [ intT ] # []
_ =
     ldf -- First, we construct the curried function.
       ((ldf
         (ld zero >> ld (suc zero) >> add >> rtn)) >> rtn)
  >> ldc (int (+ 1)) -- Load first argument.
  >> ap              -- Apply function. Results in a closure.
  >> ldc (int (+ 2)) -- Load second argument.
  >> ap              -- Apply second argument to closure.

-- Shit getting real.
foldl : ∀ {a b e} → ⊢ [] # [] ↝
          [ closureT                          -- We construct a function,
              (closureT b (closureT a b e) e) -- which takes the folding function,
              (closureT b                     -- returning a function which takes acc,
                (closureT (listT a)           -- returning a function which takes the list,
                  b                           -- and returns the acc.
                  (b ∷ [ closureT b (closureT a b e) e ])) [ closureT b (closureT a b e) e ]) [] ] # []
foldl = ldf ((ldf (ldf body >> rtn) >> rtn) >> rtn)
  where
    body =
         ld zero
      >> nil?
      >> if (ld (suc zero) >> rtn)
          (ld (suc (suc zero))
        >> ld (suc zero)
        >> ap
        >> ld zero
        >> head
        >> ap
        >> {!!})
