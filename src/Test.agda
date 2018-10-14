module Test where

open import Prelude
open import Syntax


-- 2 + 3
_ : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
_ =
    ldc (int (+ 2))
 >> ldc (int (+ 3))
 >> add

-- λx.x + 1
inc : ∀ {e f} → ⊢ [] # (intT ∷ e) # (mkClosure intT intT [] ∷ f) ↝ [ intT ] # [] # f
inc =
    ld zero
 >> ldc (int (+ 1))
 >> add
 >> rtn

-- Apply 2 to the above.
_ : ⊢ [] # [] # [] ↝ [ intT ] # _ # []
_ =
    ldf inc
 >> ldc (int (+ 2))
 >> ap

-- Partial application test.
_ : ⊢ [] # [] # [] ↝ [ intT ] # [] # []
_ =
     ldf -- First, we construct the curried function.
       (ldf
         (ld zero >> ld (suc zero) >> add >> rtn) >> rtn)
  >> ldc (int (+ 1)) -- Load first argument.
  >> ap              -- Apply to curried function. Results in a closure.
  >> ldc (int (+ 2)) -- Load second argument.
  >> ap              -- Apply to closure.

withEnv : Env → Type → Type
withEnv e (pairT t u)       = pairT (withEnv e t) (withEnv e u)
withEnv e (funT a b)        = let aWithE = (withEnv e a) in closureT aWithE (withEnv (aWithE ∷ e) b) e
withEnv e (listT t)         = listT (withEnv e t)
withEnv e intT              = intT
withEnv e boolT             = boolT
withEnv e (closureT a b e') = closureT a b e'
withEnv e (envT x)          = envT x

_⇒_ : Type → Type → Type
_⇒_ = funT
infixr 15 _⇒_

-- λa.λb.a+b
-- withEnv test. Below is what withEnv desugars to.
-- plus : ∀ {e f} → ⊢ [] # e # f ↝ [ closureT intT (closureT intT intT (intT ∷ e)) e ] # e # f
plus : ∀ {s e f} → ⊢ s # e # f ↝ (withEnv e (intT ⇒ intT ⇒ intT) ∷ s) # e # f
plus = ldf (ldf (ld zero >> ld (suc zero) >> add >> rtn) >> rtn)

-- Shit getting real.
foldl : ∀ {e f} → ⊢ [] # e # f ↝ [ withEnv e ((intT ⇒ intT ⇒ intT) ⇒ intT ⇒ (listT intT) ⇒ intT) ] # e # f
-- Below is the Agda-polymorphic version which does not typecheck. Something to do with how `withEnv e b` does not normalize further.
-- foldl : ∀ {a b e f} → ⊢ [] # e # f ↝ [ withEnv e ((b ⇒ a ⇒ b) ⇒ b ⇒ (listT a) ⇒ b)] # e # f
-- Explicitly typing out the polymorhic version, however, works:
--         closureT                            -- We construct a function,
--             (closureT b (closureT a b (b ∷ e)) e) -- which takes the folding function,
--             (closureT b                     -- returning a function which takes acc,
--               (closureT (listT a)           -- returning a function which takes the list,
--                 b                           -- and returns the acc.
--                 (b ∷ (closureT b (closureT a b (b ∷ e)) e) ∷ e))
--               ((closureT b (closureT a b (b ∷ e)) e) ∷ e))
--             e
-- TODO: figure out what's going on here if has time.
foldl = ldf (ldf (ldf body >> rtn) >> rtn)
  where
    body =
         ld zero                   -- Load list.
      >> nil?                      -- Is it empty?
      >> if (ld (suc zero) >> rtn) -- If so, load & return acc.
          (ld (suc (suc zero))     -- If not, load folding function.
        >> ld (suc zero)           -- Load previous acc.
        >> ap                      -- Partially apply folding function.
        >> ld zero                 -- Load list.
        >> head                    -- Get the first element.
        >> ap                      -- Apply, yielding new acc.
        >> ld (suc (suc zero))     -- Load the folding function.
        >> tc (suc (suc zero))     -- Partially-tail apply the folding function to us.
        >> flip                    -- Flip resulting closure with our new acc.
        >> ap                      -- Apply acc, result in another closure.
        >> ld zero                 -- Load list.
        >> tail                    -- Drop the first element we just processed.
        >> ap                      -- Finally apply the last argument, that rest of the list.
        >> rtn)                    -- Once that returns, just return the result.
