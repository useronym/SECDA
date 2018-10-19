module Semantics where

open import Prelude
open import Syntax -- hiding (State)


mutual
  ⟦_⟧ᵉ : Env → Set
  ⟦ [] ⟧ᵉ     = ⊤
  ⟦ x ∷ xs ⟧ᵉ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ᵉ

  record Closure {a b : Type} {e : Env} : Set where
    inductive
    constructor ⟦_⟧ᶠ×⟦_⟧ᵉ
    field
      {f} : FunDump
      ⟦f⟧ᶠ : ⊢ [] # (a ∷ e) # (mkClosureT a b e ∷ f) ↝ [ b ] # [] # f
      ⟦e⟧ᵉ : ⟦ e ⟧ᵉ

  ⟦_⟧ᵗ : Type → Set
  ⟦ intT ⟧ᵗ           = ℤ
  ⟦ boolT ⟧ᵗ          = Bool
  ⟦ pairT t₁ t₂ ⟧ᵗ    = ⟦ t₁ ⟧ᵗ × ⟦ t₂ ⟧ᵗ
  ⟦ funT a b ⟧ᵗ       = ⊤
  ⟦ closureT a b e ⟧ᵗ = Closure {a} {b} {e = e}
  ⟦ envT e ⟧ᵗ         = ⟦ e ⟧ᵉ
  ⟦ listT t ⟧ᵗ        = List ⟦ t ⟧ᵗ

⟦_⟧ˢ : Stack → Set
⟦ [] ⟧ˢ     = ⊤
⟦ x ∷ xs ⟧ˢ = ⟦ x ⟧ᵗ × ⟦ xs ⟧ˢ


run : ∀ {s s' e e' f f'} → ⟦ s ⟧ˢ → ⟦ e ⟧ᵉ → ⊢ s # e # f ↝ s' # e' # f'
                         → Delay ⟦ s' ⟧ˢ ∞
run s e ∅        = now s
run s e (ldf f >> r) = run (⟦ f ⟧ᶠ×⟦ e ⟧ᵉ , s) e r
run s e (lett >> r) = {!!}
run (from , ⟦ f ⟧ᶠ×⟦ fE ⟧ᵉ , s) e (ap >> r) = later λ where .force → later λ where .force → bind (run tt {!from , fE!} f) λ s' → run (proj₁ s' , s) e r
run s e (tc at >> r) = {!!}
run s e (rtn >> r) = {!now !}
run s e (nil >> r) = {!!}
run s e (ldc const >> r) = {!!}
run s e (ld at >> r) = {!!}
run s e (flp >> r) = {!!}
run s e (cons >> r) = {!!}
run s e (head >> r) = {!!}
run s e (tail >> r) = {!!}
run s e (pair >> r) = {!!}
run s e (fst >> r) = {!!}
run s e (snd >> r) = {!!}
run (a , b , s) e (add >> r) = {!!}
run s e (nil? >> r) = {!!}
run s e (not >> r) = {!!}
run s e (if x x₁ >> r) = {!!}

--run : ∀ {s s' e e' f f'} → ⟦ s ⟧ˢ → ⟦ e ⟧ᵉ → ⊢ s # e # f ↝ s' # e' # f'
--                         → Stream (Σ Stack ⟦_⟧ˢ)
--cohead (run {s} ss ee r)    = s , ss
--cotail (run {s} ss ee ∅)    = repeat (s , ss)
--cotail (run ss ee (i >> r)) = let (ss' , ee') = step ss ee i in {!!}


--record State : Set where
--  constructor _/_/_/_
--  field
--    s : Stack
--    e : Env
--    c : Comp
--    d : Dump


--makeRun : State → Stream State
--cohead (makeRun s) = s
--cotail (makeRun s) = makeRun (step s)

