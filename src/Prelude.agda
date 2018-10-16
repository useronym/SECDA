module Prelude where

open import Function using (flip) public
open import Data.Unit using (⊤) public
open import Data.Bool using (Bool) renaming (not to ¬_) public
open import Data.Integer using (ℤ; +_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Product using (_×_; _,_; Σ) public
open import Data.List using (List; []; [_]; _∷_; map; length; lookup) public


data Path {A : Set} (R : A → A → Set) : A → A → Set where
  ∅    : ∀ {a} → Path R a a
  _>>_ : ∀ {a b c} → R a b → Path R b c → Path R a c
infixr 5 _>>_

_>|_ : ∀ {A R} {a b c : A} → R a b → R b c → Path R a c
a >| b = a >> b >> ∅

prune : ∀ {A R} {a b : A} → Path R a b → Path R a b
prune ∅ = ∅
prune (x >> ∅) = x >> ∅
prune (x >> x₁ >> p) = {!!}

concatenate : ∀ {A R} {a b c : A} → Path R a b → Path R b c → Path R a c
concatenate ∅ r = r
concatenate (x >> l) r = x >> (concatenate l r)

reverse : ∀ {A R} {a b : A} → Path R a b → Path (flip R) b a
reverse ∅ = ∅
reverse (x >> p) = concatenate (reverse p) (x >> ∅)

record Stream (A : Set) : Set where
  coinductive
  field
    cohead : A
    cotail : Stream A
open Stream public

repeat : ∀ {A} → A → Stream A
cohead (repeat a) = a
cotail (repeat a) = repeat a
