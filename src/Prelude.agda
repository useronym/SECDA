module Prelude where

open import Function using (flip) public
open import Data.Unit using (⊤; tt) public
open import Data.Bool using (Bool) renaming (not to ¬_) public
open import Data.Integer using (ℤ; +_; _+_) public
open import Data.Maybe using (Maybe; nothing; just; maybe) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃-syntax) public
open import Data.List using (List; []; [_]; _∷_; map; length; lookup) public
open import Size public
open import Codata.Thunk using (force) public
open import Codata.Delay using (Delay; now; later; bind) public


data Path {A : Set} (R : A → A → Set) : A → A → Set where
  ∅    : ∀ {a} → Path R a a
  _>>_ : ∀ {a b c} → R a b → Path R b c → Path R a c
infixr 5 _>>_

_>|_ : ∀ {A R} {a b c : A} → R a b → R b c → Path R a c
a >| b = a >> b >> ∅

concatenate : ∀ {A R} {a b c : A} → Path R a b → Path R b c → Path R a c
concatenate ∅ r = r
concatenate (x >> l) r = x >> (concatenate l r)

snoc : ∀ {A R} {a b c : A} → Path R a b → R b c → Path R a c
snoc ∅ e = e >> ∅
snoc (x >> p) e = x >> (snoc p e)

reverse : ∀ {A R} {a b : A} → Path R a b → Path (flip R) b a
reverse ∅ = ∅
reverse (x >> p) = snoc (reverse p) x

record Stream (A : Set) : Set where
  coinductive
  field
    cohead : A
    cotail : Stream A
open Stream public

repeat : ∀ {A} → A → Stream A
cohead (repeat a) = a
cotail (repeat a) = repeat a
