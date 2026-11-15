{-# OPTIONS --safe --guardedness #-}

-- Streams of answers, with mature and immature steps.

module MicroKanren.Stream where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

private variable
  R S : Set

mutual
  record Stream (R : Set) : Set where
    coinductive
    field step : Step R

  data Step (R : Set) : Set where
    fail  : Step R
    yield : R → Stream R → Step R
    later : Stream R → Step R

open Stream public

infix 4 _∈_ _∈ˢ_

data _∈ˢ_ (r : R) : Step R → Set where
  here  : ∀ {xs}    → r ∈ˢ yield r xs
  there : ∀ {r′ xs} → r ∈ˢ xs .step → r ∈ˢ yield r′ xs
  later : ∀ {xs}    → r ∈ˢ xs .step → r ∈ˢ later xs

_∈_ : R → Stream R → Set
r ∈ xs = r ∈ˢ xs .step

take : ℕ → ℕ → Stream R → List R
take zero    _       xs = []
take (suc n) zero    xs = []
take (suc n) (suc f) xs with xs .step
... | fail        = []
... | later xs′   = take (suc n) f xs′
... | yield a xs′ = a ∷ take n f xs′
