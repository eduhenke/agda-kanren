{-# OPTIONS --safe --guardedness #-}

-- The goal language.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.Definitions using (DecidableEquality)

module MicroKanren.Goal (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

infix  8 _≐_
infixr 7 _∧_
infixr 6 _∨_

mutual
  data Goal (c : ℕ) : Set where
    _≐_   : Term c → Term c → Goal c
    fresh : (Term (suc c) → Goal (suc c)) → Goal c
    _∨_   : Goal c → Goal c → Goal c
    _∧_   : Goal c → Goal c → Goal c
    delay : ∞Goal c → Goal c

  record ∞Goal (c : ℕ) : Set where
    coinductive
    field force : Goal c

open ∞Goal public
