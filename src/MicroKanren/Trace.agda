{-# OPTIONS --safe --guardedness #-}

-- Runs of a search written out step by step and checked by evaluation.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List; []; _∷_; _++_; map)

module MicroKanren.Trace (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren.Search A A⟨_≟_⟩

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

Paused Finished : Prefix c → List (Solution c) → Set
Paused   (paused as _) sols = sols ≡ map solution as
Paused   (finished _)  _    = ⊥
Finished (finished as) sols = sols ≡ map solution as
Finished (paused _ _)  _    = ⊥

rest : Prefix c → Prefix c
rest (paused _ t)  = next t
rest (finished as) = finished as

instance
  by-evaluation : ∀ {X : Set} {x : X} → x ≡ x
  by-evaluation = refl

  trivially : ⊤
  trivially = tt

infixr 2 _⟶_
infix  3 _∎ _⋯

data Run : Prefix c → Set where
  _⟶_ : ∀ {p : Prefix c} (sols : List (Solution c)) {{_ : Paused p sols}}
        → Run (rest p) → Run p
  _∎  : ∀ {p : Prefix c} (sols : List (Solution c)) {{_ : Finished p sols}}
        → Run p
  _⋯  : ∀ {p : Prefix c} (sols : List (Solution c)) {{_ : Paused p sols}}
        → Run p
