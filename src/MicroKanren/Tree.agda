{-# OPTIONS --safe --guardedness #-}

-- Search trees, and the tree a goal denotes.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (∃; _,_; Σ-syntax; proj₁; _×_)
open import Data.Maybe using (nothing; just)

module MicroKanren.Tree (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren.State A A⟨_≟_⟩
open import MicroKanren.Goal A A⟨_≟_⟩

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

mutual
  data Tree (c : ℕ) : Set where
    fail   : Tree c
    leaf   : Answer c → Tree c
    choice : Tree c → Tree c → Tree c
    bind   : Tree c → (Answer c → Tree c) → Tree c
    within : c ⊑ c′ → Tree c′ → Tree c
    delay  : ∞Tree c → Tree c

  record ∞Tree (c : ℕ) : Set where
    coinductive
    field force : Tree c

open ∞Tree public

⟦_⟧   : Goal c → c ⊑ c′ → State c′ → Tree c′
after : Goal c → c ⊑ c′ → Answer c′ → Tree c′

⟦ t ≐ u ⟧ p (mkState {k} σ) with amgu (wk p t) (wk p u) (k , σ)
... | nothing        = fail
... | just (k′ , σ′) = leaf (answer id (mkState σ′))
⟦ fresh f ⟧ p (mkState σ) =
  within (skip id) (⟦ f (var 0F) ⟧ (keep p) (mkState (liftAList σ)))
⟦ g₁ ∨ g₂ ⟧ p s = choice (⟦ g₁ ⟧ p s) (⟦ g₂ ⟧ p s)
⟦ g₁ ∧ g₂ ⟧ p s = bind (⟦ g₁ ⟧ p s) (after g₂ p)
⟦ delay g ⟧ p s = delay λ where .force → ⟦ g .force ⟧ p s

after g p (answer q s) = within q (⟦ g ⟧ (p ∙ q) s)
