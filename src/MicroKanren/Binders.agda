{-# OPTIONS --safe --guardedness #-}

-- Conveniences for goals that bind several variables: weakening terms
-- into the scope of new binders, and binding two or three variables at
-- once, each handed over already weakened into the innermost scope.

open import Relation.Binary.Definitions using (DecidableEquality)

module MicroKanren.Binders (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_)
open import MicroKanren A A⟨_≟_⟩

private variable
  c m : ℕ

-- Weakening a term past two or three new binders.
↑² : Term c → Term (2 + c)
↑² = wk (skip (skip id))

↑³ : Term c → Term (3 + c)
↑³ = wk (skip (skip (skip id)))

-- The same, for a list of terms.
↑ˢ : List (Term c) → List (Term (suc c))
↑ˢ = map ↑

↑³ˢ : List (Term c) → List (Term (3 + c))
↑³ˢ = map ↑³

-- Binding several variables at once.
fresh₂ : (Term (2 + c) → Term (2 + c) → Goal (2 + c)) → Goal c
fresh₂ f = fresh λ a → fresh λ b → f (↑ a) b
{-# INLINE fresh₂ #-}

fresh₃ : (Term (3 + c) → Term (3 + c) → Term (3 + c) → Goal (3 + c)) → Goal c
fresh₃ f = fresh λ a → fresh λ b → fresh λ d → f (↑² a) (↑ b) d
{-# INLINE fresh₃ #-}

-- A weakened term reads the old part of an extended substitution.
apply-↑ : ∀ (θ : Subst (suc c) m) t → apply θ (↑ t) ≡ apply (λ x → θ (suc x)) t
apply-↑ θ t = apply-wk θ (skip id) t

apply-↑³ : ∀ (θ : Subst (3 + c) m) t
  → apply θ (↑³ t) ≡ apply (λ x → θ (suc (suc (suc x)))) t
apply-↑³ θ t = apply-wk θ (skip (skip (skip id))) t

apply-↑³ˢ : ∀ (θ : Subst (3 + c) m) (Γ : List (Term c))
  → map (apply θ) (↑³ˢ Γ) ≡ map (apply (λ x → θ (suc (suc (suc x))))) Γ
apply-↑³ˢ θ []      = refl
apply-↑³ˢ θ (a ∷ Γ) = cong₂ _∷_ (apply-↑³ θ a) (apply-↑³ˢ θ Γ)
