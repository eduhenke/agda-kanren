{-# OPTIONS --safe --guardedness #-}

-- The declarative semantics of goals.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality as Eq
  using (refl; sym; _≡_; cong; cong₂; trans)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (∃; _,_; Σ-syntax; proj₁; _×_)

module MicroKanren.Semantics (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Properties A A⟨_≟_⟩ hiding (_∧_; _∈_)
open import MicroKanren.State A A⟨_≟_⟩
open import MicroKanren.Goal A A⟨_≟_⟩

private variable
  l m n c c′ c″ k : ℕ
  R S : Set
  θ : Subst c m
  t u : Term c

infix 3 _⊨_

private variable
  g g₁ g₂ : Goal c

_▹_ : Term m → Subst c m → Subst (suc c) m
(t ▹ θ) zero    = t
(t ▹ θ) (suc x) = θ x

data _⊨_ {m} : ∀ {c} → Subst c m → Goal c → Set where
  ⊨≐     : Unifies t u θ → θ ⊨ t ≐ u
  ⊨fresh : ∀ {f} (v : Term m) → (v ▹ θ) ⊨ f (var 0F)
         → θ ⊨ fresh f
  ⊨∨₁    : θ ⊨ g₁ → θ ⊨ g₁ ∨ g₂
  ⊨∨₂    : θ ⊨ g₂ → θ ⊨ g₁ ∨ g₂
  ⊨∧     : θ ⊨ g₁ → θ ⊨ g₂ → θ ⊨ g₁ ∧ g₂
  ⊨delay : ∀ {g : ∞Goal c} → θ ⊨ g .force → θ ⊨ delay g

⊨-cong : ∀ {g : Goal c} {θ θ′ : Subst c m}
  → (∀ x → θ x ≡ θ′ x) → θ ⊨ g → θ′ ⊨ g
⊨-cong pw (⊨≐ {t = t} {u} h) = ⊨≐ (Unifies-cong t u _ _ pw h)
⊨-cong {θ = θ} {θ′} pw (⊨fresh t h) = ⊨fresh t (⊨-cong pw′ h)
  where
    pw′ : ∀ z → (t ▹ θ) z ≡ (t ▹ θ′) z
    pw′ zero    = refl
    pw′ (suc x) = pw x
⊨-cong pw (⊨∨₁ h)    = ⊨∨₁ (⊨-cong pw h)
⊨-cong pw (⊨∨₂ h)    = ⊨∨₂ (⊨-cong pw h)
⊨-cong pw (⊨∧ h₁ h₂) = ⊨∧ (⊨-cong pw h₁) (⊨-cong pw h₂)
⊨-cong pw (⊨delay h) = ⊨delay (⊨-cong pw h)

-- Satisfaction is stable under instantiation.
⊨-inst : ∀ {g : Goal c} {m′} {θ : Subst c m} {θ′ : Subst c m′}
  (h : Subst m m′) → (∀ x → θ′ x ≡ (h ◇ θ) x) → θ ⊨ g → θ′ ⊨ g
⊨-inst {θ = θ} {θ′} h e (⊨≐ {t = t} {u} s) =
  ⊨≐ (Unifies-DClosed t u θ′ θ (h , e) s)
⊨-inst {θ = θ} {θ′} h e (⊨fresh t s) = ⊨fresh (apply h t) (⊨-inst h e′ s)
  where
    e′ : ∀ z → (apply h t ▹ θ′) z ≡ (h ◇ (t ▹ θ)) z
    e′ zero    = refl
    e′ (suc x) = e x
⊨-inst h e (⊨∨₁ s)    = ⊨∨₁ (⊨-inst h e s)
⊨-inst h e (⊨∨₂ s)    = ⊨∨₂ (⊨-inst h e s)
⊨-inst h e (⊨∧ s₁ s₂) = ⊨∧ (⊨-inst h e s₁) (⊨-inst h e s₂)
⊨-inst h e (⊨delay s) = ⊨delay (⊨-inst h e s)

apply-rename : ∀ (θ : Subst n m) (f : Fin l → Fin n) (t : Term l)
  → apply θ (rename f t) ≡ apply (λ x → θ (f x)) t
apply-rename θ f (var x)      = refl
apply-rename θ f (val a)      = refl
apply-rename θ f ⟨ t₁ , t₂ ⟩ = cong₂ ⟨_,_⟩ (apply-rename θ f t₁) (apply-rename θ f t₂)

apply-wk : ∀ (θ : Subst n m) (p : l ⊑ n) (t : Term l)
  → apply θ (wk p t) ≡ apply (λ x → θ (ren p x)) t
apply-wk θ id       t = refl
apply-wk θ (keep p) t = apply-rename θ (ren (keep p)) t
apply-wk θ (skip p) t = apply-rename θ (ren (skip p)) t
