{-# OPTIONS --safe #-}

open import Data.Nat hiding (_≟_; _/_; _≤_; _+_)
open import Data.Fin as Fin renaming (_≟_ to Fin⟨_≟_⟩) hiding (lift; _≤_; _+_)
open import Data.Fin.Properties using (punchOut-punchIn; punchIn-punchOut; punchInᵢ≢i)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation
open import Data.Empty
open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Definitions using (DecidableEquality)
open import Function.Base using (_∘_)
open import Data.Product
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

module Unification.Term (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

data Term (n : ℕ) : Set where
  var   : Fin n → Term n
  val   : A → Term n
  ⟨_,_⟩ : (t₁ t₂ : Term n) → Term n

private variable
  n n′ n″ n‴ m l k : ℕ

weaken : Term n → Term (suc n)
weaken (var x) = var (suc x)
weaken (val a) = val a
weaken ⟨ t₁ , t₂ ⟩ = ⟨ weaken t₁ , weaken t₂ ⟩

Subst : ℕ → ℕ → Set
Subst m n = Fin m → Term n

apply : Subst m n → Term m → Term n
apply ρ (var x) = ρ x
apply ρ (val a) = val a
apply ρ ⟨ t₁ , t₂ ⟩ = ⟨ apply ρ t₁ , apply ρ t₂ ⟩

infix 8 _◇_

_◇_ : Subst m n → Subst l m → Subst l n
f ◇ g = apply f ∘ g

apply-id : ∀ (t : Term m) → t ≡ apply var t
apply-id (var x) = refl
apply-id (val x) = refl
apply-id ⟨ t₁ , t₂ ⟩ = cong₂ ⟨_,_⟩ (apply-id t₁) (apply-id t₂)

apply-assoc : ∀
  (t : Term m)
  (g : Subst m n)
  (f : Subst n l)
  → apply f (apply g t)
    ≡ apply (f ◇ g) t
apply-assoc (var x) g f = refl
apply-assoc (val a) g f = refl
apply-assoc ⟨ t₁ , t₂ ⟩ g f = cong₂ ⟨_,_⟩ (apply-assoc t₁ g f) (apply-assoc t₂ g f)

apply-cong : ∀
  (t : Term m)
  (f g : Subst m n)
  → (∀ x → f x ≡ g x)
  → apply f t ≡ apply g t
apply-cong (var x) f g prf = prf x
apply-cong (val a) f g prf = refl
apply-cong ⟨ t₁ , t₂ ⟩ f g prf = cong₂ ⟨_,_⟩ (apply-cong t₁ f g prf) (apply-cong t₂ f g prf)

private variable
  x y : Fin n
  t u : Term n
  a b : A
  t₁ t₂ : Term n
  u₁ u₂ : Term n

data _∈_ : Fin n → Term n → Set where
  var : x ∈ var x
  ⟨_,-⟩ : x ∈ t → x ∈ ⟨ t , u ⟩
  ⟨-,_⟩ : x ∈ u → x ∈ ⟨ t , u ⟩

_∉_ : Fin n → Term n → Set
x ∉ t = ¬ (x ∈ t)

_∈?_ : ∀ (x : Fin n) t → Dec (x ∈ t)

x ∈? var y with Fin⟨ x ≟ y ⟩
... | yes refl = yes var
... | no ¬refl = no (λ{var → ¬refl refl})
x ∈? val _ = no λ()
x ∈? ⟨ t₁ , t₂ ⟩ with x ∈? t₁
... | yes x∈t₁ = yes ⟨ x∈t₁ ,-⟩
... | no ¬x∈t₁ with x ∈? t₂
... | yes x∈t₂ = yes ⟨-, x∈t₂ ⟩
... | no ¬x∈t₂ = no λ{⟨ x∈t₁ ,-⟩ → ¬x∈t₁ x∈t₁
                    ; ⟨-, x∈t₂ ⟩ → ¬x∈t₂ x∈t₂}

punchOut-∉ : ∀ {x : Fin (suc n)} {t : Term (suc n)} → x ∉ t → Term n

punchOut-∉ {x = x} {t = var y} x∉t = var (punchOut {i = x} {j = y} λ{refl → x∉t var})
punchOut-∉ {t = val a} x∉t = val a
punchOut-∉ {t = ⟨ t₁ , t₂ ⟩} x∉t = ⟨ punchOut-∉ (x∉t ∘ ⟨_,-⟩) , punchOut-∉ (x∉t ∘ ⟨-,_⟩) ⟩

⟨⟩-inj : ⟨ t₁ , t₂ ⟩ ≡ ⟨ u₁ , u₂ ⟩ → t₁ ≡ u₁ × t₂ ≡ u₂
⟨⟩-inj refl = refl , refl

_↦_ : Fin (suc n) → Term n → Subst (suc n) n
(x ↦ t) y with Fin⟨ x ≟ y ⟩
... | yes refl = t
... | no x≢y = var (punchOut x≢y)
