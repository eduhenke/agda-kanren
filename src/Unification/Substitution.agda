{-# OPTIONS --safe #-}

open import Data.Nat hiding (_≟_; _/_; _≤_; _+_)
open import Data.Fin as Fin renaming (_≟_ to Fin⟨_≟_⟩) hiding (lift; _≤_; _+_)
open import Data.Fin.Properties using (suc-injective)
open import Data.Fin.Patterns
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation
open import Data.Empty
open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Definitions using (DecidableEquality)
open import Function.Base using (_∘_)
open import Data.Product
open import Data.Maybe

module Unification.Substitution (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Term A A⟨_≟_⟩ public

private variable
  n n′ n″ n‴ m l k : ℕ
  t₁ t₂ u₁ u₂ : Term n

data AList : ℕ → ℕ → Set where
  ε     : AList n n
  _↦_⨾_ : (x : Fin (suc m)) (t : Term m) (σ : AList m n) → AList (suc m) n

sub : AList m n → Subst m n
sub ε           = var
sub (x ↦ t ⨾ σ) = sub σ ◇ (x ↦ t)

infixr 5 _↦_⨾_

_++ₐ_ : AList m n → AList l m → AList l n
ρ ++ₐ ε = ρ
ρ ++ₐ (x ↦ t ⨾ σ) = x ↦ t ⨾ (ρ ++ₐ σ)

sub-single : ∀ (t′ : Term m) (x : Fin (suc m)) → ∀ y → sub (x ↦ t′ ⨾ ε) y ≡ (x ↦ t′) y
sub-single t′ x y = sym (apply-id ((x ↦ t′) y))

sub-++-◇ : ∀ (f : AList m n) (g : AList l m) → ∀ y → sub (f ++ₐ g) y ≡ (sub f ◇ sub g) y
sub-++-◇ f ε y = refl
sub-++-◇ f (x ↦ t ⨾ g) y =
  trans (apply-cong ((x ↦ t) y) (sub (f ++ₐ g)) (sub f ◇ sub g) (sub-++-◇ f g))
        (sym (apply-assoc ((x ↦ t) y) (sub g) (sub f)))

amgu : (t u : Term m) → ∃ (AList m) → Maybe (∃ (AList m))
mgu  : (t u : Term m) → Maybe (∃ (AList m))

amgu t u (n , (z ↦ r ⨾ ρ)) = do
  let z↦r = apply (z ↦ r)
  n′ , ρ′ ← amgu (z↦r t) (z↦r u) (n , ρ)
  just (n′ , (z ↦ r ⨾ ρ′))

amgu (val a) (val b) (m , ε) with A⟨ a ≟ b ⟩
... | yes refl = just (m , ε)
... | no ¬refl = nothing
amgu (val _) ⟨ u₁ , u₂ ⟩ (m , ε) = nothing
amgu ⟨ t₁ , t₂ ⟩ (val _) (m , ε) = nothing
amgu ⟨ t₁ , t₂ ⟩ ⟨ u₁ , u₂ ⟩ (m , ε) = do
  ρ′ ← amgu t₁ u₁ (m , ε)
  amgu t₂ u₂ ρ′

amgu (var x) (var y) (suc m , ε) with Fin⟨ x ≟ y ⟩
... | yes refl = just (suc m , ε)
... | no  x≢y  = just (m , (x ↦ (var (punchOut x≢y)) ⨾ ε))
amgu (var x) u (suc m , ε) with x ∈? u
... | yes _   = nothing
... | no  x∉u = just (m , (x ↦ (punchOut-∉ x∉u) ⨾ ε))
amgu t (var y) (suc m , ε) with y ∈? t
... | yes _   = nothing
... | no  y∉t = just (m , (y ↦ (punchOut-∉ y∉t) ⨾ ε))

mgu {m} t u = amgu t u (m , ε)

liftAList : AList m n → AList (suc m) (suc n)

liftAList ε             = ε
liftAList (x ↦ t ⨾ σ) = suc x ↦ weaken t ⨾ liftAList σ

-- weaken t is the same as substituting each var y with var (suc y)
weaken-as-apply : ∀ (t : Term m) → weaken t ≡ apply (λ z → var (Fin.suc z)) t
weaken-as-apply (var x)      = refl
weaken-as-apply (val a)      = refl
weaken-as-apply ⟨ t₁ , t₂ ⟩ = cong₂ ⟨_,_⟩ (weaken-as-apply t₁) (weaken-as-apply t₂)

-- apply over a weakened term is equivalent to apply with a shifted substitution
apply-weaken : ∀ (t : Term m) (g : Subst (suc m) n)
  → apply g (weaken t) ≡ apply (g ∘ Fin.suc) t
apply-weaken t g =
  begin
    apply g (weaken t)
  ≡⟨ cong (apply g) (weaken-as-apply t) ⟩
    apply g (apply (λ z → var (Fin.suc z)) t)
  ≡⟨ apply-assoc t (λ z → var (Fin.suc z)) g ⟩
    apply (λ x → apply g (var (Fin.suc x))) t
  ≡⟨⟩
    apply (g ∘ Fin.suc) t
  ∎

punchOut-irrelevant : ∀ {n} {i j : Fin (suc n)} (p q : i ≢ j)
  → punchOut p ≡ punchOut q
punchOut-irrelevant {i = zero}  {j = zero}  p _ = ⊥-elim (p refl)
punchOut-irrelevant {i = zero}  {j = suc _} _ _ = refl
punchOut-irrelevant {i = suc _} {j = zero}  _ _ = refl
punchOut-irrelevant {n = suc n} {i = suc i} {j = suc j} p q =
  cong Fin.suc (punchOut-irrelevant (p ∘ cong Fin.suc) (q ∘ cong Fin.suc))

-- (suc x ↦ weaken t) (suc y) ≡ weaken ((x ↦ t) y)
↦-suc : ∀ (t : Term m) (x y : Fin (suc m))
  → (suc x ↦ weaken t) (suc y) ≡ weaken ((x ↦ t) y)
↦-suc t x y with Fin⟨ x ≟ y ⟩ | Fin⟨ suc x ≟ suc y ⟩
... | yes refl | yes refl = refl
... | yes refl | no  p    = ⊥-elim (p refl)
... | no  x≢y  | yes p    = ⊥-elim (x≢y (suc-injective p))
... | no  x≢y  | no sx≢sy = cong (λ z → var (Fin.suc z)) (punchOut-irrelevant (sx≢sy ∘ cong Fin.suc) x≢y)

-- Property P1: new variable 0F remains free
sub-liftAList-new : ∀ (σ : AList m n) → sub (liftAList σ) 0F ≡ var 0F
sub-liftAList-new ε = refl
sub-liftAList-new (x ↦ t ⨾ σ) =
  begin
    sub (suc x ↦ weaken t ⨾ liftAList σ) 0F
  ≡⟨⟩
    apply (sub (liftAList σ)) ((suc x ↦ weaken t) 0F)
  ≡⟨ cong (apply (sub (liftAList σ))) step ⟩
    apply (sub (liftAList σ)) (var 0F)
  ≡⟨⟩
    sub (liftAList σ) 0F
  ≡⟨ sub-liftAList-new σ ⟩
    var 0F
  ∎
  where
    step : (suc x ↦ weaken t) 0F ≡ var 0F
    step with Fin⟨ suc x ≟ 0F ⟩
    ... | yes ()
    ... | no  _  = refl

-- Property P2: old variables suc y are weakened
sub-liftAList-old : ∀ (σ : AList m n) (y : Fin m)
  → sub (liftAList σ) (suc y) ≡ weaken (sub σ y)
sub-liftAList-old ε y = refl
sub-liftAList-old (x ↦ t ⨾ σ) y =
  begin
    sub (suc x ↦ weaken t ⨾ liftAList σ) (suc y)
  ≡⟨⟩
    apply (sub (liftAList σ)) ((suc x ↦ weaken t) (suc y))
  ≡⟨ cong (apply (sub (liftAList σ))) (↦-suc t x y) ⟩
    apply (sub (liftAList σ)) (weaken ((x ↦ t) y))
  ≡⟨ apply-weaken ((x ↦ t) y) (sub (liftAList σ)) ⟩
    apply (sub (liftAList σ) ∘ Fin.suc) ((x ↦ t) y)
  ≡⟨ apply-cong ((x ↦ t) y) _ _ (sub-liftAList-old σ) ⟩
    apply (weaken ∘ sub σ) ((x ↦ t) y)
  ≡⟨ apply-cong ((x ↦ t) y) _ _ (λ z → weaken-as-apply (sub σ z)) ⟩
    apply (λ z → apply (λ z → var (Fin.suc z)) (sub σ z)) ((x ↦ t) y)
  ≡⟨ sym (apply-assoc ((x ↦ t) y) (sub σ) (λ z → var (Fin.suc z))) ⟩
    apply (λ z → var (Fin.suc z)) (apply (sub σ) ((x ↦ t) y))
  ≡⟨ sym (weaken-as-apply (apply (sub σ) ((x ↦ t) y))) ⟩
    weaken (apply (sub σ) ((x ↦ t) y))
  ≡⟨⟩
    weaken (sub (x ↦ t ⨾ σ) y)
  ∎

sub-liftAList : ∀ (σ : AList m n)
  → sub (liftAList σ) 0F ≡ var 0F
  × (∀ (y : Fin m) → sub (liftAList σ) (suc y) ≡ weaken (sub σ y))
sub-liftAList σ = sub-liftAList-new σ , sub-liftAList-old σ
