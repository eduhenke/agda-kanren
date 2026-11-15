{-# OPTIONS --safe #-}

open import Data.Nat hiding (_≟_; _/_; _≤_; _+_)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Fin as Fin renaming (_≟_ to Fin⟨_≟_⟩) hiding (lift; _≤_; _+_)
open import Data.Fin.Properties using (punchOut-punchIn; punchIn-punchOut; punchInᵢ≢i)
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
open import Data.Maybe using (Maybe; just; nothing)

module Unification.Properties (A : Set) (A⟨_≟_⟩ : DecidableEquality A) where

open import Unification.Substitution A A⟨_≟_⟩ public

private variable
  n n′ n″ n‴ m l k : ℕ
  x y : Fin n
  t u : Term n
  a b : A
  t₁ t₂ : Term n
  u₁ u₂ : Term n

-- a property of substitutions with m source variables

Property : (m : ℕ) → Set₁
Property m = ∀ {n : ℕ} → Subst m n → Set

Unifies : (t u : Term m) → Property m
Unifies t u f = apply f t ≡ apply f u

_∧_ : Property m → Property m → Property m
(P ∧ Q) f = P f × Q f

_[-◇_] : (P : Property m) → (f : Subst m n) → Property n
(P [-◇ f ]) g = P (g ◇ f)

_⇔_ : Property m → Property m → Property m
(P ⇔ Q) f = (P f → Q f) × (Q f → P f)

infix 4 _≤_

_≤_ : (f : Subst m n) → (g : Subst m n′) → Set
f ≤ g = ∃ λ f′ → ∀ x → f x ≡ (f′ ◇ g) x

≤-refl : ∀ (f : Subst m n) → f ≤ f
≤-refl f = var , λ x → apply-id (f x)

◇-assoc : ∀ (a : Subst n″ n‴) (b : Subst n′ n″) (c : Subst n n′)
  → ∀ x → (a ◇ (b ◇ c)) x ≡ ((a ◇ b) ◇ c) x
◇-assoc a b c x = apply-assoc (c x) b a

≤-trans : ∀ (f : Subst m n) (g : Subst m n′) (h : Subst m n″)
  → f ≤ g
  → g ≤ h
  → f ≤ h
≤-trans f g h (fg-rem , fg-prf) (gh-rem , gh-prf) = fg-rem ◇ gh-rem , λ x →
  begin
    f x
  ≡⟨ fg-prf x ⟩
    apply fg-rem (g x)
  ≡⟨ cong (apply fg-rem) (gh-prf x) ⟩
    apply fg-rem (apply gh-rem (h x))
  ≡⟨ apply-assoc (h x) gh-rem fg-rem ⟩
    apply (fg-rem ◇ gh-rem) (h x)
  ∎

≤-var : ∀ (f : Subst m n) → f ≤ var
≤-var f = f , λ _ → refl

≤-cong : ∀ (f : Subst m n) (g : Subst m n′)
  → (h : Subst l m)
  → f ≤ g
  → f ◇ h ≤ g ◇ h
≤-cong f g h (fg-rem , fg-prf) = fg-rem , λ x →
  begin
    apply f (h x)
  ≡⟨ apply-cong (h x) f (fg-rem ◇ g) fg-prf ⟩
    apply (fg-rem ◇ g) (h x)
  ≡⟨ sym (apply-assoc (h x) g fg-rem) ⟩
    apply fg-rem (apply g (h x))
  ∎

Max : ∀ {m} → Property m → Property m
Max P f = P f × (∀ {n′} (f′ : Subst _ n′) → P f′ → f′ ≤ f)

Nothing : (P : Property m) → Set
Nothing {m} P = ∀ {n : ℕ} → (f : Subst m n) → ¬ P f

Nothing-ext : ∀ (P : Property m) (f : Subst m n) → Nothing P → Nothing (P [-◇ f ])
Nothing-ext P f nothingP g Pgf = nothingP (g ◇ f) Pgf

-- Transform the property in Max P f, given a bidirectional conversion between P and Q
Max-map : ∀ {m n} {P Q : Property m} {f : Subst m n}
  → (P f → Q f)
  → (∀ {n′} {g : Subst m n′} → Q g → P g)
  → Max P f → Max Q f
Max-map P→Q Q→P (Pf , maxPf) = P→Q Pf , λ f′ Qf′ → maxPf f′ (Q→P Qf′)

DClosed : ∀ {m} → Property m → Set
DClosed {m} P = ∀ {n n′} (f : Subst m n) (g : Subst m n′) → f ≤ g → P g → P f

Unifies-DClosed : ∀ (t u : Term m) → DClosed (Unifies t u)

∈-no-unif : x ∈ ⟨ u₁ , u₂ ⟩ → Nothing (Unifies (var x) ⟨ u₁ , u₂ ⟩)

Unifies-var-elim : ∀ (t′ : Term m) (x : Fin (suc m))
  → Max (Unifies (var x) (apply (var ∘ punchIn x) t′)) (x ↦ t′)

Max-pw-cong : ∀ {m n} (P : Property m) (f g : Subst m n)
  → (∀ x → f x ≡ g x) → DClosed P → Max P f → Max P g
Max-pw-cong P f g pw dcP (Pf , maxF) =
  dcP g f (var , λ x → trans (sym (pw x)) (apply-id (f x))) Pf ,
  λ f′ Pf′ → ≤-trans f′ f g (maxF f′ Pf′) (var , λ x → trans (pw x) (apply-id (g x)))

Unifies-DClosed t u f g (rem , prf) unif-g = begin
  apply f t
    ≡⟨ apply-cong t f (rem ◇ g) prf ⟩
  apply (rem ◇ g) t
    ≡⟨ sym (apply-assoc t g rem) ⟩
  apply rem (apply g t)
    ≡⟨ cong (apply rem) unif-g ⟩
  apply rem (apply g u)
    ≡⟨ apply-assoc u g rem ⟩
  apply (rem ◇ g) u
    ≡⟨ apply-cong u (rem ◇ g) f (λ x → sym (prf x)) ⟩
  apply f u
    ∎

∧-failure-left : ∀ (P Q : Property m) (a : Subst m n)
  → Nothing (P [-◇ a ]) → Nothing ((P ∧ Q) [-◇ a ])
∧-failure-left P Q a nothingP g (Pga , Qga) = nothingP g Pga

∧-failure-right : ∀ {m n n′} (P Q : Property m) (a : Subst m n) (p : Subst n n′)
  → DClosed Q → Max (P [-◇ a ]) p → Nothing (Q [-◇ (p ◇ a) ]) → Nothing ((P ∧ Q) [-◇ a ])
∧-failure-right P Q a p dcq (Pa , maxP) nothingQ {n″} g (Pga , Qga) =
  let (wit , prf) = maxP g Pga
  in nothingQ wit (dcq (wit ◇ (p ◇ a)) (g ◇ a)
       (var , λ x → trans
         (trans (apply-assoc (a x) p wit) (sym (apply-cong (a x) g (wit ◇ p) prf)))
         (apply-id ((g ◇ a) x)))
       Qga)

Optimist : ∀ (P Q : Property l) (a : Subst l m)
             (p : Subst m n) (q : Subst n n′)
  → DClosed P → DClosed Q
  → Max (P [-◇ a ]) p
  → Max (Q [-◇ (p ◇ a) ]) q
  → Max ((P ∧ Q) [-◇ a ]) (q ◇ p)

Optimist P Q a p q dcp dcq (Ppa , pMax) (Qqpa , qMax) =
  (P-qpa , Q-qpa) , max-proof
  where
    P-qpa : P ((q ◇ p) ◇ a)
    P-qpa = dcp ((q ◇ p) ◇ a) (p ◇ a) (q , λ x → sym (apply-assoc (a x) p q)) Ppa

    Q-qpa : Q ((q ◇ p) ◇ a)
    Q-qpa = dcq ((q ◇ p) ◇ a) (q ◇ (p ◇ a))
              (var , λ x → trans (sym (apply-assoc (a x) p q)) (apply-id _))
              Qqpa

    max-proof : ∀ {n′} (f′ : Subst _ n′) → (P ∧ Q) (f′ ◇ a) → f′ ≤ (q ◇ p)
    max-proof f (Pf , Qf) =
      let (g , f≡gp) = pMax f Pf
          Qgpa : Q (g ◇ (p ◇ a))
          Qgpa = dcq (g ◇ (p ◇ a)) (f ◇ a)
                   (var , λ x → trans (apply-assoc (a x) p g)
                     (trans (sym (apply-cong (a x) f (g ◇ p) f≡gp))
                            (apply-id ((f ◇ a) x))))
                   Qf
          (h , g≡hq) = qMax g Qgpa
      in h , λ x → trans (f≡gp x)
                     (trans (apply-cong (p x) g (h ◇ q) g≡hq)
                            (sym (apply-assoc (p x) q h)))

Unifies-trivial : ∀ (t : Term m) → Max (Unifies t t) var
Unifies-trivial t = refl , λ f′ un → ≤-var f′

Unifies-var-elim t′ x = unif , max
  where
    ↦-punchIn-inverse : ∀ y → (x ↦ t′) (punchIn x y) ≡ var y
    ↦-punchIn-inverse y with Fin⟨ x ≟ punchIn x y ⟩
    ... | yes eq  = ⊥-elim (punchInᵢ≢i x y (sym eq))
    ... | no  neq = cong var (punchOut-punchIn x)

    unif : Unifies (var x) (apply (var ∘ punchIn x) t′) (x ↦ t′)
    unif with Fin⟨ x ≟ x ⟩
    ... | yes refl = begin
        t′
      ≡⟨ apply-id t′ ⟩
        apply var t′
      ≡⟨ apply-cong t′ var (λ z → (x ↦ t′) (punchIn x z)) (λ y → sym (↦-punchIn-inverse y)) ⟩
        apply (λ z → (x ↦ t′) (punchIn x z)) t′
      ≡⟨ sym (apply-assoc t′ (λ z → var (punchIn x z)) (x ↦ t′)) ⟩
        apply (x ↦ t′) (apply (λ z → var (punchIn x z)) t′)
      ∎
    ... | no x≢x = ⊥-elim (x≢x refl)

    max : ∀ {n′} (f : Subst _ n′) → Unifies (var x) (apply (var ∘ punchIn x) t′) f → f ≤ (x ↦ t′)
    max f unif-f = (f ∘ punchIn x) , λ y → helper y
      where
        helper : ∀ y → f y ≡ apply (f ∘ punchIn x) ((x ↦ t′) y)
        helper y with Fin⟨ x ≟ y ⟩
        helper .x | yes refl with Fin⟨ x ≟ x ⟩
        ... | yes _   = trans unif-f (apply-assoc t′ (var ∘ punchIn x) f)
        ... | no  x≢x = ⊥-elim (x≢x refl)
        helper y  | no  x≢y  = cong f (sym (punchIn-punchOut x≢y))

-- Convenience: Unifies-var-elim already in the sub form for amgu-correct
Unifies-var-elim-sub : ∀ (t′ : Term m) (x : Fin (suc m))
  → Max (Unifies (var x) (apply (var ∘ punchIn x) t′)) (sub (x ↦ t′ ⨾ ε))
Unifies-var-elim-sub t′ x =
  Max-pw-cong
    (Unifies (var x) (apply (var ∘ punchIn x) t′))
    (x ↦ t′) (sub (x ↦ t′ ⨾ ε))
    (λ y → sym (sub-single t′ x y))
    (Unifies-DClosed (var x) (apply (var ∘ punchIn x) t′))
    (Unifies-var-elim t′ x)

Max-sym : ∀ (t u : Term m) (f : Subst m n)
  → Max (Unifies t u) f → Max (Unifies u t) f
Max-sym t u f (unif , maximal) = sym unif , λ f′ unif′ → maximal f′ (sym unif′)

Nothing-sym : ∀ (t u : Term m)
  → Nothing (Unifies t u) → Nothing (Unifies u t)
Nothing-sym t u not-unif f unif = not-unif f (sym unif)

-- Key equivalence for the step case: unifying substituted terms
Unifies-subst-iff : ∀ (t u : Term (suc n)) (r : Term n) (z : Fin (suc n)) (f : Subst n k)
  → (Unifies (apply (z ↦ r) t) (apply (z ↦ r) u) f → Unifies t u (f ◇ (z ↦ r)))
  × (Unifies t u (f ◇ (z ↦ r)) → Unifies (apply (z ↦ r) t) (apply (z ↦ r) u) f)
Unifies-subst-iff t u r z f =
  (λ unif → begin
    apply (f ◇ (z ↦ r)) t
  ≡⟨ sym (apply-assoc t (z ↦ r) f) ⟩
    apply f (apply (z ↦ r) t)
  ≡⟨ unif ⟩
    apply f (apply (z ↦ r) u)
  ≡⟨ apply-assoc u (z ↦ r) f ⟩
    apply (f ◇ (z ↦ r)) u
  ∎)
  ,
  (λ unif → begin
    apply f (apply (z ↦ r) t)
  ≡⟨ apply-assoc t (z ↦ r) f ⟩
    apply (f ◇ (z ↦ r)) t
  ≡⟨ unif ⟩
    apply (f ◇ (z ↦ r)) u
  ≡⟨ sym (apply-assoc u (z ↦ r) f) ⟩
    apply f (apply (z ↦ r) u)
  ∎)

Unifies-cong : ∀ (t u : Term m) {n} (f g : Subst m n)
  → (∀ x → f x ≡ g x) → Unifies t u f → Unifies t u g
Unifies-cong t u f g pw h =
  begin
    apply g t
  ≡⟨ sym (apply-cong t f g pw) ⟩
    apply f t
  ≡⟨ h ⟩
    apply f u
  ≡⟨ apply-cong u f g pw ⟩
    apply g u
  ∎

-- Occur check: if x ∉ t, then t can be expressed in a smaller scope
module OccurCheck where
  punchOut-∉-inverse : ∀ {x : Fin (suc n)} {t : Term (suc n)} (x∉t : x ∉ t)
    → t ≡ apply (var ∘ punchIn x) (punchOut-∉ x∉t)
  punchOut-∉-inverse {t = var y} x∉t = cong var (sym (punchIn-punchOut _))
  punchOut-∉-inverse {t = val a} x∉t = refl
  punchOut-∉-inverse {t = ⟨ t₁ , t₂ ⟩} x∉t =
    cong₂ ⟨_,_⟩ (punchOut-∉-inverse (x∉t ∘ ⟨_,-⟩)) (punchOut-∉-inverse (x∉t ∘ ⟨-,_⟩))

-- No cycle: a variable never unifies with a pair that contains it,
-- because applying a substitution preserves the size ordering.
size : Term n → ℕ
size (var _)       = 1
size (val _)       = 1
size ⟨ t₁ , t₂ ⟩ = suc (size t₁ ℕ.+ size t₂)

∈-size : ∀ (f : Subst m n) → x ∈ t → size (f x) ℕ.≤ size (apply f t)
∈-size f var       = ℕₚ.≤-refl
∈-size f ⟨ x∈t ,-⟩ = ℕₚ.m≤n⇒m≤1+n (ℕₚ.m≤n⇒m≤n+o _ (∈-size f x∈t))
∈-size f ⟨-, x∈u ⟩ = ℕₚ.m≤n⇒m≤1+n (ℕₚ.m≤n⇒m≤o+n _ (∈-size f x∈u))

∈-no-unif ⟨ x∈u ,-⟩ f eq =
  ℕₚ.<-irrefl (cong size eq) (ℕ.s≤s (ℕₚ.m≤n⇒m≤n+o _ (∈-size f x∈u)))
∈-no-unif ⟨-, x∈u ⟩ f eq =
  ℕₚ.<-irrefl (cong size eq) (ℕ.s≤s (ℕₚ.m≤n⇒m≤o+n _ (∈-size f x∈u)))

open OccurCheck public

data MguResult (t u : Term m) : Maybe (∃ (AList m)) → Set where
  unifies     : ∀ {n} (σ : AList m n) → Max (Unifies t u) (sub σ)
              → MguResult t u (just (n , σ))
  not-unifies : Nothing (Unifies t u) → MguResult t u nothing

mgu-correct : ∀ (t u : Term m) → MguResult t u (mgu t u)

data AmguResult (t u : Term m) (ρ : AList m l)
              : Maybe (∃ (AList m)) → Set where
  unifies : (σ : AList l n) → Max (Unifies t u [-◇ sub ρ ]) (sub σ)
          → AmguResult t u ρ (just (n , σ ++ₐ ρ))
  not-unifies : (¬un : Nothing (Unifies t u [-◇ sub ρ ]))
              → AmguResult t u ρ nothing

amgu-correct : ∀ (t u : Term m) (ρ : AList m l)
  → AmguResult t u ρ (amgu t u (l , ρ))

-- Pending binding: recurse on the substituted terms under the rest of
-- the accumulator; unifiers correspond through Unifies-subst-iff.
amgu-correct t u (z ↦ r ⨾ ρ)
  with amgu (apply (z ↦ r) t) (apply (z ↦ r) u) (_ , ρ)
     | amgu-correct (apply (z ↦ r) t) (apply (z ↦ r) u) ρ
... | just _ | unifies σ″ max =
  unifies σ″
    (Max-map
      (λ unif-zt →
         Unifies-cong t u ((sub σ″ ◇ sub ρ) ◇ (z ↦ r)) (sub σ″ ◇ (sub ρ ◇ (z ↦ r)))
           (λ x → sym (◇-assoc (sub σ″) (sub ρ) (z ↦ r) x))
           (proj₁ (Unifies-subst-iff t u r z (sub σ″ ◇ sub ρ)) unif-zt))
      (λ {_} {g} unif-t →
         proj₂ (Unifies-subst-iff t u r z (g ◇ sub ρ))
           (Unifies-cong t u (g ◇ (sub ρ ◇ (z ↦ r))) ((g ◇ sub ρ) ◇ (z ↦ r))
             (◇-assoc g (sub ρ) (z ↦ r))
             unif-t))
      max)
... | nothing | not-unifies ¬un =
  not-unifies (λ f unif-t →
    ¬un f (proj₂ (Unifies-subst-iff t u r z (f ◇ sub ρ))
      (Unifies-cong t u (f ◇ (sub ρ ◇ (z ↦ r))) ((f ◇ sub ρ) ◇ (z ↦ r))
        (◇-assoc f (sub ρ) (z ↦ r))
        unif-t)))
-- Empty accumulator: by the shape of the terms.
amgu-correct (val a) (val b) ε with A⟨ a ≟ b ⟩
... | yes refl = unifies ε (Unifies-trivial (val a))
... | no ¬refl = not-unifies (λ{f refl → ¬refl refl})
amgu-correct (val _) ⟨ u₁ , u₂ ⟩ ε = not-unifies λ{f ()}
amgu-correct ⟨ t₁ , t₂ ⟩ (val _) ε = not-unifies λ{f ()}
amgu-correct ⟨ t₁ , t₂ ⟩ ⟨ u₁ , u₂ ⟩ ε with amgu t₁ u₁ (_ , ε) | amgu-correct t₁ u₁ ε
... | nothing | not-unifies ¬un₁ =
  not-unifies (λ f un′ →
    ∧-failure-left
      (Unifies t₁ u₁) (Unifies t₂ u₂)
      (sub ε)
      ¬un₁ f (⟨⟩-inj un′)
  )
... | just _ | unifies σ max₁ with amgu t₂ u₂ (_ , σ) | amgu-correct t₂ u₂ σ
... | nothing | not-unifies ¬un₂ =
  not-unifies (λ f un′ →
    ∧-failure-right
      (Unifies t₁ u₁) (Unifies t₂ u₂)
      (sub ε) (sub σ)
      (Unifies-DClosed t₂ u₂)
      max₁
      (λ f′ un₂′ → ¬un₂ f′ (Unifies-cong t₂ u₂
        (f′ ◇ (sub σ ◇ sub ε)) (f′ ◇ sub σ)
        (λ y → cong (apply f′) (sym (sub-++-◇ σ ε y)))
        un₂′))
      f
      (⟨⟩-inj un′)
    )
... | just _ | unifies σ′ max₂ =
      unifies (σ′ ++ₐ σ) (Max-pw-cong
        (Unifies ⟨ t₁ , t₂ ⟩ ⟨ u₁ , u₂ ⟩ [-◇ sub ε ])
        (sub σ′ ◇ sub σ) (sub (σ′ ++ₐ σ))
        (λ y → sym (sub-++-◇ σ′ σ y))
        (λ f g f≤g → Unifies-DClosed ⟨ t₁ , t₂ ⟩ ⟨ u₁ , u₂ ⟩ (f ◇ sub ε) (g ◇ sub ε) (≤-cong f g (sub ε) f≤g))
        pair-unifies-max)
      where
        max₂' : Max (Unifies t₂ u₂ [-◇ sub σ ◇ sub ε ]) (sub σ′)
        max₂' = Max-map
          (λ p → Unifies-cong t₂ u₂
            (sub σ′ ◇ sub σ) (sub σ′ ◇ (sub σ ◇ sub ε))
            (λ y → cong (apply (sub σ′)) (sub-++-◇ σ ε y)) p)
          (λ {_} {g} q → Unifies-cong t₂ u₂
            (g ◇ (sub σ ◇ sub ε)) (g ◇ sub σ)
            (λ y → cong (apply g) (sym (sub-++-◇ σ ε y))) q)
          max₂
        conj-max : Max ((Unifies t₁ u₁ ∧ Unifies t₂ u₂) [-◇ sub ε ]) (sub σ′ ◇ sub σ)
        conj-max = Optimist (Unifies t₁ u₁) (Unifies t₂ u₂) (sub ε) (sub σ) (sub σ′) (Unifies-DClosed t₁ u₁) (Unifies-DClosed t₂ u₂) max₁ max₂'
        pair-unifies-max : Max (Unifies ⟨ t₁ , t₂ ⟩ ⟨ u₁ , u₂ ⟩ [-◇ sub ε ]) (sub σ′ ◇ sub σ)
        pair-unifies-max with conj-max
        ... | (unif₁ , unif₂) , max-witness =
          cong₂ ⟨_,_⟩ unif₁ unif₂ , λ f′ unif-pair → max-witness f′ (⟨⟩-inj unif-pair)
amgu-correct {l = suc l} (var x) (var y) ε with Fin⟨ x ≟ y ⟩
... | yes refl = unifies ε (Unifies-trivial (var x))
... | no x≢y = unifies σ max-unifies-x-y
  where
    y′ : Term l
    y′ = var (punchOut x≢y)

    σ : AList (suc l) l
    σ = x ↦ y′ ⨾ ε

    thinned-y : Term (suc l)
    thinned-y = apply (var ∘ punchIn x) y′

    -- The core lemma: binding x to the punched-out y unifies them (in sub form)
    max-sub : Max (Unifies (var x) thinned-y) (sub σ)
    max-sub = Unifies-var-elim-sub y′ x

    -- Simplify: punchIn x (punchOut x≢y) is just y
    max-unifies-x-y : Max (Unifies (var x) (var y)) (sub σ)
    max-unifies-x-y = subst (λ t → Max (Unifies (var x) t) (sub σ)) (cong var (punchIn-punchOut x≢y)) max-sub
-- flexRigid x↦u
amgu-correct {l = suc l} (var x) (val b) ε = unifies (x ↦ val b ⨾ ε) (Unifies-var-elim-sub (val b) x)
amgu-correct {l = suc l} (var x) ⟨ u₁ , u₂ ⟩ ε with x ∈? ⟨ u₁ , u₂ ⟩
... | yes x∈u = not-unifies (∈-no-unif x∈u)
... | no  x∉u =
  let u′ = punchOut-∉ x∉u
      σ  = x ↦ u′ ⨾ ε
  in unifies σ (subst (λ t → Max (Unifies (var x) t) (sub σ))
                      (sym (punchOut-∉-inverse x∉u)) (Unifies-var-elim-sub u′ x))
-- flexRigid y↦t
amgu-correct {l = suc l} (val b) (var y) ε =
  unifies (y ↦ val b ⨾ ε)    (Max-sym (var y) (val b) (sub (y ↦ val b ⨾ ε)) (Unifies-var-elim-sub (val b) y))
amgu-correct {l = suc l} ⟨ t₁ , t₂ ⟩ (var y) ε with y ∈? ⟨ t₁ , t₂ ⟩
... | yes y∈t = not-unifies (Nothing-sym (var y) ⟨ t₁ , t₂ ⟩ (∈-no-unif y∈t))
... | no  y∉t =
  let t′ = punchOut-∉ y∉t
      σ  = y ↦ t′ ⨾ ε
  in unifies σ (Max-sym (var y) ⟨ t₁ , t₂ ⟩ (sub σ)
                 (subst (λ t → Max (Unifies (var y) t) (sub σ))
                        (sym (punchOut-∉-inverse y∉t)) (Unifies-var-elim-sub t′ y)))
amgu-correct {l = zero} _ (var ()) ε

-- From the empty accumulator.
mgu-correct t u = from (amgu-correct t u ε)
  where
    from : ∀ {r} → AmguResult t u ε r → MguResult t u r
    from (unifies σ max)   = unifies σ max
    from (not-unifies ¬un)      = not-unifies ¬un
