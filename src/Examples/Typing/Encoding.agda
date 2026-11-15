{-# OPTIONS --safe #-}

-- The encoding behind Examples.Typing: the symbols that label terms,
-- the object language of types and λ-terms, and the translation between
-- it and Terms.

module Examples.Typing.Encoding where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
import Data.Fin.Properties as FinP
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- Symbols

-- The constants of the encoding: the base type, two propositional
-- atoms, and one tag per syntactic form.
data Sym : Set where
  base atomP atomQ : Sym
  zeroˢ sucˢ       : Sym
  varˢ lamˢ appˢ   : Sym

-- Decidable equality, through a round trip into Fin.
private
  toFin : Sym → Fin 8
  toFin base  = 0F
  toFin atomP = 1F
  toFin atomQ = 2F
  toFin zeroˢ = 3F
  toFin sucˢ  = 4F
  toFin varˢ  = 5F
  toFin lamˢ  = 6F
  toFin appˢ  = 7F
  
  fromFin : Fin 8 → Sym
  fromFin 0F = base
  fromFin 1F = atomP
  fromFin 2F = atomQ
  fromFin 3F = zeroˢ
  fromFin 4F = sucˢ
  fromFin 5F = varˢ
  fromFin 6F = lamˢ
  fromFin _  = appˢ

  from-to : ∀ x → fromFin (toFin x) ≡ x
  from-to base  = refl
  from-to atomP = refl
  from-to atomQ = refl
  from-to zeroˢ = refl
  from-to sucˢ  = refl
  from-to varˢ  = refl
  from-to lamˢ  = refl
  from-to appˢ  = refl
  
_≟ˢ_ : DecidableEquality Sym
x ≟ˢ y = map′ (λ e → trans (sym (from-to x)) (trans (cong fromFin e) (from-to y)))
              (cong toFin) (toFin x FinP.≟ toFin y)

open import Unification.Properties Sym _≟ˢ_ hiding (_∧_)

private variable
  c m : ℕ

------------------------------------------------------------------------
-- The object language

-- Types, with type variables for the unknowns of inference.
data Ty (c : ℕ) : Set where
  tv    : Fin c → Ty c
  ι P Q : Ty c
  _⇒_   : Ty c → Ty c → Ty c

infixr 5 _⇒_

-- Untyped λ-terms, variables as de Bruijn indices.
data Exp : Set where
  var : ℕ → Exp
  lam : Exp → Exp
  app : Exp → Exp → Exp

------------------------------------------------------------------------
-- The encoding into Terms

pattern Z       = val zeroˢ
pattern S k     = ⟨ val sucˢ , k ⟩
pattern VAR k   = ⟨ val varˢ , k ⟩
pattern LAM b   = ⟨ val lamˢ , b ⟩
pattern APP f x = ⟨ val appˢ , ⟨ f , x ⟩ ⟩

-- An arrow A ⇒ B is a plain pair ⟨ A , B ⟩.

⌜_⌝ᵀ : Ty c → Term c
⌜ tv x  ⌝ᵀ = var x
⌜ ι     ⌝ᵀ = val base
⌜ P     ⌝ᵀ = val atomP
⌜ Q     ⌝ᵀ = val atomQ
⌜ A ⇒ B ⌝ᵀ = ⟨ ⌜ A ⌝ᵀ , ⌜ B ⌝ᵀ ⟩

⌜_⌝ᴺ : ℕ → Term c
⌜ zero  ⌝ᴺ = Z
⌜ suc k ⌝ᴺ = S ⌜ k ⌝ᴺ

⌜_⌝ : Exp → Term c
⌜ var k   ⌝ = VAR ⌜ k ⌝ᴺ
⌜ lam e   ⌝ = LAM ⌜ e ⌝
⌜ app f x ⌝ = APP ⌜ f ⌝ ⌜ x ⌝

-- Reading answers back; partial, since an answer may leave parts unknown.
⌞_⌟ᵀ : Term c → Maybe (Ty c)
⌞ var x         ⌟ᵀ = just (tv x)
⌞ val base      ⌟ᵀ = just ι
⌞ val atomP     ⌟ᵀ = just P
⌞ val atomQ     ⌟ᵀ = just Q
⌞ ⟨ A , B ⟩     ⌟ᵀ = ⌞ A ⌟ᵀ >>= λ A′ → ⌞ B ⌟ᵀ >>= λ B′ → just (A′ ⇒ B′)
⌞ _             ⌟ᵀ = nothing

⌞_⌟ᴺ : Term c → Maybe ℕ
⌞ Z   ⌟ᴺ = just zero
⌞ S k ⌟ᴺ = ⌞ k ⌟ᴺ >>= λ k′ → just (suc k′)
⌞ _   ⌟ᴺ = nothing

⌞_⌟ : Term c → Maybe Exp
⌞ VAR k   ⌟ = ⌞ k ⌟ᴺ >>= λ k′ → just (var k′)
⌞ LAM b   ⌟ = ⌞ b ⌟ >>= λ b′ → just (lam b′)
⌞ APP f x ⌟ = ⌞ f ⌟ >>= λ f′ → ⌞ x ⌟ >>= λ x′ → just (app f′ x′)
⌞ _       ⌟ = nothing


-- Numerals are closed, so no substitution changes them.
apply-⌜⌝ᴺ : ∀ (θ : Subst c m) k → apply θ ⌜ k ⌝ᴺ ≡ ⌜ k ⌝ᴺ
apply-⌜⌝ᴺ θ zero    = refl
apply-⌜⌝ᴺ θ (suc k) = cong S (apply-⌜⌝ᴺ θ k)
