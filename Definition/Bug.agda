------------------------------------------------------------------------
-- Equality in the logical relation is transitive
------------------------------------------------------------------------

module Definition.Bug
  {a} {M : Set a}
  where

open import Agda.Primitive using (lsuc)
open import Data.Product using (Σ; ∃₂; _,_)

data Nat : Set where
  zero : Nat
  1+_  : (n : Nat) → Nat

data _≤′_ (m : Nat) : Nat → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ (1+ n)

_<′_ : (m n : Nat) → Set
m <′ n = (1+ m) ≤′ n

record ⊤₂ : Set a where
  instance constructor tt₂


data Term : Set a where

private
  variable
    ℓ l : Nat
    t t′ u u′ : Term

data Product {n : Nat} : Set a where
  ne    : Product


-- Ordering of type levels.

record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    ⊩U : Set a
    ⊩B : Set a

    ⊩ : Set a
    ⊩_/_ : (A : Term) → ⊩ → Set a

module LogRel (l : Nat) (rec : ∀ {l′} → l′ <′ l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record ⊩₁U : Set a where
    constructor Uᵣ
    field
      l′  : Nat
      l<  : l′ <′ l

  -- Universe term equality
  record ⊩₁U/ : Set a where
    constructor Uₜ₌



  record ⊩ₗB : Set a where
    constructor Bᵣ
    eta-equality

  -- Term equality of Σ-type
  ⊩ₗΣ_/_ :
    (A : Term)
    ([A] : ⊩ₗB) → Set a
  ⊩ₗΣ_/_
    A
    Bᵣ =
    ∃₂ λ (t′ u′ : Term) →
                Σ Product λ pProd
                → ⊤₂

  -- Logical relation definition
  data ⊩ₗ : Set a where
    Uᵣ  : ⊩₁U → ⊩ₗ
    Bᵣ  : ⊩ₗB → ⊩ₗ

  ⊩ₗ_/_ : (A : Term) → ⊩ₗ → Set a
  ⊩ₗ A / Uᵣ (Uᵣ l′ l<) = ⊩₁U/
  ⊩ₗ A / Bᵣ ΣA  = ⊩ₗΣ A / ΣA

  kit : LogRelKit
  kit = Kit ⊩₁U ⊩ₗB
            ⊩ₗ ⊩ₗ_/_

open LogRel public
  using
    (Uᵣ; Bᵣ; Uₜ₌;
     module ⊩₁U; module ⊩₁U/;
     module ⊩ₗB)

pattern Σₜ₌ p r pProd prop = p , r , pProd , prop

pattern Uᵣ′ a b = Uᵣ (Uᵣ a b)

mutual
  kit : Nat → LogRelKit
  kit ℓ = LogRel.kit ℓ kit-helper

  kit-helper : {n m : Nat} → m <′ n → LogRelKit
  kit-helper {m = m} ≤′-refl = kit m
  kit-helper (≤′-step p) = kit-helper p


⊩⟨_⟩ : (l : Nat) → Set a
⊩⟨ l ⟩ = ⊩ where open LogRelKit (kit l)

-- Equality of reducibile terms

⊩⟨_⟩∷_/_ : (l : Nat) (A : Term) → ⊩⟨ l ⟩ → Set a
⊩⟨ l ⟩∷ A / [A] = ⊩ A / [A] where open LogRelKit (kit l)

-- Transitivty of term equality.
transEqTerm :  {l : Nat} {A : Term}
              ([A] : ⊩⟨ l ⟩)
            → ⊩⟨ l ⟩∷ A / [A]
            → ⊩⟨ l ⟩∷ A / [A]
            → ⊩⟨ l ⟩∷ A / [A]

transEqTerm (Uᵣ′ l′ (≤′-step s))
            (Uₜ₌ )
            (Uₜ₌ ) =
              lemma (transEqTerm
              (Uᵣ′ l′ s) Uₜ₌ {!!})
            where
              lemma : {A : Term} {l′ n : Nat} {s : l′ <′ n} →
                ⊩⟨ n ⟩∷ A / Uᵣ′ l′ s → ⊩⟨ 1+ n ⟩∷ A / Uᵣ′ l′ (≤′-step s)
              lemma = {!!}
transEqTerm
  (Bᵣ Bᵣ)
  (Σₜ₌ p r ne p~r) = {!!}
