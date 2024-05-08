------------------------------------------------------------------------
-- The logical relation for reducibility
------------------------------------------------------------------------

module Definition.LogicalRelation
  {a} {Mod : Set a}
  where

open import Definition.Untyped Mod as U

open import Tools.Level using (lsuc)
open import Tools.Nat using (Nat; 1+; _<′_; ≤′-step; ≤′-refl)
open import Tools.Product using (Σ; ∃₂; _,_)




private
  variable
    ℓ l : Nat
    t t′ u u′ : Term _

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.



-- Ordering of type levels.

record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    ⊩U : Set a
    ⊩B : Set a

    ⊩ : Set a
    ⊩_/_ : (A : Term ℓ) → ⊩ → Set a

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



  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record ⊩ₗB : Set a where
      constructor Bᵣ
      eta-equality

    record ⊤₂ : Set a where
      instance constructor tt₂

    -- Term equality of Σ-type
    ⊩ₗΣ_/_ :
      {ℓ : Nat} (A : Term ℓ)
      ([A] : ⊩ₗB) → Set a
    ⊩ₗΣ_/_
      {ℓ} A
      Bᵣ =
      ∃₂ λ (t′ u′ : Term ℓ) →
                 Σ (Product t′) λ pProd
                 → ⊤₂

    -- Logical relation definition
    data ⊩ₗ : Set a where
      Uᵣ  : ⊩₁U → ⊩ₗ
      Bᵣ  : ⊩ₗB → ⊩ₗ

    ⊩ₗ_/_ : (A : Term ℓ) → ⊩ₗ → Set a
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


⊩′⟨_⟩U : (l : Nat) → Set a
⊩′⟨ l ⟩U = ⊩U where open LogRelKit (kit l)

⊩′⟨_⟩B : (l : Nat) → Set a
⊩′⟨ l ⟩B = ⊩B where open LogRelKit (kit l)

-- Reducibility of types

⊩⟨_⟩ : (l : Nat) → Set a
⊩⟨ l ⟩ = ⊩ where open LogRelKit (kit l)

-- Equality of reducibile terms

⊩⟨_⟩∷_/_ : (l : Nat) (A : Term ℓ) → ⊩⟨ l ⟩ → Set a
⊩⟨ l ⟩∷ A / [A] = ⊩ A / [A] where open LogRelKit (kit l)
