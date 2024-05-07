------------------------------------------------------------------------
-- The logical relation for reducibility
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation
  {a} {Mod : Set a}
  {𝕄 : Modality Mod}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped Mod as U hiding (_∷_; K)
open import Definition.Typed.Properties R
open import Definition.Typed R
open import Definition.Typed.Weakening R

open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+; _<′_; ≤′-step; ≤′-refl)
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Unit

private
  variable
    p q : Mod
    ℓ l : Nat
    Γ Δ : Con Term ℓ
    t t′ u u′ : Term _
    ρ : Wk _ _

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.


TypeLevel : Set
TypeLevel = Nat

_<_ : (i j : TypeLevel) → Set
i < j = i <′ j

-- Ordering of type levels.

data _≤_ (l : TypeLevel) : TypeLevel → Set where
  refl : l ≤ l
  emb  : ∀ {l′} → l < l′ → l ≤ l′

record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    _⊩U_ : Con Term ℓ → Term ℓ → Set a
    _⊩B⟨_⟩_ : (Γ : Con Term ℓ) (W : BindingType) → Term ℓ → Set a

    _⊩_ : (Γ : Con Term ℓ) → Term ℓ → Set a
    _⊩_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ A → Set a
    _⊩_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ A → Set a

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ <′ l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩₁U_ (Γ : Con Term ℓ) (A : Term ℓ) : Set a where
    constructor Uᵣ
    field
      l′  : TypeLevel
      l<  : l′ < l


  -- Universe term
  record _⊩₁U_∷U/_ {l′} (Γ : Con Term ℓ) (t : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ
    open LogRelKit (rec l<)

  -- Universe term equality
  record _⊩₁U_≡_∷U/_ {l′} (Γ : Con Term ℓ) (t u : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ₌
    open LogRelKit (rec l<)



  mutual

    -- Reducibility of Binding types (Π, Σ):

    -- B-type
    record _⊩ₗB⟨_⟩_ (Γ : Con Term ℓ) (W : BindingType) (A : Term ℓ) : Set a where
      inductive
      constructor Bᵣ
      eta-equality
      field
        F : Term ℓ
        G : Term (1+ ℓ)
        D : Γ ⊢ A :⇒*: ⟦ W ⟧ F ▹ G
        ⊢F : Γ ⊢ F
        ⊢G : Γ ∙ F ⊢ G
        A≡A : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F ▹ G
        [F] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} → ρ ∷ Δ ⊇ Γ → ⊢ Δ → Δ ⊩ₗ U.wk ρ F
        [G] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a : Term m}
            → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ
            → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀
        ok : BindingType-allowed W

    -- Term reducibility of Σ-type
    _⊩ₗΣ_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_∷_/_
      {p = p} {q = q} {m = m} Γ t A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃ λ u → Γ ⊢ t :⇒*: u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Γ ⊢ u ≅ u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Σ (Product u) λ pProd
            → Σ-prop m u Γ [A] pProd

    Σ-prop : ∀ {A p q} (m : Strength) (t : Term ℓ) → (Γ : Con Term ℓ)
           → ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → (Product t) → Set a
    Σ-prop {p = p} 𝕤 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst] →
      Γ ⊩ₗ snd p t ∷ U.wk (lift id) G [ fst p t ]₀ /
        [G] id (wf ⊢F) [fst]
    Σ-prop
      {p = p} 𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
      (prodₙ {p = p′} {t = p₁} {u = p₂} {m = m}) =
           p PE.≡ p′ ×
           Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁]
           → Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁]
           × m PE.≡ 𝕨
    Σ-prop
      {p = p} {q = q}
      𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne x) =
      Γ ⊢ t ~ t ∷ Σʷ p , q ▷ F ▹ G

    -- Term equality of Σ-type
    _⊩ₗΣ_≡_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t u A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_≡_∷_/_
      {p = p} {q = q} {m} Γ t u A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
      ∃₂ λ t′ u′ → Γ ⊢ t :⇒*: t′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ u :⇒*: u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊢ t′ ≅ u′ ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
                 × Γ ⊩ₗΣ t ∷ A / [A]
                 × Γ ⊩ₗΣ u ∷ A / [A]
                 × Σ (Product t′) λ pProd
                 → Σ (Product u′) λ rProd
                 → [Σ]-prop m t′ u′ Γ [A] pProd rProd

    [Σ]-prop :
      ∀ {A p q} (m : Strength) (t r : Term ℓ) (Γ : Con Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Product t → Product r → Set a
    [Σ]-prop {p = p} 𝕤 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) _ _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
      → Γ ⊩ₗ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ fst p t ≡ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ snd p t ≡ snd p r ∷ U.wk (lift id) G [ fst p t ]₀
        / [G] id (wf ⊢F) [fstp]
    [Σ]-prop
      {p = p} 𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
      (prodₙ {p = p′} {t = p₁} {u = p₂})
      (prodₙ {p = p″} {t = r₁} {u = r₂}) =
             p PE.≡ p′ × p PE.≡ p″ ×
             Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁] →
             Σ (Γ ⊩ₗ r₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [r₁]
             → (Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
             × (Γ ⊩ₗ r₂ ∷ U.wk (lift id) G [ r₁ ]₀ / [G] id (wf ⊢F) [r₁])
             × (Γ ⊩ₗ p₁ ≡ r₁ ∷ U.wk id F / [F] id (wf ⊢F))
             × (Γ ⊩ₗ p₂ ≡ r₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁])
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
      (prodₙ {t = p₁} {u = p₂}) (ne y) =
      Lift a ⊥
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] ok)
      (ne x) (prodₙ {t = r₁} {u = r₂}) =
      Lift a ⊥
    [Σ]-prop
      {p = p} {q = q} 𝕨 t r Γ
      (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] _) (ne x) (ne y) =
        Γ ⊢ t ~ r ∷ Σʷ p , q ▷ F ▹ G

    -- Logical relation definition
    data _⊩ₗ_ (Γ : Con Term ℓ) : Term ℓ → Set a where
      Uᵣ  : ∀ {A} → Γ ⊩₁U A → Γ ⊩ₗ A
      Bᵣ  : ∀ {A} W → Γ ⊩ₗB⟨ W ⟩ A → Γ ⊩ₗ A

    _⊩ₗ_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ∷ A / Uᵣ p = Γ ⊩₁U t ∷U/ _⊩₁U_.l< p
    Γ ⊩ₗ t ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ∷ A / ΣA

    _⊩ₗ_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ≡ u ∷ A / Uᵣ (Uᵣ l′ l<) = Γ ⊩₁U t ≡ u ∷U/ l<
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ≡ u ∷ A / ΣA

    kit : LogRelKit
    kit = Kit _⊩₁U_ _⊩ₗB⟨_⟩_
              _⊩ₗ_ _⊩ₗ_∷_/_ _⊩ₗ_≡_∷_/_

open LogRel public
  using
    (Uᵣ; Bᵣ; Uₜ; Uₜ₌;
     module _⊩₁U_; module _⊩₁U_∷U/_; module _⊩₁U_≡_∷U/_;
     module _⊩ₗB⟨_⟩_)

pattern Σₜ p d p≡p pProd prop =  p , d , p≡p , pProd , prop
pattern Σₜ₌ p r d d′ pProd rProd p≅r [t] [u] prop = p , r , d , d′ , p≅r , [t] , [u] , pProd , rProd , prop

pattern Uᵣ′ a b = Uᵣ (Uᵣ a b)
pattern Bᵣ′ W a b c d e f g h i = Bᵣ W (Bᵣ a b c d e f g h i)
pattern 𝕨′ a b c d e f g h i = Bᵣ′ BΣ! a b c d e f g h i

mutual
  kit : TypeLevel → LogRelKit
  kit ℓ = LogRel.kit ℓ kit-helper

  kit-helper : {n m : TypeLevel} → m < n → LogRelKit
  kit-helper {m = m} ≤′-refl = kit m
  kit-helper (≤′-step p) = kit-helper p


_⊩′⟨_⟩U_ : (Γ : Con Term ℓ) (l : TypeLevel) (A : Term ℓ) → Set a
Γ ⊩′⟨ l ⟩U A = Γ ⊩U A where open LogRelKit (kit l)

_⊩′⟨_⟩B⟨_⟩_ : (Γ : Con Term ℓ) (l : TypeLevel) (W : BindingType) → Term ℓ → Set a
Γ ⊩′⟨ l ⟩B⟨ W ⟩ A = Γ ⊩B⟨ W ⟩ A where open LogRelKit (kit l)

-- Reducibility of types

_⊩⟨_⟩_ : (Γ : Con Term ℓ) (l : TypeLevel) → Term ℓ → Set a
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

-- Equality of reducibile types

_⊩⟨_⟩_∷_/_ : (Γ : Con Term ℓ) (l : TypeLevel) (t A : Term ℓ) → Γ ⊩⟨ l ⟩ A → Set a
Γ ⊩⟨ l ⟩ t ∷ A / [A] = Γ ⊩ t ∷ A / [A] where open LogRelKit (kit l)

-- Equality of reducibile terms

_⊩⟨_⟩_≡_∷_/_ : (Γ : Con Term ℓ) (l : TypeLevel) (t u A : Term ℓ) → Γ ⊩⟨ l ⟩ A → Set a
Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A] = Γ ⊩ t ≡ u ∷ A / [A] where open LogRelKit (kit l)

