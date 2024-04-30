------------------------------------------------------------------------
-- Lemmata relating to terms of the universe type
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Properties.Escape R
open import Definition.LogicalRelation.Properties.Cumulativity R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Nat hiding (_<_; _≤_)
open import Tools.Product

private
  variable
    n l′ : Nat
    Γ : Con Term n

-- Helper function for reducible terms of type U for specific type derivations.
univEq′ :
  ∀ {l l′ t A} ([U] : Γ ⊩⟨ l ⟩U A) → Γ ⊩⟨ l ⟩ t ∷ A / U-intr [U] →
  ∃ λ l″ → l″ ≤ l′ → Γ ⊩⟨ l″ ⟩ A
univEq′ (noemb (Uᵣ l l< ⊢Γ)) (Uₜ A₁ d typeA A≡A [A]) = l , (λ x → Uᵣ′ {!!} {!!} {!!})
univEq′ (emb ≤′-refl x) [A] = univEq′ x [A]
univEq′ (emb (≤′-step l<) x) [A] = univEq′ (emb l< x) [A]

-- Reducible terms of type U are reducible types.
univEq :
  ∀ {l t A} ([U] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / [U] →
  ∃ λ l″ → l″ ≤ l′ → Γ ⊩⟨ l″ ⟩ t
univEq [U] [A] = univEq′ {!U-elim ? [U]!} {!irrelevanceTerm [U] (U-intr (U-elim [U])) [A]!}

-- univEq′ (U-elim [U])
--                          (irrelevanceTerm [U] (U-intr (U-elim [U])) [A])

-- Helper function for reducible term equality of type U for specific type derivations.
univEqEq′ : ∀ {l l′ A B} ([U] : Γ ⊩⟨ l ⟩U (U l′)) ([A] : Γ ⊩⟨ l′ ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ (U l′) / U-intr [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B / [A]
univEqEq′ (noemb (Uᵣ l′ l< ⇒*U)) [A] (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =  irrelevanceEq {![t]!} [A] [t≡u]
univEqEq′ (emb x [U]) [t] t≡v = univEqEq′ {!x!} {!!} {!!}
-- univEqEq′ (noemb (Uᵣ 0 l< ⊢Γ)) [t]
--           (Uₜ₌ A₁ B₁ d d′ typeA typeB A≡B [t] [u] [t≡u]) =
--   irrelevanceEq [t] [A] [t≡u]
-- univEqEq′ (emb 0<1 x) [A] [A≡B] = univEqEq′ x [A] [A≡B]

-- Reducible term equality of type U is reducible type equality.
univEqEq : ∀ {l l′ t v} ([U] : Γ ⊩⟨ l ⟩ (U l′)) ([t] : Γ ⊩⟨ l′ ⟩ t)
         → Γ ⊩⟨ l ⟩ t ≡ v ∷ (U l′) / [U]
         → Γ ⊩⟨ l′ ⟩ t ≡ v / [t]
univEqEq [U] [t] [t≡v] =
  let [U]′ = U-elim (id (escape [U])) [U]
      [t≡v]′ = irrelevanceEqTerm [U] (U-intr [U]′) [t≡v]
  in univEqEq′ [U]′ [t] [t≡v]′
