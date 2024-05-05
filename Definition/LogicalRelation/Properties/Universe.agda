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
  ∀ {l l′ A} ([U] : Γ ⊩⟨ l ⟩U U l′) → Γ ⊩⟨ l ⟩ A ∷ U l′ / U-intr [U] → Γ ⊩⟨ l′ ⟩ A
univEq′ (noemb (Uᵣ l′ l< D)) (Uₜ A d typeA A≡A [t]) = {!!}
univEq′ (emb ≤′-refl [U]) [A] = univEq′ [U] [A]
univEq′ (emb (≤′-step x) [U]) [A] = univEq′ (emb x [U]) [A]

-- Reducible terms of type U are reducible types.
univEq :
  ∀ {l l′ t A} ([U] : Γ ⊩⟨ l ⟩ U l′) → Γ ⊩⟨ l ⟩ t ∷ U l′ / [U] → Γ ⊩⟨ l′ ⟩ t
univEq [U] [A] =
  let Uel = U-elim (id (escape [U])) [U]
  in univEq′ Uel (irrelevanceTerm [U] (U-intr Uel) [A])

-- Helper function for reducible term equality of type U for specific type derivations.
univEqEq′ : ∀ {l l′ A B} ([U] : Γ ⊩⟨ l ⟩U (U l′)) ([A] : Γ ⊩⟨ l′ ⟩ A)
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ (U l′) / U-intr [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B / [A]
univEqEq′ (noemb (Uᵣ l′ ≤′-refl ⇒*U)) [A] (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  irrelevanceEq (helperToLogRel ≤′-refl [t]) [A] [t≡u]
univEqEq′ (noemb (Uᵣ l′ (≤′-step l<) ⇒*U)) [A] (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  univEqEq′ (noemb (Uᵣ l′ l< ⇒*U)) [A] (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u])
                     --
univEqEq′ (emb ≤′-refl [U]) [A] A≡B = univEqEq′ [U] [A] A≡B
univEqEq′ (emb (≤′-step x) [U]) [A] A≡B = univEqEq′ (emb x [U]) [A] A≡B

-- Reducible term equality of type U is reducible type equality.
univEqEq : ∀ {l l′ t v} ([U] : Γ ⊩⟨ l ⟩ (U l′)) ([t] : Γ ⊩⟨ l′ ⟩ t)
         → Γ ⊩⟨ l ⟩ t ≡ v ∷ (U l′) / [U]
         → Γ ⊩⟨ l′ ⟩ t ≡ v / [t]
univEqEq [U] [t] [t≡v] =
  let [U]′ = U-elim (id (escape [U])) [U]
      [t≡v]′ = irrelevanceEqTerm [U] (U-intr [U]′) [t≡v]
  in univEqEq′ [U]′ [t] [t≡v]′
