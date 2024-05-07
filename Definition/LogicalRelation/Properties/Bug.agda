------------------------------------------------------------------------
-- Equality in the logical relation is transitive
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Bug
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.LogicalRelation R

open import Tools.Nat hiding (_<_)

-- Transitivty of term equality.
transEqTerm :  {n : Nat} → ∀ {Γ : Con Term n} {l A t u v}
              ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]

transEqTerm (Uᵣ′ l′ (≤′-step s))
            (Uₜ₌ )
            (Uₜ₌ ) =
              lemma (transEqTerm
              (Uᵣ′ l′ s) Uₜ₌ {!!})
            where
              lemma : {ℓ : Nat} {Γ : Con Term ℓ} {t v A : Term ℓ} {l′ n : TypeLevel} {s : l′ < n} →
                Γ ⊩⟨ n ⟩ t ≡ v ∷ A / Uᵣ′ l′ s → Γ ⊩⟨ Nat.suc n ⟩ t ≡ v ∷ A / Uᵣ′ l′ (≤′-step s)
              lemma = {!!}
transEqTerm
  (Bᵣ′ (BΣ 𝕨 p′ q) F G D ⊢F ⊢G A≡A [F] [G] _)
  (Σₜ₌ p r d d′ (ne x) _ p≅r [t] [u] p~r) = {!!}
transEqTerm = {!!}
