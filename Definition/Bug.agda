------------------------------------------------------------------------
-- Equality in the logical relation is transitive
------------------------------------------------------------------------

module Definition.Bug
  {a} {M : Set a}
  where

open import Definition.Untyped M
open import Definition.LogicalRelation

open import Tools.Nat hiding (_<_)

-- Transitivty of term equality.
transEqTerm :  {n l : Nat} {A : Term n}
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
              lemma : {ℓ : Nat} {A : Term ℓ} {l′ n : Nat} {s : l′ <′ n} →
                ⊩⟨ n ⟩∷ A / Uᵣ′ l′ s → ⊩⟨ Nat.suc n ⟩∷ A / Uᵣ′ l′ (≤′-step s)
              lemma = {!!}
transEqTerm
  (Bᵣ Bᵣ)
  (Σₜ₌ p r ne p~r) = {!!}
transEqTerm = {!!}
