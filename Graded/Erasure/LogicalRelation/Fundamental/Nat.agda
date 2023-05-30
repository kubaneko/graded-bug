------------------------------------------------------------------------
-- Graded.Erasure validity of the natural numbers.
------------------------------------------------------------------------

open import Graded.Modality
open import Definition.Typed.EqualityRelation
import Definition.Typed as T
open import Definition.Typed.Restrictions
import Definition.Untyped as U hiding (_∷_)
open import Tools.Nullary
open import Tools.PropositionalEquality

module Graded.Erasure.LogicalRelation.Fundamental.Nat
  {a k} {M : Set a}
  (open U M)
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (R : Type-restrictions M)
  (open T R)
  {Δ : Con Term k} (⊢Δ : ⊢ Δ)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  {{eqrel : EqRelSet R}}
  where


open EqRelSet {{...}}

open import Graded.Erasure.LogicalRelation 𝕄 R ⊢Δ is-𝟘?
open import Graded.Erasure.LogicalRelation.Irrelevance 𝕄 R ⊢Δ is-𝟘?
open import Graded.Erasure.LogicalRelation.Subsumption 𝕄 R ⊢Δ is-𝟘?
import Graded.Erasure.Target as T

open import Definition.Typed.Consequences.Substitution R
open import Definition.Typed.Properties R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Fundamental R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Nat R

open import Graded.Context 𝕄
open import Graded.Mode 𝕄

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    γ : Conₘ n
    Γ : Con Term n
    t t′ : Term n
    v v′ : T.Term n
    p : M
    m : Mode

ℕʳ : ⊢ Γ
   → ∃ λ ([Γ] : ⊩ᵛ Γ)
   → ∃ λ ([U] : Γ ⊩ᵛ⟨ ¹ ⟩ U / [Γ])
   → γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ ℕ ∷[ m ] U / [Γ] / [U]
ℕʳ {m = m} ⊢Γ = [Γ] , [U] , λ _ _ → Uᵣ (ℕⱼ ⊢Δ) ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [U] = Uᵛ [Γ]

zeroʳ : ∀ {l} → ⊢ Γ
      → ∃ λ ([Γ] : ⊩ᵛ Γ)
      → ∃ λ ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
      → γ ▸ Γ ⊩ʳ⟨ l ⟩ zero ∷[ m ] ℕ / [Γ] / [ℕ]
zeroʳ {m = m} ⊢Γ =
    [Γ] , [ℕ]
    , λ _ _ → zeroᵣ (id (zeroⱼ ⊢Δ)) T.refl ◀ ⌜ m ⌝
  where
  [Γ] = valid ⊢Γ
  [ℕ] = ℕᵛ [Γ]

-- successor case of the logical relation for any quantity

sucᵣ′ : ∀ {l}
      → Δ ⊢ t ⇒* U.suc t′ ∷ ℕ
      → v T.⇒* T.suc v′
      → t′ ®⟨ l ⟩ v′ ∷ ℕ ◂ p / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))
      → t ®⟨ l ⟩ v ∷ ℕ ◂ p / ℕᵣ (idRed:*: (ℕⱼ ⊢Δ))
sucᵣ′ {p = p} d d′ t®v with is-𝟘? p
... | yes p≡𝟘 = _
... | no p≢𝟘 = sucᵣ d d′ t®v

sucʳ : ∀ {l}
     → ([Γ] : ⊩ᵛ Γ)
       ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ / [Γ])
       (⊩ʳt : γ ▸ Γ ⊩ʳ⟨ l ⟩ t ∷[ m ] ℕ / [Γ] / [ℕ])
     → Γ ⊢ t ∷ ℕ
     → γ ▸ Γ ⊩ʳ⟨ l ⟩ suc t ∷[ m ] ℕ / [Γ] / [ℕ]
sucʳ {Γ = Γ} {γ = γ} {t = t} {m = m} {l = l}
     [Γ] [ℕ] ⊩ʳt Γ⊢t:ℕ {σ = σ} {σ′ = σ′} [σ] σ®σ′ =
  let [ℕ]′ = ℕᵛ {l = l} [Γ]
      ⊢t:ℕ = substitutionTerm Γ⊢t:ℕ (wellformedSubst [Γ] ⊢Δ [σ]) ⊢Δ
      t®v = ⊩ʳt [σ] σ®σ′
      [σℕ] = proj₁ (unwrap [ℕ] ⊢Δ [σ])
      [σℕ]′ = proj₁ (unwrap [ℕ]′ ⊢Δ [σ])
      t®v∷ℕ = irrelevanceQuant _ [σℕ] [σℕ]′ t®v
      suct®sucv : _ ®⟨ _ ⟩ _ ∷ ℕ ◂ _ / [σℕ]′
      suct®sucv = sucᵣ′ (id (sucⱼ ⊢t:ℕ)) T.refl t®v∷ℕ
  in  irrelevanceQuant ⌜ m ⌝ [σℕ]′ [σℕ] suct®sucv