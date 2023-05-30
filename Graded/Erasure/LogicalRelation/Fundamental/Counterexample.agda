------------------------------------------------------------------------
-- The fundamental lemma does not hold in general without the
-- assumption that erased matches are disallowed or the context is
-- empty
------------------------------------------------------------------------

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Tools.Nullary
open import Tools.PropositionalEquality as PE

module Graded.Erasure.LogicalRelation.Fundamental.Counterexample
  {a} {M : Set a}
  (𝕄 : Modality M)
  (open Modality 𝕄)
  (TR : Type-restrictions M)
  (open Type-restrictions TR)
  (UR : Usage-restrictions M)
  (open Usage-restrictions UR)
  (is-𝟘? : (p : M) → Dec (p ≡ 𝟘))
  (𝟙≉𝟘 : 𝟙 ≢ 𝟘)
  -- Erased matches is allowed
  (P₀₁₀ : Prodrec-restriction 𝟘 𝟙 𝟘)
  (Σᵣ-𝟙-𝟘 : Σᵣ-restriction 𝟙 𝟘)
  {{eqrel : EqRelSet TR}}
  where

open EqRelSet {{...}}

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Modality.Properties.PartialOrder
  semiring-with-meet
open import Graded.Usage 𝕄 UR
open import Graded.Mode 𝕄

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed TR
open import Definition.Typed.Properties TR
open import Definition.LogicalRelation TR
open import Definition.LogicalRelation.Substitution TR
open import Definition.LogicalRelation.Substitution.Properties TR
import Definition.LogicalRelation.Substitution.Irrelevance TR as IS

Δ : Con Term 1
Δ = ε ∙ (Σᵣ 𝟙 , 𝟘 ▷ ℕ ▹ ℕ)

⊢Δ : ⊢ Δ
⊢Δ = ε ∙ ΠΣⱼ (ℕⱼ ε) (ℕⱼ (ε ∙ ℕⱼ ε)) Σᵣ-𝟙-𝟘

import Graded.Erasure.Target as T
open import Graded.Erasure.LogicalRelation 𝕄 TR ⊢Δ is-𝟘?
open import Graded.Erasure.LogicalRelation.Irrelevance 𝕄 TR ⊢Δ is-𝟘?
open import Graded.Erasure.LogicalRelation.Subsumption 𝕄 TR ⊢Δ is-𝟘?

open import Tools.Fin
open import Tools.Product

cEx″ : ∀ {v} → prodrec 𝟘 𝟙 𝟘 ℕ (var x0) zero ® v ∷ℕ → ⊥
cEx″ (zeroᵣ x x₁) with whnfRed*Term x (ne (prodrecₙ (var x0)))
... | ()
cEx″ (sucᵣ x x₁ t®v) with whnfRed*Term x (ne (prodrecₙ (var x0)))
... | ()

cEx′ :
  ([Δ] : ⊩ᵛ Δ)
  ([A] : Δ ⊩ᵛ⟨ ¹ ⟩ ℕ / [Δ]) →
  ε ∙ 𝟘 ▸ Δ ⊩ʳ⟨ ¹ ⟩ prodrec 𝟘 𝟙 𝟘 ℕ (var x0) zero
    ∷[ 𝟙ᵐ ] ℕ / [Δ] / [A] →
  ⊥
cEx′ [Δ] [A] ⊩ʳpr =
  let [σ]′ = idSubstS [Δ]
      ⊢Δ′ = soundContext [Δ]
      [σ] = IS.irrelevanceSubst [Δ] [Δ] ⊢Δ′ ⊢Δ [σ]′
      σ®σ′ = erasedSubst {l = ¹} {σ′ = T.idSubst} [Δ] [σ]
      pr®pr = ⊩ʳpr [σ] σ®σ′
      [σA] = proj₁ (unwrap [A] ⊢Δ [σ])
      [ℕ] = ℕᵣ {l = ¹} (idRed:*: (ℕⱼ ⊢Δ))
      pr®pr′ = irrelevanceTerm [σA] [ℕ] (pr®pr ◀≢𝟘 𝟙≉𝟘)
  in  cEx″ pr®pr′

-- The fundamental lemma does not hold if erased matches are allowed

cEx : ∃ λ n
    → ∃₄ λ (t A : Term n) (Γ : Con Term n) (γ : Conₘ n)
    → Γ ⊢ t ∷ A
    × γ ▸[ 𝟙ᵐ ] t
    × ((∃₂ λ ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ ¹ ⟩ A / [Γ]) →
        γ ▸ Γ ⊩ʳ⟨ ¹ ⟩ t ∷[ 𝟙ᵐ ] A / [Γ] / [A]) →
       ⊥)
cEx = _
    , prodrec 𝟘 𝟙 𝟘 ℕ (var x0) zero , ℕ , ε ∙ (Σᵣ 𝟙 , 𝟘 ▷ ℕ ▹ ℕ)
    , ε ∙ 𝟘
    , prodrecⱼ Δ⊢ℕ Δℕ⊢ℕ ΔΣ⊢ℕ (var ⊢Δ here) (zeroⱼ ⊢Δℕℕ) Σᵣ-𝟙-𝟘
    , sub ▸pr (≤ᶜ-reflexive (≈ᶜ-refl ∙ PE.sym (PE.trans (+-identityʳ _) (·-zeroˡ _))))
    , λ {([Γ] , [A] , ⊩ʳpr) → cEx′ [Γ] [A] ⊩ʳpr}
    where
    Δ⊢ℕ = ℕⱼ ⊢Δ
    ⊢Δℕ = ⊢Δ ∙ Δ⊢ℕ
    Δℕ⊢ℕ = ℕⱼ ⊢Δℕ
    Δ⊢Σ = ΠΣⱼ Δ⊢ℕ Δℕ⊢ℕ Σᵣ-𝟙-𝟘
    ⊢ΔΣ = ⊢Δ ∙ Δ⊢Σ
    ΔΣ⊢ℕ = ℕⱼ ⊢ΔΣ
    ⊢Δℕℕ = ⊢Δ ∙ Δ⊢ℕ ∙ Δℕ⊢ℕ
    ▸zero = sub zeroₘ (≤ᶜ-reflexive (≈ᶜ-refl ∙ PE.trans (·-congˡ (·-zeroˡ 𝟙)) (·-zeroʳ 𝟙) ∙ ·-zeroʳ _))
    ▸ℕ = sub ℕₘ (≤ᶜ-refl ∙ ≤-reflexive (·-zeroʳ _))
    ▸pr = prodrecₘ {η = 𝟘ᶜ} var ▸zero ▸ℕ P₀₁₀