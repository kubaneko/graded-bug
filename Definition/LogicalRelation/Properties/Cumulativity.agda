------------------------------------------------------------------------
-- Escaping the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Cumulativity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (_∷_; K)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Reflexivity R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat hiding (_<_)
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
    l : TypeLevel
    b : BinderMode
    s : Strength
    p q : M

mutual
  -- Well-formness is cumulative
  cumul : ∀ {l l′ A} → l < l′ → Γ ⊩⟨ l ⟩ A →  Γ ⊩⟨ l′ ⟩ A
  cumul ≤′-refl ⊩Ty = cumulStep ⊩Ty
  cumul (≤′-step l<) ⊩Ty = cumulStep (cumul l< ⊩Ty)

  cumulStep : ∀ {l A} → Γ ⊩⟨ l ⟩ A →  Γ ⊩⟨ 1+ l ⟩ A
  cumulStep (Uᵣ′ l′ l< ⇒*U) = Uᵣ′ l′ (≤′-step l<) ⇒*U
  cumulStep (ℕᵣ x) =  ℕᵣ x
  cumulStep (Emptyᵣ x) =  Emptyᵣ x
  cumulStep (Unitᵣ x) =  Unitᵣ x
  cumulStep (ne′ K D neK K≡K) = ne′ K D neK K≡K
  cumulStep (Bᵣ′ W F G D ⊢F ⊢G A≡A [F] [G] G-ext ok) =  (Bᵣ′ W F G D ⊢F ⊢G A≡A (λ x x₁ → {!!}) {!!} G-ext ok)
  cumulStep (Idᵣ (Idᵣ Ty lhs rhs ⇒*Id ⊩Ty ⊩lhs ⊩rhs)) =  Idᵣ
          (Idᵣ Ty lhs rhs ⇒*Id (cumul ≤′-refl ⊩Ty) (cumulTerm ≤′-refl  ⊩Ty ⊩lhs) (cumulTerm ≤′-refl  ⊩Ty ⊩rhs))
  cumulStep (emb l< [A]) = emb (≤′-step l<) [A]

  cumulTerm : ∀ {l l′ A t} → (l< : l < l′) → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ∷ A / [A]
                → Γ ⊩⟨ l′ ⟩ t ∷ A / cumul l< [A]
  cumulTerm ≤′-refl ⊩Ty ⊩Tm = cumulTermStep ⊩Ty ⊩Tm 
  cumulTerm (≤′-step l<) ⊩Ty ⊩Tm = cumulTermStep (cumul l< ⊩Ty) (cumulTerm l< ⊩Ty ⊩Tm)

  cumulTermStep : ∀ {l A t} → ([A] : Γ ⊩⟨ l ⟩ A)
                → Γ ⊩⟨ l ⟩ t ∷ A / [A]
                → Γ ⊩⟨ 1+ l ⟩ t ∷ A / cumulStep [A]
  cumulTermStep (Uᵣ x) (Uₜ A d typeA A≡A [t]) = Uₜ A d typeA A≡A [t]
  cumulTermStep (ℕᵣ x) ⊩Tm = ⊩Tm
  cumulTermStep (Emptyᵣ x) ⊩Tm = ⊩Tm
  cumulTermStep (Unitᵣ x) ⊩Tm = ⊩Tm
  cumulTermStep (ne x) (neₜ k d nf) = neₜ k d nf
  cumulTermStep (Bᵣ W x) k = {!!}
  cumulTermStep (Idᵣ x) (fst₁ , snd₁) =  fst₁ , {!!}
  cumulTermStep (emb l< [A]) k = k

  cumulEq :
    ∀ {l l′ A B} → (l< : l < l′) →
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l′ ⟩ A ≡ B / (cumul l< ⊩A)
  cumulEq ≤′-refl ⊩A eq = cumulEqStep ⊩A eq
  cumulEq (≤′-step l<) ⊩A eq = cumulEqStep (cumul l< ⊩A) (cumulEq l< ⊩A eq)

  cumulEqStep : ∀ {l A B} → (⊩A : Γ ⊩⟨ l ⟩ A) →
                  Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
                  Γ ⊩⟨ 1+ l ⟩ A ≡ B / cumulStep ⊩A
  cumulEqStep (Uᵣ x) eq = eq
  cumulEqStep (ℕᵣ x) eq = eq
  cumulEqStep (Emptyᵣ x) eq = eq
  cumulEqStep (Unitᵣ x) eq = eq
  cumulEqStep (ne x) (ne₌ M D′ neM K≡M) = ne₌ M D′ neM K≡M
  cumulEqStep (Bᵣ W x) (B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) = B₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
  cumulEqStep (Idᵣ x) (Id₌ Ty′ lhs′ rhs′ ⇒*Id′ Ty≡Ty′ lhs≡lhs′ rhs≡rhs′ lhs≡rhs→lhs′≡rhs′ lhs′≡rhs′→lhs≡rhs) =
    Id₌ Ty′ lhs′ rhs′ ⇒*Id′ (cumulEq ≤′-refl {!!} Ty≡Ty′) (cumulTermEq ≤′-refl {!!} lhs≡lhs′)
    (cumulTermEq ≤′-refl {!!} rhs≡rhs′) (λ x1 →  cumulEqStep {!!} (lhs≡rhs→lhs′≡rhs′ {!!})) λ x1 → cumulEqStep {!!} (lhs′≡rhs′→lhs≡rhs {!!})
  cumulEqStep (emb l< [A]) eq = eq

  cumulTermEq :
      ∀ {l l′ A t u} → (l< : l < l′) →
      (⊩A : Γ ⊩⟨ l ⟩ A) →
      Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
      Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / cumul l< ⊩A
  cumulTermEq ≤′-refl ⊩A teq = cumulTermEqStep ⊩A teq
  cumulTermEq (≤′-step l<) ⊩A teq = cumulTermEqStep (cumul l< ⊩A) (cumulTermEq l< ⊩A teq)

  cumulTermEqStep : ∀ {l A t u} → (⊩A : Γ ⊩⟨ l ⟩ A) →
                  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
                  Γ ⊩⟨ 1+ l ⟩ t ≡ u ∷ A / cumulStep ⊩A
  cumulTermEqStep (Uᵣ x) (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) = Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]
  cumulTermEqStep (ℕᵣ x) teq = teq
  cumulTermEqStep (Emptyᵣ x) teq = teq
  cumulTermEqStep (Unitᵣ x) teq = teq
  cumulTermEqStep (ne x) (neₜ₌ k m d d′ nf) = neₜ₌ k m d d′ nf
  cumulTermEqStep (Bᵣ W x) teq = {!!}
  cumulTermEqStep (Idᵣ x) teq = {!!}
  cumulTermEqStep (emb l< [A]) teq = teq
