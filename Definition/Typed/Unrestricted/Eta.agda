------------------------------------------------------------------------
-- Some properties related to typing and the variant of Unrestricted
-- that is defined using a Σ-type with η-equality
------------------------------------------------------------------------

open import Definition.Modality

module Definition.Typed.Unrestricted.Eta
  {a} {M : Set a}
  (𝕄 : Modality M)
  -- A quantity that stands for "an unlimited number of uses".
  (ω : M)
  where

open Modality 𝕄

open import Definition.Typed M
open import Definition.Typed.Consequences.Inequality M
open import Definition.Typed.Consequences.Injectivity M
open import Definition.Typed.Consequences.Inversion M
open import Definition.Typed.Consequences.Substitution M
open import Definition.Typed.Consequences.Syntactic M
open import Definition.Typed.Properties M

open import Definition.Untyped M as U hiding (_∷_; _[_])
open import Definition.Untyped.Unrestricted.Eta 𝕄 ω

open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nullary
open import Tools.Product
import Tools.PropositionalEquality as PE

private variable
  Γ       : Con Term _
  A B t u : Term _

------------------------------------------------------------------------
-- Typing rules

-- A formation rule for Unrestricted.

Unrestrictedⱼ : Γ ⊢ A → Γ ⊢ Unrestricted A
Unrestrictedⱼ ⊢A = ΠΣⱼ ⊢A ▹ Unitⱼ (wf ⊢A ∙ ⊢A)

-- A corresponding congruence rule.

Unrestricted-cong :
  Γ ⊢ A ≡ B →
  Γ ⊢ Unrestricted A ≡ Unrestricted B
Unrestricted-cong A≡B = ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A)))
  where
  ⊢A = syntacticEq A≡B .proj₁

-- An introduction rule for U.

Unrestrictedⱼ-U : Γ ⊢ A ∷ U → Γ ⊢ Unrestricted A ∷ U
Unrestrictedⱼ-U ⊢A∷U = ΠΣⱼ ⊢A∷U ▹ Unitⱼ (wf ⊢A ∙ ⊢A)
  where
  ⊢A = univ ⊢A∷U

-- A corresponding congruence rule.

Unrestricted-cong-U :
  Γ ⊢ A ≡ B ∷ U →
  Γ ⊢ Unrestricted A ≡ Unrestricted B ∷ U
Unrestricted-cong-U A≡B =
  ΠΣ-cong ⊢A A≡B (refl (Unitⱼ (wf ⊢A ∙ ⊢A)))
  where
  ⊢A = univ (syntacticEqTerm A≡B .proj₂ .proj₁)

-- An introduction rule for Unrestricted.

[]ⱼ : Γ ⊢ t ∷ A → Γ ⊢ [ t ] ∷ Unrestricted A
[]ⱼ ⊢t = prodⱼ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A)) ⊢t (starⱼ ⊢Γ)
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- A corresponding congruence rule.

[]-cong :
  Γ ⊢ t ≡ u ∷ A → Γ ⊢ [ t ] ≡ [ u ] ∷ Unrestricted A
[]-cong t≡u =
  prod-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A)) t≡u (refl (starⱼ (wf ⊢A)))
  where
  ⊢A = syntacticEqTerm t≡u .proj₁

-- An elimination rule for Unrestricted.

unboxⱼ : Γ ⊢ t ∷ Unrestricted A → Γ ⊢ unbox t ∷ A
unboxⱼ ⊢t = fstⱼ ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A)) ⊢t
  where
  ⊢A = case syntacticTerm ⊢t of λ where
    (ΠΣⱼ ⊢A ▹ _) → ⊢A
    (univ ⊢E-A)  → univ (inversion-ΠΣ ⊢E-A .proj₁)

-- A corresponding congruence rule.

unbox-cong : Γ ⊢ t ≡ u ∷ Unrestricted A → Γ ⊢ unbox t ≡ unbox u ∷ A
unbox-cong t≡u = fst-cong ⊢A (Unitⱼ (wf ⊢A ∙ ⊢A)) t≡u
  where
  ⊢A = case syntacticEqTerm t≡u .proj₁ of λ where
    (ΠΣⱼ ⊢A ▹ _) → ⊢A
    (univ ⊢E-A)  → univ (inversion-ΠΣ ⊢E-A .proj₁)

-- A β-rule for Unrestricted.

Unrestricted-β :
  Γ ⊢ t ∷ A →
  Γ ⊢ unbox [ t ] ≡ t ∷ A
Unrestricted-β ⊢t = Σ-β₁ ⊢A (Unitⱼ (⊢Γ ∙ ⊢A)) ⊢t (starⱼ ⊢Γ) PE.refl
  where
  ⊢A = syntacticTerm ⊢t
  ⊢Γ = wf ⊢A

-- An η-rule for Unrestricted.

Unrestricted-η :
  Γ ⊢ t ∷ Unrestricted A →
  Γ ⊢ u ∷ Unrestricted A →
  Γ ⊢ unbox t ≡ unbox u ∷ A →
  Γ ⊢ t ≡ u ∷ Unrestricted A
Unrestricted-η ⊢t ⊢u t≡u = Σ-η
  ⊢A Γ∙A⊢Unit ⊢t ⊢u t≡u
  (η-unit (sndⱼ ⊢A Γ∙A⊢Unit ⊢t) (sndⱼ ⊢A Γ∙A⊢Unit ⊢u))
  where
  ⊢A       = syntacticEqTerm t≡u .proj₁
  Γ∙A⊢Unit = Unitⱼ (wf ⊢A ∙ ⊢A)

-- An instance of the η-rule.

[unbox] :
  Γ ⊢ t ∷ Unrestricted A →
  Γ ⊢ [ unbox t ] ≡ t ∷ Unrestricted A
[unbox] ⊢t =
  Unrestricted-η ([]ⱼ (unboxⱼ ⊢t)) ⊢t $
  Unrestricted-β (unboxⱼ ⊢t)

------------------------------------------------------------------------
-- Inversion lemmas for typing

-- An inversion lemma for Unrestricted.

inversion-Unrestricted-∷ :
  Γ ⊢ Unrestricted A ∷ B →
  Γ ⊢ A ∷ U × Γ ⊢ B ≡ U
inversion-Unrestricted-∷ ⊢Unrestricted =
  case inversion-ΠΣ ⊢Unrestricted of λ (⊢A , _ , B≡) →
  ⊢A , B≡

-- Another inversion lemma for Unrestricted.

inversion-Unrestricted : Γ ⊢ Unrestricted A → Γ ⊢ A
inversion-Unrestricted (ΠΣⱼ ⊢A ▹ _)   = ⊢A
inversion-Unrestricted (univ ⊢Unrestricted) =
  univ (inversion-Unrestricted-∷ ⊢Unrestricted .proj₁)

-- An inversion lemma for [_].
--
-- TODO: Make it possible to replace the conclusion with
--
--   ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Unrestricted B?

inversion-[] :
  Γ ⊢ [ t ] ∷ A →
  ∃₃ λ B q C →
     Γ ⊢ t ∷ B ×
     Γ ⊢ A ≡ Σₚ ω , q ▷ B ▹ C ×
     Γ ⊢ C U.[ t ] ≡ Unit
inversion-[] ⊢[] =
  case inversion-prod ⊢[] of
    λ (B , C , q , ⊢B , _ , ⊢t , ⊢star , A≡) →
  case inversion-star ⊢star of λ ≡Unit →
    B , q , C , ⊢t , A≡ , ≡Unit

-- Another inversion lemma for [_].

inversion-[]′ : Γ ⊢ [ t ] ∷ Unrestricted A → Γ ⊢ t ∷ A
inversion-[]′ ⊢[] =
  case inversion-[] ⊢[] of
    λ (_ , _ , _ , ⊢t , Unrestricted-A≡ , _) →
  case Σ-injectivity Unrestricted-A≡ of
    λ (A≡ , _) →
  conv ⊢t (_⊢_≡_.sym A≡)

-- A certain form of inversion for [_] does not hold.

¬-inversion-[]′ :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ [ t ] ∷ A →
     ∃₂ λ B q → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Σₚ ω , q ▷ B ▹ Unit)
¬-inversion-[]′ inversion-[] = bad
  where
  Γ′ = ε
  t′ = zero
  A′ = Σₚ ω , 𝟙 ▷ ℕ ▹ natrec 𝟙 𝟙 𝟙 U Unit ℕ (var x0)

  ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
  ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

  ⊢Γ′∙ℕ∙ℕ : ⊢ Γ′ ∙ ℕ ∙ ℕ
  ⊢Γ′∙ℕ∙ℕ = ⊢Γ′∙ℕ ∙ ℕⱼ ⊢Γ′∙ℕ

  ⊢Γ′∙ℕ∙U : ⊢ Γ′ ∙ ℕ ∙ U
  ⊢Γ′∙ℕ∙U = ⊢Γ′∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ

  ⊢[t′] : Γ′ ⊢ [ t′ ] ∷ A′
  ⊢[t′] = prodⱼ
    (ℕⱼ ε)
    (univ (natrecⱼ
             (Uⱼ ⊢Γ′∙ℕ∙ℕ)
             (Unitⱼ ⊢Γ′∙ℕ)
             (ℕⱼ (⊢Γ′∙ℕ∙ℕ ∙ Uⱼ ⊢Γ′∙ℕ∙ℕ))
             (var ⊢Γ′∙ℕ here)))
    (zeroⱼ ε)
    (conv (starⱼ ε)
       (_⊢_≡_.sym $
        univ (natrec-zero (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε) (ℕⱼ ⊢Γ′∙ℕ∙U))))

  ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
  ℕ≡Unit =
    case inversion-[] ⊢[t′] of
      λ (_ , _ , _ , A′≡) →
    case Σ-injectivity A′≡ of
      λ (_ , ≡Unit , _ , _ , _) →
    trans
      (_⊢_≡_.sym $
       univ (natrec-suc (zeroⱼ ε) (Uⱼ ⊢Γ′∙ℕ) (Unitⱼ ε) (ℕⱼ ⊢Γ′∙ℕ∙U)))
      (substTypeEq ≡Unit (refl (sucⱼ (zeroⱼ ε))))

  bad : ⊥
  bad = ℕ≢Unitⱼ ℕ≡Unit

-- Another form of inversion for [] also does not hold.

¬-inversion-[] :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ [ t ] ∷ A →
     ∃ λ B → Γ ⊢ t ∷ B × Γ ⊢ A ≡ Unrestricted B)
¬-inversion-[] inversion-[] =
  ¬-inversion-[]′ λ ⊢[] →
  case inversion-[] ⊢[] of λ (B , ⊢t , A≡) →
  B , ω , ⊢t , A≡

-- An inversion lemma for unbox.
--
-- TODO: Make it possible to replace the conclusion with
--
--   Γ ⊢ t ∷ Unrestricted A?

inversion-unbox :
  Γ ⊢ unbox t ∷ A →
  ∃₂ λ q B → Γ ⊢ t ∷ Σₚ ω , q ▷ A ▹ B
inversion-unbox ⊢unbox =
  case inversion-fst ⊢unbox of λ (_ , C , q , ⊢B , ⊢C , ⊢t , ≡B) →
  q , C , conv ⊢t (ΠΣ-cong ⊢B (_⊢_≡_.sym ≡B) (refl ⊢C))

-- A certain form of inversion for unbox does not hold.

¬-inversion-unbox′ :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ unbox t ∷ A →
     ∃ λ q → Γ ⊢ t ∷ Σₚ ω , q ▷ A ▹ Unit)
¬-inversion-unbox′ inversion-unbox = bad
  where
  Γ′ = ε
  t′ = prodₚ ω zero zero
  A′ = ℕ

  ⊢Γ′∙ℕ : ⊢ Γ′ ∙ ℕ
  ⊢Γ′∙ℕ = ε ∙ ℕⱼ ε

  ⊢t′₁ : Γ′ ⊢ t′ ∷ Σ ω , 𝟙 ▷ ℕ ▹ ℕ
  ⊢t′₁ = prodⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε)

  ⊢unbox-t′ : Γ′ ⊢ unbox t′ ∷ A′
  ⊢unbox-t′ = fstⱼ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) ⊢t′₁

  unbox-t′≡zero : Γ′ ⊢ unbox t′ ≡ zero ∷ A′
  unbox-t′≡zero = Σ-β₁ (ℕⱼ ε) (ℕⱼ ⊢Γ′∙ℕ) (zeroⱼ ε) (zeroⱼ ε) PE.refl

  ⊢t′₂ : ∃ λ q → Γ′ ⊢ t′ ∷ Σₚ ω , q ▷ A′ ▹ Unit
  ⊢t′₂ = inversion-unbox ⊢unbox-t′

  ⊢snd-t′ : Γ′ ⊢ snd ω t′ ∷ Unit
  ⊢snd-t′ = sndⱼ (ℕⱼ ε) (Unitⱼ ⊢Γ′∙ℕ) (⊢t′₂ .proj₂)

  ℕ≡Unit : Γ′ ⊢ ℕ ≡ Unit
  ℕ≡Unit =
    case inversion-snd ⊢snd-t′ of
      λ (_ , _ , _ , _ , _ , ⊢t′ , Unit≡) →
    case inversion-prod ⊢t′ of
      λ (_ , _ , _ , _ , _ , ⊢zero , ⊢zero′ , Σ≡Σ) →
    case Σ-injectivity Σ≡Σ of
      λ (F≡F′ , G≡G′ , _ , _ , _) →
    case inversion-zero ⊢zero of
      λ ≡ℕ →
    case inversion-zero ⊢zero′ of
      λ ≡ℕ′ →
    _⊢_≡_.sym $
    _⊢_≡_.trans Unit≡ $
    trans
      (substTypeEq G≡G′ $
       conv unbox-t′≡zero (_⊢_≡_.sym (trans F≡F′ ≡ℕ)))
    ≡ℕ′

  bad : ⊥
  bad = ℕ≢Unitⱼ ℕ≡Unit

-- Another form of inversion for unbox also does not hold.

¬-inversion-unbox :
  ¬ (∀ {n} {Γ : Con Term n} {t A : Term n} →
     Γ ⊢ unbox t ∷ A →
     Γ ⊢ t ∷ Unrestricted A)
¬-inversion-unbox inversion-unbox =
  ¬-inversion-unbox′ λ ⊢unbox →
  _ , inversion-unbox ⊢unbox