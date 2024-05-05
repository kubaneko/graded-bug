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
open import Definition.Typed R
open import Definition.LogicalRelation R

open import Tools.Nat hiding (_<_)

data Strength : Set where
  𝕤 𝕨 : Strength

data BinderMode : Set where
  BMΠ : BinderMode
  BMΣ : (s : Strength) → BinderMode

data Kind : (ns : List Nat) → Set a where
  Ukind : Nat → Kind []
  Binderkind : (b : BinderMode) (p q : M) → Kind (0 ∷ 1 ∷ [])

data GenTs (A : Nat → Set a) : Nat → List Nat → Set a where
  []  : {n : Nat} → GenTs A n []
  _∷_ : {n b : Nat} {bs : List Nat} (t : A (b + n)) (ts : GenTs A n bs) → GenTs A n (b ∷ bs)

data Term (n : Nat) : Set a where
  var : (x : Fin n) → Term n
  gen : {bs : List Nat} (k : Kind bs) (ts : GenTs Term n bs) → Term n

data Con (A : Nat → Set a) : Nat → Set a where
  ε   :                             Con A 0        -- Empty context.
  _∙_ : {n : Nat} → Con A n → A n → Con A (1+ n)   -- Context extension.

  data _⊢_ (Γ : Con Term n) : Term n → Set ℓ where
    Uⱼ     : ⊢ Γ → Γ ⊢ U l
    ΠΣⱼ    : Γ     ⊢ F
           → Γ ∙ F ⊢ G
           → ΠΣ-allowed b p q
           → Γ     ⊢ ΠΣ⟨ b ⟩ p , q ▷ F ▹ G
    univ   : Γ ⊢ A ∷ U l
           → Γ ⊢ A

data _⊢_⇒*_ (Γ : Con Term n) : Term n → Term n → Set ℓ where
  id  : Γ ⊢ A
      → Γ ⊢ A ⇒* A
  _⇨_ : Γ ⊢ A  ⇒  A′
      → Γ ⊢ A′ ⇒* B
      → Γ ⊢ A  ⇒* B

record _⊢_:⇒*:_ (Γ : Con Term n) (A B : Term n) : Set ℓ where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A
    ⊢B : Γ ⊢ B
    D  : Γ ⊢ A ⇒* B

-- Type levels

TypeLevel : Set
TypeLevel = Nat

_<_ : (i j : TypeLevel) → Set
i < j = i <′ j

data BindingType : Set a where
  BM : BinderMode → (p q : M) → BindingType

pattern BΠ p q = BM BMΠ p q
pattern BΠ! = BΠ _ _
pattern BΣ s p q = BM (BMΣ s) p q
pattern BΣ! = BΣ _ _ _
pattern BΣʷ = BΣ 𝕨 _ _
pattern BΣˢ = BΣ 𝕤 _ _

⟦_⟧_▹_ : BindingType → Term n → Term (1+ n) → Term n
⟦ BΠ p q   ⟧ F ▹ G = Π p , q ▷ F ▹ G
⟦ BΣ m p q ⟧ F ▹ G = Σ⟨ m ⟩ p , q ▷ F ▹ G

data Wk : Nat → Nat → Set where
  id    : {n : Nat}   → Wk n n                    -- η : Γ ≤ Γ.
  step  : {n m : Nat} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : Nat} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

mutual
  wkGen : {m n : Nat} {bs : List Nat} (ρ : Wk m n) (c : GenTs (Term) n bs) → GenTs (Term) m bs
  wkGen ρ []                = []
  wkGen ρ (_∷_ {b = b} t c) = (wk (liftn ρ b) t) ∷ (wkGen ρ c)

  wk : {m n : Nat} (ρ : Wk m n) (t : Term n) → Term m
  wk ρ (var x)   = var (wkVar ρ x)
  wk ρ (gen k c) = gen k (wkGen ρ c)

data _∷_⊇_ : Wk m n → Con Term m → Con Term n → Set a where
  id   :             id     ∷ Γ            ⊇ Γ
  step : ρ ∷ Δ ⊇ Γ → step ρ ∷ Δ ∙ A        ⊇ Γ
  lift : ρ ∷ Δ ⊇ Γ → lift ρ ∷ Δ ∙ U.wk ρ A ⊇ Γ ∙ A

_[_]₀ : (t : Term (1+ n)) (s : Term n) → Term n
t [ s ]₀ = t [ sgSubst s ]


data ⊢_ : Con Term n → Set ℓ where
  ε   : ⊢ ε
  _∙_ : ⊢ Γ
      → Γ ⊢ A
      → ⊢ Γ ∙ A

BindingType-allowed : BindingType → Set a
BindingType-allowed (BM b p q) = ΠΣ-allowed b p q

data Neutral : Term n → Set a where
  var       : (x : Fin n) → Neutral (var x)

data Type {n : Nat} : Term n → Set a where
  ΠΣₙ    :             Type (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B)
  ℕₙ     :             Type ℕ
  Emptyₙ :             Type Empty
  Unitₙ  :             Type (Unit s)
  Idₙ    :             Type (Id A t u)
  ne     : Neutral t → Type t

data Function {n : Nat} : Term n → Set a where
  ne   : Neutral t → Function t

pattern ΠΣ⟨_⟩_,_▷_▹_ b p q F G = gen (Binderkind b p q) (F ∷ G ∷ [])
pattern Π_,_▷_▹_ p q F G = gen (Binderkind BMΠ p q) (F ∷ G ∷ [])
pattern Σˢ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ 𝕤) p q) (F ∷ G ∷ [])
pattern Σʷ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ 𝕨) p q) (F ∷ G ∷ [])
pattern Σ_,_▷_▹_ p q F G = gen (Binderkind (BMΣ _) p q) (F ∷ G ∷ [])
pattern Σ⟨_⟩_,_▷_▹_ s p q F G =
  gen (Binderkind (BMΣ s) p q) (F ∷ G ∷ [])

record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    _⊩U_ : Con Term ℓ → Term ℓ → Set a
    _⊩B⟨_⟩_ : (Γ : Con Term ℓ) (W : BindingType) → Term ℓ → Set a
    -- TODO: Include _⊩ne_ and perhaps more fields here?
    -- _⊩ne_ : Con Term ℓ → Term ℓ → Set a

    _⊩_ : (Γ : Con Term ℓ) → Term ℓ → Set a
    _⊩_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ A → Set a
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
      ⇒*U : Γ ⊢ A :⇒*: U l′

  -- Universe type equality
  _⊩₁U≡_/_ : Con Term ℓ → Term ℓ → TypeLevel → Set a
  Γ ⊩₁U≡ B / l′ = Γ ⊢ B :⇒*: U l′


  -- Universe term
  record _⊩₁U_∷U/_ {l′} (Γ : Con Term ℓ) (t : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U l′
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ U l′
      [t]   : Γ ⊩ t

  -- Universe term equality
  record _⊩₁U_≡_∷U/_ {l′} (Γ : Con Term ℓ) (t u : Term ℓ) (l< : l′ < l) : Set a where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term ℓ
      d     : Γ ⊢ t :⇒*: A ∷ U l′
      d′    : Γ ⊢ u :⇒*: B ∷ U l′
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ U l′
      [t]   : Γ ⊩ t
      [u]   : Γ ⊩ u
      [t≡u] : Γ ⊩ t ≡ u / [t]

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
        G-ext : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ
              → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G [ b ]₀ / [G] [ρ] ⊢Δ [a]
        ok : BindingType-allowed W

    -- B-type equality
    record _⊩ₗB⟨_⟩_≡_/_ (Γ : Con Term ℓ) (W : BindingType) (A B : Term ℓ) ([A] : Γ ⊩ₗB⟨ W ⟩ A) : Set a where
      inductive
      constructor B₌
      eta-equality
      open _⊩ₗB⟨_⟩_ [A]
      field
        F′     : Term ℓ
        G′     : Term (1+ ℓ)
        D′     : Γ ⊢ B ⇒* ⟦ W ⟧ F′ ▹ G′
        A≡B    : Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ F′ ▹ G′
        [F≡F′] : {m : Nat} {ρ : Wk m ℓ} {Δ : Con Term m}
               → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩ₗ U.wk ρ F ≡ U.wk ρ F′ / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a}
               → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
               → Δ ⊩ₗ U.wk (lift ρ) G [ a ]₀ ≡ U.wk (lift ρ) G′ [ a ]₀ / [G] [ρ] ⊢Δ [a]

    -- Term reducibility of Π-type
    _⊩ₗΠ_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_∷_/_ {ℓ} {p} {q} Γ t A (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
            × Function f
            × Γ ⊢ f ≅ f ∷ Π p , q ▷ F ▹ G
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a b}
              ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([b] : Δ ⊩ₗ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              ([a≡b] : Δ ⊩ₗ a ≡ b ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ f ∘⟨ p ⟩ b ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
            × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} → ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
              → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
              {- NOTE(WN): Last 2 fields could be refactored to a single forall.
                           But touching this definition is painful, so only do it
                           if you have to change it anyway. -}
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _⊩ₗΠ_≡_∷_/_ : {ℓ : Nat} {p q : Mod} (Γ : Con Term ℓ) (t u A : Term ℓ) ([A] : Γ ⊩ₗB⟨ BΠ p q ⟩ A) → Set a
    _⊩ₗΠ_≡_∷_/_
      {ℓ} {p} {q} Γ t u A [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃₂ λ f g → Γ ⊢ t :⇒*: f ∷ Π p , q ▷ F ▹ G
               × Γ ⊢ u :⇒*: g ∷ Π p , q ▷ F ▹ G
               × Function f
               × Function g
               × Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G
               × Γ ⊩ₗΠ t ∷ A / [A]
               × Γ ⊩ₗΠ u ∷ A / [A]
               × (∀ {m} {ρ : Wk m ℓ} {Δ : Con Term m} {a} ([ρ] : ρ ∷ Δ ⊇ Γ) (⊢Δ : ⊢ Δ)
                 ([a] : Δ ⊩ₗ a ∷ U.wk ρ F / [F] [ρ] ⊢Δ)
                 → Δ ⊩ₗ U.wk ρ f ∘⟨ p ⟩ a ≡ U.wk ρ g ∘⟨ p ⟩ a ∷ U.wk (lift ρ) G [ a ]₀ / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.


    -- Term reducibility of Σ-type
    _⊩ₗΣ_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_∷_/_
      {p = p} {q = q} {m = m} Γ t A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
      ∃ λ u → Γ ⊢ t :⇒*: u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Γ ⊢ u ≅ u ∷ Σ⟨ m ⟩ p , q ▷ F ▹ G
            × Σ (Product u) λ pProd
            → Σ-prop m u Γ [A] pProd

    Σ-prop : ∀ {A p q} (m : Strength) (t : Term ℓ) → (Γ : Con Term ℓ)
           → ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → (Product t) → Set a
    Σ-prop {p = p} 𝕤 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fst] →
      Γ ⊩ₗ snd p t ∷ U.wk (lift id) G [ fst p t ]₀ /
        [G] id (wf ⊢F) [fst]
    Σ-prop
      {p = p} 𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {p = p′} {t = p₁} {u = p₂} {m = m}) =
           p PE.≡ p′ ×
           Σ (Γ ⊩ₗ p₁ ∷ U.wk id F / [F] id (wf ⊢F)) λ [p₁]
           → Γ ⊩ₗ p₂ ∷ U.wk (lift id) G [ p₁ ]₀ / [G] id (wf ⊢F) [p₁]
           × m PE.≡ 𝕨
    Σ-prop
      {p = p} {q = q}
      𝕨 t Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) =
      Γ ⊢ t ~ t ∷ Σʷ p , q ▷ F ▹ G

    -- Term equality of Σ-type
    _⊩ₗΣ_≡_∷_/_ :
      {p q : Mod} {m : Strength} (Γ : Con Term ℓ) (t u A : Term ℓ)
      ([A] : Γ ⊩ₗB⟨ BΣ m p q ⟩ A) → Set a
    _⊩ₗΣ_≡_∷_/_
      {p = p} {q = q} {m} Γ t u A
      [A]@(Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) =
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
    [Σ]-prop {p = p} 𝕤 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) _ _ =
      Σ (Γ ⊩ₗ fst p t ∷ U.wk id F / [F] id (wf ⊢F)) λ [fstp]
      → Γ ⊩ₗ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ fst p t ≡ fst p r ∷ U.wk id F / [F] id (wf ⊢F)
      × Γ ⊩ₗ snd p t ≡ snd p r ∷ U.wk (lift id) G [ fst p t ]₀
        / [G] id (wf ⊢F) [fstp]
    [Σ]-prop
      {p = p} 𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
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
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
      (prodₙ {t = p₁} {u = p₂}) (ne y) =
      Lift a ⊥
    [Σ]-prop
      𝕨 t r Γ (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext ok)
      (ne x) (prodₙ {t = r₁} {u = r₂}) =
      Lift a ⊥
    [Σ]-prop
      {p = p} {q = q} 𝕨 t r Γ
      (Bᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext _) (ne x) (ne y) =
        Γ ⊢ t ~ r ∷ Σʷ p , q ▷ F ▹ G

    -- Logical relation definition
    data _⊩ₗ_ (Γ : Con Term ℓ) : Term ℓ → Set a where
      Uᵣ  : ∀ {A} → Γ ⊩₁U A → Γ ⊩ₗ A
      ne  : ∀ {A} → Γ ⊩ne⟨ l ⟩ A → Γ ⊩ₗ A
      Bᵣ  : ∀ {A} W → Γ ⊩ₗB⟨ W ⟩ A → Γ ⊩ₗ A

    _⊩ₗ_≡_/_ : (Γ : Con Term ℓ) (A B : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ A ≡ B / Uᵣ (Uᵣ l′ _ _) = Γ ⊩₁U≡ B / l′
    Γ ⊩ₗ A ≡ B / ne neA = Γ ⊩ne⟨ l ⟩ A ≡ B / neA
    Γ ⊩ₗ A ≡ B / Bᵣ W BA = Γ ⊩ₗB⟨ W ⟩ A ≡ B / BA
      where open LogRelKit (rec l<)

    _⊩ₗ_∷_/_ : (Γ : Con Term ℓ) (t A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ∷ A / Uᵣ p = Γ ⊩₁U t ∷U/ _⊩₁U_.l< p
    Γ ⊩ₗ t ∷ A / ne neA = Γ ⊩ne⟨ l ⟩ t ∷ A / neA
    Γ ⊩ₗ t ∷ A / Bᵣ BΠ! ΠA  = Γ ⊩ₗΠ t ∷ A / ΠA
    Γ ⊩ₗ t ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ∷ A / ΣA
      where open LogRelKit (rec l<)

    _⊩ₗ_≡_∷_/_ : (Γ : Con Term ℓ) (t u A : Term ℓ) → Γ ⊩ₗ A → Set a
    Γ ⊩ₗ t ≡ u ∷ A / Uᵣ (Uᵣ l′ l< ⊢Γ) = Γ ⊩₁U t ≡ u ∷U/ l<
    Γ ⊩ₗ t ≡ u ∷ A / ne neA = Γ ⊩ne⟨ l ⟩ t ≡ u ∷ A / neA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΠ! ΠA = Γ ⊩ₗΠ t ≡ u ∷ A / ΠA
    Γ ⊩ₗ t ≡ u ∷ A / Bᵣ BΣ! ΣA  = Γ ⊩ₗΣ t ≡ u ∷ A / ΣA
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩₁U_ _⊩ₗB⟨_⟩_ _⊩ₗId_
              _⊩ₗ_ _⊩ₗ_≡_/_ _⊩ₗ_∷_/_ _⊩ₗ_≡_∷_/_

open LogRel public
  using
    (Uᵣ; ℕᵣ; Emptyᵣ; Unitᵣ; ne; Bᵣ; B₌; Idᵣ; Id₌; emb; Uₜ; Uₜ₌;
     module _⊩₁U_; module _⊩₁U_∷U/_; module _⊩₁U_≡_∷U/_;
     module _⊩ₗB⟨_⟩_; module _⊩ₗB⟨_⟩_≡_/_;
     module _⊩ₗId_; module _⊩ₗId_≡_/_)

mutual
  kit : TypeLevel → LogRelKit
  kit ℓ = LogRel.kit ℓ kit-helper

  kit-helper : {n m : TypeLevel} → m < n → LogRelKit
  kit-helper {m = m} ≤′-refl = kit m
  kit-helper (≤′-step p) = kit-helper p

_⊩⟨_⟩_ : (Γ : Con Term ℓ) (l : TypeLevel) → Term ℓ → Set a
Γ ⊩⟨ l ⟩ A = Γ ⊩ A where open LogRelKit (kit l)

-- Transitivty of term equality.
transEqTerm :  {n : Nat} → ∀ {Γ : Con Term n} {l A t u v}
              ([A] : Γ ⊩⟨ l ⟩ A)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A / [A]

transEqTerm (Uᵣ′ l′ (≤′-step s) D)
            (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u])
            (Uₜ₌ A₁ B₁ d₁ d₁′ typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁) =
              lemma (transEqTerm
              (Uᵣ′ l′ s D) (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u]) {!!})
            where
              lemma : {ℓ : Nat} {Γ : Con Term ℓ} {t v A : Term ℓ} {l′ n : TypeLevel} {D : Γ ⊢ A :⇒*: U l′} {s : l′ < n} →
                Γ ⊩⟨ n ⟩ t ≡ v ∷ A / Uᵣ′ l′ s D → Γ ⊩⟨ Nat.suc n ⟩ t ≡ v ∷ A / Uᵣ′ l′ (≤′-step s) D
              lemma = {!!}
transEqTerm
  (Bᵣ′ (BΣ 𝕨 p′ q) F G D ⊢F ⊢G A≡A [F] [G] G-ext _)
  (Σₜ₌ p r d d′ (ne x) _ p≅r [t] [u] p~r) = {!!}
transEqTerm = {!!}
