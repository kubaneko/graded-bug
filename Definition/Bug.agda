module Definition.Bug
  {a} {M : Set a}
  where

open import Agda.Primitive using (lsuc; _⊔_)

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

infixr 4 _,_

data Nat : Set where
  zero : Nat
  1+_  : (n : Nat) → Nat

data _≤′_ (m : Nat) : Nat → Set where
  ≤′-refl :                         m ≤′ m
  ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ (1+ n)

_<′_ : (m n : Nat) → Set
m <′ n = (1+ m) ≤′ n

private
  variable
    ℓ l : Nat

data Product {n : Nat} : Set a where
  ne    : Product

record LogRelKit : Set (lsuc a) where
  constructor Kit
  field
    ⊩U : Set a
    ⊩B : Set a
    ⊩ : Set a
    ⊩/_ : ⊩ → Set a

module LogRel (l : Nat) (rec : ∀ {l′} → l′ <′ l → LogRelKit) where

  record ⊩₁U : Set a where
    constructor Uᵣ
    field
      l′  : Nat
      l<  : l′ <′ l

  record ⊩₁U/ : Set a where
    constructor Uₜ₌

  record ⊩ₗB : Set a where
    constructor Bᵣ
    eta-equality

  ⊩ₗΣ/_ :
    ([A] : ⊩ₗB) → Set a
  ⊩ₗΣ/_
    Bᵣ = Σ Product λ pProd → Nat

  data ⊩ₗ : Set a where
    Uᵣ  : ⊩₁U → ⊩ₗ
    Bᵣ  : ⊩ₗB → ⊩ₗ

  ⊩ₗ/_ : ⊩ₗ → Set a
  ⊩ₗ/ Uᵣ (Uᵣ l′ l<) = ⊩₁U/
  ⊩ₗ/ Bᵣ ΣA  = ⊩ₗΣ/ ΣA

  kit : LogRelKit
  kit = Kit ⊩₁U ⊩ₗB
            ⊩ₗ ⊩ₗ/_

open LogRel public
  using
    (Uᵣ; Bᵣ; Uₜ₌;
     module ⊩₁U; module ⊩₁U/;
     module ⊩ₗB)

pattern Σₜ₌ pProd prop = pProd , prop

pattern Uᵣ′ a b = Uᵣ (Uᵣ a b)

mutual
  kit : Nat → LogRelKit
  kit ℓ = LogRel.kit ℓ kit-helper

  kit-helper : {n m : Nat} → m <′ n → LogRelKit
  kit-helper {m = m} ≤′-refl = kit m
  kit-helper (≤′-step p) = kit-helper p


⊩⟨_⟩ : (l : Nat) → Set a
⊩⟨ l ⟩ = ⊩ where open LogRelKit (kit l)

⊩⟨_⟩∷/_ : (l : Nat) → ⊩⟨ l ⟩ → Set a
⊩⟨ l ⟩∷/ [A] = ⊩/ [A] where open LogRelKit (kit l)

transEqTerm :  {l : Nat}
              ([A] : ⊩⟨ l ⟩)
            → ⊩⟨ l ⟩∷/ [A]
            → ⊩⟨ l ⟩∷/ [A]
transEqTerm (Uᵣ′ l′ (≤′-step s)) _ =
              lemma (transEqTerm
              ? ?)
            where
              lemma : {l′ n : Nat} {s : l′ <′ n} →
                ⊩⟨ n ⟩∷/ Uᵣ′ _ s → ⊩⟨ 1+ n ⟩∷/ Uᵣ′ _ (≤′-step s)
              lemma = {!!}
transEqTerm
  (Bᵣ Bᵣ)
  (Σₜ₌ ne p~r) = {!!}
transEqTerm = ?
