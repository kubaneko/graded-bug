------------------------------------------------------------------------
-- Raw terms, weakening (renaming) and substitution.
------------------------------------------------------------------------

module Definition.Untyped {a} (M : Set a) where

open import Tools.Nat

data Term (n : Nat) : Set a where

private
  variable
    n : Nat
    t : Term n

data Neutral : Term n → Set a where

-- Weak head normal forms (whnfs).

-- These are the (lazy) values of our language.

data Product {n : Nat} : Term n → Set a where
  ne    : Neutral t → Product t

