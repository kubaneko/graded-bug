------------------------------------------------------------------------
-- Graded modal type theory formalized in Agda
------------------------------------------------------------------------

module Everything where

------------------------------------------------------------------------
-- A small library

import Tools.Level
import Tools.Unit
import Tools.Relation
import Tools.Product
import Tools.PropositionalEquality
import Tools.Empty
import Tools.Sum
import Tools.Function
import Tools.Bool
import Tools.Nat
import Tools.Fin
import Tools.List
import Tools.Algebra

import Tools.Reasoning.Preorder
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Graded modalities

import Graded.Modality.Variant
import Graded.Modality
import Graded.Modality.Nr-instances
import Graded.Modality.Dedicated-nr
import Graded.Modality.Dedicated-nr.Instance

------------------------------------------------------------------------
-- The type theory's syntax

import Definition.Untyped.NotParametrised
import Definition.Untyped
import Definition.Untyped.Inversion
import Definition.Untyped.Properties.NotParametrised
import Definition.Untyped.Properties
import Definition.Untyped.Identity
import Definition.Untyped.Sigma
import Definition.Untyped.Unit
import Graded.Derived.Erased.Eta.Untyped
import Graded.Derived.Erased.NoEta.Untyped
import Graded.Derived.Erased.Untyped

------------------------------------------------------------------------
-- The type theory

-- Typing and conversion rules of language
import Definition.Typed.Restrictions
import Definition.Typed
import Definition.Typed.Reasoning.Type
import Definition.Typed.Reasoning.Term
import Definition.Typed.Properties.Well-formed
import Graded.Derived.Erased.Typed.Primitive
import Definition.Typed.Properties
import Definition.Typed.Weakening
import Definition.Typed.Reduction
import Definition.Typed.RedSteps
import Definition.Typed.EqualityRelation
import Definition.Typed.EqRelInstance

-- The logical relation for reducibility
import Definition.LogicalRelation
import Definition.LogicalRelation.Properties.Reflexivity
import Definition.LogicalRelation.Properties.Escape
import Definition.LogicalRelation.ShapeView
import Definition.LogicalRelation.Irrelevance
import Definition.LogicalRelation.Properties.Conversion
import Definition.LogicalRelation.Properties.Cumulativity
import Definition.LogicalRelation.Properties.Symmetry
import Definition.LogicalRelation.Properties.Neutral
import Definition.LogicalRelation.Properties.Successor
import Definition.LogicalRelation.Properties.Bug
-- import Definition.LogicalRelation.Properties.Reduction
-- import Definition.LogicalRelation.Properties
-- import Definition.LogicalRelation.Weakening
-- import Definition.LogicalRelation.Application

-- import Definition.Typed.Reasoning.Reduction
-- import Graded.Derived.Erased.Eta.Typed.Primitive
-- import Graded.Derived.Erased.Eta.Typed
-- import Graded.Derived.Erased.NoEta.Typed
-- import Graded.Derived.Erased.Typed
-- import Definition.Typed.Consequences.NeTypeEq
-- import Definition.Typed.Consequences.Consistency
-- import Definition.Typed.Consequences.RedSteps

-- -- Algorithmic equality with lemmas that depend on typing consequences
-- import Definition.Untyped.Normal-form
-- import Definition.Typed.Eta-long-normal-form
-- import Definition.Conversion.FullReduction

-- -- Bi-directional typechecking
-- import Definition.Typechecking
-- import Definition.Typechecking.Deterministic
-- import Definition.Typechecking.Soundness
-- import Definition.Typechecking.Completeness

-- -- Decidability of typing
-- import Definition.Typed.Decidable.Equality
-- import Definition.Typed.Decidable.Reduction
-- import Definition.Typechecking.Decidable.Assumptions
-- import Definition.Typechecking.Decidable
-- import Definition.Typed.Decidable

-- -- Subject reduction for modalities.
-- import Graded.Reduction

-- -- A "full reduction" lemma for modalities.
-- import Graded.FullReduction

-- -- Modality morphisms and quantity translations
-- import Definition.Untyped.QuantityTranslation
-- import Definition.Typed.QuantityTranslation
-- import Graded.Context.QuantityTranslation
-- import Graded.Mode.QuantityTranslation
-- import Graded.Usage.QuantityTranslation

-- -- Extended modalities.

-- import Graded.Modality.Extended
-- import Graded.Modality.Extended.K-allowed
-- import Graded.Modality.Extended.K-not-allowed.Erased-matches
-- import Graded.Modality.Extended.K-not-allowed.No-erased-matches

-- ------------------------------------------------------------------------
-- -- A case study: erasure

-- -- Target language

-- import Graded.Erasure.Target
-- import Graded.Erasure.Target.Properties.Weakening
-- import Graded.Erasure.Target.Properties.Substitution
-- import Graded.Erasure.Target.Properties.Reduction
-- import Graded.Erasure.Target.Properties
-- import Graded.Erasure.Target.Reasoning
-- import Graded.Erasure.Target.Non-terminating

-- -- Extraction

-- import Graded.Erasure.Extraction
-- import Graded.Erasure.Extraction.Properties
-- import Graded.Erasure.Extraction.Non-terminating

-- -- Soundness of Extraction function
-- import Graded.Erasure.SucRed
-- import Graded.Erasure.Consequences.Soundness

-- -- The fundamental lemma does not hold in general without the
-- -- assumption that erased matches are disallowed or the context is
-- -- empty
-- import Graded.Erasure.LogicalRelation.Fundamental.Counterexample

-- -- Non-interference
-- import Graded.Erasure.Consequences.Non-interference

-- -- More consequences of the fundamental lemma.
-- import Graded.Erasure.Consequences.Identity
-- import Graded.Erasure.Consequences.Resurrectable

-- -- A result related to neutral terms and usage.
-- import Graded.Neutral

-- -- Some discussion of under what circumstances a []-cong combinator
-- -- can be defined.
-- import Graded.Box-cong

-- -- Some examples related to the erasure modality and extraction

-- import Graded.Erasure.Examples

-- ------------------------------------------------------------------------
-- -- Some applications

-- -- Application: consistent negative axioms preserve canonicity
-- import Application.NegativeAxioms.NegativeType
-- import Application.NegativeAxioms.NegativeContext
-- import Application.NegativeAxioms.Canonicity

-- -- Application: consistent negative or erased axioms preserve canonicity
-- import Application.NegativeOrErasedAxioms.NegativeOrErasedType
-- import Application.NegativeOrErasedAxioms.NegativeOrErasedContext
-- import Application.NegativeOrErasedAxioms.Canonicity
-- -- ... but not if matching is allowed on erased pairs
-- import Application.NegativeOrErasedAxioms.Canonicity.ErasedMatches

-- ------------------------------------------------------------------------
-- -- Pointers to code related to a paper

-- -- Pointers to code related to the paper "A Graded Modal Dependent
-- -- Type Theory with a Universe and Erasure, Formalized".
-- import README
