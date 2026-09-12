/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Recurrent cross sections characterize polynomial growth

This is the independent statement for Comparator. Its only imports are Mathlib;
all project-specific definitions used below are given here in full. The five
intentional theorem holes are implemented by `Solution.lean`. Definitions have
no holes. Comparator checks their values as well as the theorem types.

For a finitely generated group, recurrent Borel cross sections at every
prescribed strictly increasing positive integer radius schedule exist for all
Borel actions exactly when the group has polynomial growth, equivalently when
it is virtually nilpotent. Restricting to free actions gives the same class.
One recurrent sequence in a free probability-preserving action already forces
subexponential growth. The latter assertion does not require a standard Borel
space or completeness of the sections.

Boykin–Jackson's construction for free lattice actions is formulated in
Marks–Unger, *Borel circle squaring*, Appendix A, Lemma A.2 and Problem A.3
(https://doi.org/10.4007/annals.2017.186.2.4). The generalized construction
and growth obstructions are the local results recorded here; no priority
claim is made. Gromov, Wolf, and the matching-bounds consequence of
Bass–Guivarc'h supply classical group geometry. The difficult Gromov implication
uses Aaron Hill's existing formalization at
https://github.com/Aaron1011/gromov/tree/8db79f13cf211b570e3116301d91379fbc01cf3e.
See `formalization.yaml` and `REFERENCES.md` for sources and their exact roles.

All recurrence is everywhere, not merely almost everywhere. Each section
meets every orbit; separation concerns distinct points even for actions with
stabilizers. The finite symmetric generating set contains the identity, so
its powers are closed word balls. The formalization covers finite groups and
torsion. The one-sequence theorem retains the freeness and invariant probability
hypotheses. No converse for subexponential growth, assertion of hyperfiniteness,
locally compact extension, explicit growth-degree formula, or asymptotic volume
limit is asserted by this statement.
-/

open MeasureTheory
open scoped Pointwise Topology

namespace RecurrentSections

/-- A finite symmetric generating set containing the identity. Exhaustion by
its powers expresses finite generation. -/
structure WordGeometry (G : Type*) [Group G] [DecidableEq G] where
  generators : Finset G
  one_mem : 1 ∈ generators
  inv_mem : ∀ g ∈ generators, g⁻¹ ∈ generators
  generates : ∀ g : G, ∃ n : ℕ, g ∈ generators ^ n

variable {G : Type*} [Group G] [DecidableEq G]

namespace WordGeometry

/-- The closed word ball of integer radius `n`. -/
def ball (W : WordGeometry G) (n : ℕ) : Finset G := W.generators ^ n

/-- Cardinality of the closed word ball. -/
def volume (W : WordGeometry G) (n : ℕ) : ℕ := (W.ball n).card

/-- The least radius of a word ball containing the group element. -/
noncomputable def length (W : WordGeometry G) (g : G) : ℕ :=
  Nat.find (W.generates g)

end WordGeometry

variable {X : Type*} [MulAction G X]

/-- Distinct section points have orbit word distance strictly greater than `r`.
This is meaningful for arbitrary actions, including actions with stabilizers. -/
def Separated (W : WordGeometry G) (r : ℕ) (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ g ∈ W.ball r, g • x = y → x = y

/-- Every orbit meets the section. -/
def CompleteSection (C : Set X) : Prop :=
  ∀ x : X, ∃ g : G, ∃ c ∈ C, g • c = x

/-- For every positive real `ε` and every point `x`, the inequality
`d(x, C n) < ε * r n` holds for infinitely many `n`. Explicit displacement
witnesses avoid choosing an orbit metric on the entire space. -/
def Recurrent (W : WordGeometry G) (r : ℕ → ℕ) (C : ℕ → Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ x : X, ∀ N : ℕ,
    ∃ n, N ≤ n ∧ ∃ g : G, ∃ c ∈ C n,
      g • c = x ∧ (W.length g : ℝ) < ε * (r n : ℝ)

/-- Polynomial upper growth; shifting the radius by one includes radius zero. -/
def PolynomialGrowth (v : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, v n ≤ C * (n + 1) ^ d

/-- Subexponential growth in logarithmic normalization. -/
def SubexponentialGrowth (v : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.log (v n : ℝ) / n) Filter.atTop (𝓝 0)

end RecurrentSections

namespace RecurrentSections

variable {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]

/-- Freeness: every orbit map is injective. -/
def FreeAction : Prop := ∀ x : X, Function.Injective (fun g : G => g • x)

variable [MeasurableSpace X] [MeasurableConstSMul G X]

/-- Every prescribed strictly increasing positive integer radius schedule
admits a recurrent sequence of Borel, separated, complete sections. -/
def HasRecurrentSections (W : WordGeometry G) : Prop :=
  ∀ r : ℕ → ℕ, StrictMono r → (∀ n, 0 < r n) →
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, Separated W (r n) (C n)) ∧
      (∀ n, CompleteSection (G := G) (C n)) ∧ Recurrent W r C

end RecurrentSections

namespace RecurrentSections

variable {G : Type} [Group G] [DecidableEq G]

/-- Prescribed-radius recurrence for every standard Borel action.
For a countable group, measurable action maps are exactly a Borel action. -/
def UniversalRecurrence (W : WordGeometry G) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X],
      HasRecurrentSections (X := X) W

/-- The same quantification restricted to free standard Borel actions. -/
def UniversalFreeRecurrence (W : WordGeometry G) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X],
      FreeAction (G := G) (X := X) → HasRecurrentSections (X := X) W

end RecurrentSections

-- Only the five statement holes below may emit warnings.
set_option warningAsError false

namespace PalomarRecurrence

open RecurrentSections

variable {G : Type} [Group G] [DecidableEq G]

/-- Polynomial growth is characterized by prescribed-radius recurrence in
all standard Borel actions, allowing arbitrary stabilizers. -/
theorem recurrence_iff_polynomialGrowth (W : WordGeometry G) :
    UniversalRecurrence W ↔ PolynomialGrowth W.volume :=
  by sorry

/-- Equivalently, universal prescribed-radius recurrence characterizes virtual
nilpotence. Mathlib defines this as existence of a nilpotent subgroup of finite
index; the subgroup need not be normal. -/
theorem recurrence_iff_virtuallyNilpotent (W : WordGeometry G) :
    UniversalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  by sorry

/-- Quantifying over free actions alone still characterizes polynomial growth. -/
theorem freeRecurrence_iff_polynomialGrowth (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ PolynomialGrowth W.volume :=
  by sorry

/-- The free-action property is also equivalent to virtual nilpotence. -/
theorem freeRecurrence_iff_virtuallyNilpotent (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  by sorry

end PalomarRecurrence

namespace PalomarRecurrence

open RecurrentSections

/-- One everywhere recurrent sequence in one free probability-preserving
action forces subexponential growth. Strictly increasing integer radii,
measurability, and separation are assumed; complete sections are unnecessary. -/
theorem one_sequence_implies_subexponentialGrowth
    {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]
    [MeasurableSpace X] [MeasurableConstSMul G X]
    (W : WordGeometry G) (μ : Measure X)
    [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
    (hfree : FreeAction (G := G) (X := X))
    (r : ℕ → ℕ) (hr : StrictMono r) (C : ℕ → Set X)
    (hC : ∀ n, MeasurableSet (C n))
    (hsep : ∀ n, Separated W (r n) (C n))
    (hrec : Recurrent W r C) : SubexponentialGrowth W.volume :=
  by sorry

end PalomarRecurrence
