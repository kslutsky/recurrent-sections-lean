/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Converse

/-! # The group-level statement and its precise external inputs

The converse uses the published existence of a free pmp Borel action and
Gromov's theorem only as explicit hypotheses. This file provides a modular
assembly lemma. Sufficiency.lean proves the positive construction from
standard geometric and Borel inputs and supplies the final equivalence.
-/

namespace RecurrentSections

open MeasureTheory

variable {G : Type} [Group G] [DecidableEq G]

/-- Every Borel action on a standard Borel space has the prescribed-radii
recurrence property. No freeness assumption occurs in this definition. -/
def UniversalRecurrence (W : WordGeometry G) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X],
      HasRecurrentSections (X := X) W

/-- The analogous property restricted to free Borel actions. -/
def UniversalFreeRecurrence (W : WordGeometry G) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X],
      FreeAction (G := G) (X := X) → HasRecurrentSections (X := X) W

/-- A free probability-preserving Borel test action. The standard theorem
giving such an action (for a countable group) is an external input. -/
structure FreePmpModel (G : Type) [Group G] where
  Space : Type
  [measurableSpace : MeasurableSpace Space]
  [standardBorel : StandardBorelSpace Space]
  [action : MulAction G Space]
  [measurableAction : MeasurableConstSMul G Space]
  measure : Measure Space
  [probability : IsProbabilityMeasure measure]
  [invariant : SMulInvariantMeasure G Space measure]
  free : FreeAction (G := G) (X := Space)

/-- The only external input here is the free pmp test action. -/
theorem polynomialGrowth_of_universalFreeRecurrence (W : WordGeometry G)
    (test : Nonempty (FreePmpModel G)) (hrec : UniversalFreeRecurrence W) :
    PolynomialGrowth W.volume := by
  obtain ⟨A⟩ := test
  letI := A.measurableSpace
  letI := A.standardBorel
  letI := A.action
  letI := A.measurableAction
  letI := A.probability
  letI := A.invariant
  exact polynomialGrowth_of_recurrent W A.measure A.free (hrec A.Space A.free)

theorem universalFreeRecurrence_of_universalRecurrence (W : WordGeometry G)
    (hrec : UniversalRecurrence W) : UniversalFreeRecurrence W := by
  intro X _ _ _ _ _
  exact hrec X

theorem polynomialGrowth_of_universalRecurrence (W : WordGeometry G)
    (test : Nonempty (FreePmpModel G)) (hrec : UniversalRecurrence W) :
    PolynomialGrowth W.volume :=
  polynomialGrowth_of_universalFreeRecurrence W test
    (universalFreeRecurrence_of_universalRecurrence W hrec)

/-- The requested implication, conditional only on the two explicitly
permitted published results. The proof of polynomial growth is checked. -/
theorem virtuallyNilpotent_of_universalRecurrence (W : WordGeometry G)
    (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
    (test : Nonempty (FreePmpModel G)) (hrec : UniversalRecurrence W) :
    Group.IsVirtuallyNilpotent G :=
  gromov.mp (polynomialGrowth_of_universalRecurrence W test hrec)

/-- The positive direction, proved from standard inputs in Sufficiency.lean. -/
def PositiveConstruction (W : WordGeometry G) : Prop :=
  PolynomialGrowth W.volume → UniversalRecurrence W

/-- A modular assembly lemma; the final theorem in Sufficiency.lean
discharges this positive-direction hypothesis. -/
theorem recurrence_iff_virtuallyNilpotent_of_positive (W : WordGeometry G)
    (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
    (test : Nonempty (FreePmpModel G)) (positive : PositiveConstruction W) :
    UniversalRecurrence W ↔ Group.IsVirtuallyNilpotent G := by
  constructor
  · exact virtuallyNilpotent_of_universalRecurrence W gromov test
  · intro hnil
    exact positive (gromov.mpr hnil)

end RecurrentSections
