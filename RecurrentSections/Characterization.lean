/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Converse
import RecurrentSections.FreePmpModel

/-! # The group-level statement and its precise external inputs

The free pmp Bernoulli test action is constructed in `FreePmpModel.lean`.
The converse uses the proved Gromov theorem. This file provides a modular
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

/-- Universal free recurrence forces polynomial growth, using the proved Bernoulli test action. -/
theorem polynomialGrowth_of_universalFreeRecurrence (W : WordGeometry G)
    (hrec : UniversalFreeRecurrence W) :
    PolynomialGrowth W.volume := by
  let := W.countable
  obtain ⟨A⟩ := nonempty_freePmpModel G
  let := A.measurableSpace
  let := A.standardBorel
  let := A.action
  let := A.measurableAction
  let := A.probability
  let := A.invariant
  exact polynomialGrowth_of_recurrent W A.measure A.free (hrec A.Space A.free)

theorem universalFreeRecurrence_of_universalRecurrence (W : WordGeometry G)
    (hrec : UniversalRecurrence W) : UniversalFreeRecurrence W := by
  intro X _ _ _ _ _
  exact hrec X

theorem polynomialGrowth_of_universalRecurrence (W : WordGeometry G)
    (hrec : UniversalRecurrence W) :
    PolynomialGrowth W.volume :=
  polynomialGrowth_of_universalFreeRecurrence W
    (universalFreeRecurrence_of_universalRecurrence W hrec)

/-- The requested implication with no unproved mathematical inputs. -/
theorem virtuallyNilpotent_of_universalRecurrence (W : WordGeometry G)
    (hrec : UniversalRecurrence W) :
    Group.IsVirtuallyNilpotent G :=
  virtuallyNilpotent_of_polynomialGrowth W (polynomialGrowth_of_universalRecurrence W hrec)

/-- The positive direction, proved from standard inputs in Sufficiency.lean. -/
def PositiveConstruction (W : WordGeometry G) : Prop :=
  PolynomialGrowth W.volume → UniversalRecurrence W

/-- A modular assembly lemma; the final theorem in Sufficiency.lean
discharges this positive-direction hypothesis. -/
theorem recurrence_iff_virtuallyNilpotent_of_positive (W : WordGeometry G)
    (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
    (positive : PositiveConstruction W) :
    UniversalRecurrence W ↔ Group.IsVirtuallyNilpotent G := by
  constructor
  · exact virtuallyNilpotent_of_universalRecurrence W
  · intro hnil
    exact positive (gromov.mpr hnil)

end RecurrentSections
