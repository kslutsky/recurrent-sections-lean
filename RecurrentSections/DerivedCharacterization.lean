/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.VolumeBounds
import RecurrentSections.BorelTools
import RecurrentSections.Maximality

/-! # Characterizations with the geometric and Borel interfaces constructed

The remaining published inputs appear individually in the signatures.
No `PolynomialGeometry` or `StandardBorelTools` argument is requested.
-/

namespace RecurrentSections

variable {G : Type} [Group G] [DecidableEq G]

theorem recurrence_iff_polynomialGrowth_of_standard_theorems (W : WordGeometry G)
    (test : Nonempty (FreePmpModel G)) (volume : PolynomialVolumeTheorem W) :
    UniversalRecurrence W ↔ PolynomialGrowth W.volume :=
  recurrence_iff_polynomialGrowth W test
    (polynomialGeometry_of_standard_theorems W volume) (standardBorelTools W)

theorem maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems (W : WordGeometry G)
    (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
    (test : Nonempty (FreePmpModel G)) (volume : PolynomialVolumeTheorem W) :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  maximalRecurrence_iff_virtuallyNilpotent W gromov test
    (polynomialGeometry_of_standard_theorems W volume) (standardBorelTools W)

/-- The positive recurrence construction from volume doubling is fully
proved, with no external mathematical theorem as a parameter. -/
theorem universalRecurrence_of_volumeDoubling (W : WordGeometry G)
    {D : ℕ} (hD : VolumeDoubling W.volume D) : UniversalRecurrence W :=
  universalRecurrence_of_polynomialGrowth W (polynomialGeometry_of_volumeDoubling W hD)
    (standardBorelTools W) (polynomialGrowth_of_volumeDoubling W hD)

theorem universalRecurrence_of_twoSidedPolynomialGrowth (W : WordGeometry G)
    (h : TwoSidedPolynomialGrowth W.volume) : UniversalRecurrence W := by
  obtain ⟨_, _, hD⟩ := h.doubling
  exact universalRecurrence_of_volumeDoubling W hD

/-- All Borel actions of a finite group have prescribed-radius recurrence. -/
theorem universalRecurrence_of_finite [Finite G] (W : WordGeometry G) : UniversalRecurrence W :=
  universalRecurrence_of_twoSidedPolynomialGrowth W (twoSidedPolynomialGrowth_of_finite W)

end RecurrentSections
