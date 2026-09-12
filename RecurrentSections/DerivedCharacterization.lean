/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.NilpotentVolume
import RecurrentSections.BorelTools
import RecurrentSections.Maximality

/-! # Characterizations with the geometric and Borel interfaces constructed

The remaining published inputs appear individually in the signatures.
The test action is proved. No `PolynomialGeometry`, `StandardBorelTools`,
or `FreePmpModel` argument is requested.

The Gromov equivalence is proved in `GromovTheorem.lean`. The remaining
input is `volume`: Breuillard, Groups Geom. Dyn. 8 (2014), Theorem 1.1,
p. 670, https://doi.org/10.4171/GGD/244, supplies a stronger asymptotic
volume conclusion. The exact matching-bounds input appears in
`PolynomialGeometry.lean`; `NilpotentVolume.lean` reduces it to the
nilpotent matching-volume estimate of Bass--Guivarc'h.
-/

namespace RecurrentSections

variable {G : Type} [Group G] [DecidableEq G]

theorem recurrence_iff_polynomialGrowth_of_standard_theorems (W : WordGeometry G)
    (volume : PolynomialVolumeTheorem W) :
    UniversalRecurrence W ↔ PolynomialGrowth W.volume :=
  recurrence_iff_polynomialGrowth W
    (polynomialGeometry_of_standard_theorems W volume) (standardBorelTools W)

theorem maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems (W : WordGeometry G)
    (volume : PolynomialVolumeTheorem W) :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  maximalRecurrence_iff_virtuallyNilpotent W
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

/-- A single explicit nilpotent volume input supplies the remaining geometry.
The Gromov equivalence and the finite-index reductions are proved. -/
theorem maximalRecurrence_iff_virtuallyNilpotent_of_nilpotent_volume (W : WordGeometry G)
    (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{0}) :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems W
    (polynomialVolumeTheorem_of_nilpotent_volume W nilpotentVolume)

end RecurrentSections
