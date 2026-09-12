/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.NilpotentVolume
import RecurrentSections.PolynomialGeometry
import RecurrentSections.BorelTools
import RecurrentSections.Maximality

/-! # Complete recurrent-section characterizations

The geometric and Borel interfaces, Bernoulli test action, Gromov theorem,
and matching polynomial volume bounds are all proved. The theorems ending
in `_of_standard_theorems` require only the group and its word geometry.
Conditional assembly interfaces remain available in the lower-level modules.
-/

namespace RecurrentSections

variable {G : Type} [Group G] [DecidableEq G]

theorem recurrence_iff_polynomialGrowth_of_standard_theorems (W : WordGeometry G)
    :
    UniversalRecurrence W ↔ PolynomialGrowth W.volume :=
  recurrence_iff_polynomialGrowth W
    (polynomialGeometry_of_standard_theorems W (polynomialVolumeTheorem W)) (standardBorelTools W)

theorem maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems (W : WordGeometry G)
    :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  maximalRecurrence_iff_virtuallyNilpotent W
    (polynomialGeometry_of_standard_theorems W (polynomialVolumeTheorem W)) (standardBorelTools W)

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

/-- A retained modular assembly lemma. Its explicit input is now inhabited
by `nilpotentPolynomialVolumeTheorem`; the complete characterization above
does not require that argument. -/
theorem maximalRecurrence_iff_virtuallyNilpotent_of_nilpotent_volume (W : WordGeometry G)
    (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{0}) :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  maximalRecurrence_iff_virtuallyNilpotent W
    (polynomialGeometry_of_standard_theorems W
      (polynomialVolumeTheorem_of_nilpotent_volume W nilpotentVolume)) (standardBorelTools W)

/-- The nonmaximal recurrence characterization, with all inputs constructed. -/
theorem recurrence_iff_virtuallyNilpotent_of_standard_theorems (W : WordGeometry G) :
    UniversalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  (recurrence_iff_polynomialGrowth_of_standard_theorems W).trans
    (polynomialGrowth_iff_virtuallyNilpotent W)

/-- Restricting the quantification to free actions gives the same class. -/
theorem freeRecurrence_iff_polynomialGrowth_of_standard_theorems (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ PolynomialGrowth W.volume :=
  ⟨polynomialGrowth_of_universalFreeRecurrence W, fun h =>
    universalFreeRecurrence_of_universalRecurrence W
      ((recurrence_iff_polynomialGrowth_of_standard_theorems W).mpr h)⟩

theorem freeRecurrence_iff_virtuallyNilpotent_of_standard_theorems (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  (freeRecurrence_iff_polynomialGrowth_of_standard_theorems W).trans
    (polynomialGrowth_iff_virtuallyNilpotent W)

end RecurrentSections
