/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.AbelianVolume
import RecurrentSections.GromovTheorem

/-! # Reduction to the nilpotent polynomial-volume theorem

Gromov's forward theorem and passage through finite index are proved.
The remaining input is the matching-volume conclusion of Bass--Guivarc'h
for finitely generated nilpotent groups. It is explicitly a hypothesis,
not an axiom or a theorem proved by this module.

Sources: H. Bass, *The degree of polynomial growth of finitely generated
nilpotent groups*, Proc. London Math. Soc. (3) 25 (1972), 603--614,
https://doi.org/10.1112/plms/s3-25.4.603;
Y. Guivarc'h, *Croissance polynomiale et périodes des fonctions harmoniques*,
Bull. Soc. Math. France 101 (1973), 333--379,
https://doi.org/10.24033/bsmf.1764.

The statement below only asks for existence of matching integer-power bounds;
it does not assert the explicit Bass--Guivarc'h formula for the exponent.
Finite generation is already part of `WordGeometry`. Neither torsion-freeness
nor a polynomial upper bound is assumed for the nilpotent group.
-/

namespace RecurrentSections

universe u

/-- The as-yet-unproved nilpotent volume input, in the exact normalization
needed here. Merely naming this proposition does not prove the input. -/
def NilpotentPolynomialVolumeTheorem : Prop :=
  ∀ (G : Type u) [Group G] [DecidableEq G] [Group.IsNilpotent G],
    ∀ W : WordGeometry G, TwoSidedPolynomialGrowth W.volume

theorem TwoSidedPolynomialGrowth.polynomialGrowth {v : ℕ → ℕ}
    (h : TwoSidedPolynomialGrowth v) : PolynomialGrowth v := by
  obtain ⟨C, d, _, hCd⟩ := h
  exact ⟨C, d, fun n => (hCd n).2⟩

variable {G : Type u} [Group G] [DecidableEq G]

/-- Finite-index reduction, using the nilpotent volume theorem once on a
finitely generated nilpotent subgroup. -/
theorem twoSidedPolynomialGrowth_of_virtuallyNilpotent (W : WordGeometry G)
    (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{u})
    (h : Group.IsVirtuallyNilpotent G) : TwoSidedPolynomialGrowth W.volume := by
  obtain ⟨N, hN, hindex⟩ := h
  let : Group.IsNilpotent N := hN
  let : N.FiniteIndex := hindex
  let : Group.FG G := W.fg
  let : Group.FG N := Subgroup.fg_of_index_ne_zero N
  let V := WordGeometry.ofFG N
  exact (twoSidedPolynomialGrowth_iff_subgroup W N V).mpr (nilpotentVolume N V)

/-- The full Gromov equivalence follows from the proved forward theorem and
the still-explicit nilpotent volume estimate. -/
theorem polynomialGrowth_iff_virtuallyNilpotent_of_nilpotent_volume (W : WordGeometry G)
    (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{u}) :
    PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G :=
  ⟨virtuallyNilpotent_of_polynomialGrowth W,
    fun h => (twoSidedPolynomialGrowth_of_virtuallyNilpotent W nilpotentVolume h).polynomialGrowth⟩

/-- The polynomial-volume theorem reduces to the same nilpotent estimate;
the exponent of the initial polynomial upper bound is not fixed. -/
theorem polynomialVolumeTheorem_of_nilpotent_volume {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{0}) :
    PolynomialVolumeTheorem W := fun h =>
  twoSidedPolynomialGrowth_of_virtuallyNilpotent W nilpotentVolume
    (virtuallyNilpotent_of_polynomialGrowth W h)

end RecurrentSections
