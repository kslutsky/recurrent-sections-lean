/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.NilpotentMatchingVolume
import RecurrentSections.GromovTheorem

/-! # Polynomial volume from polynomial growth

Gromov's equivalence, the nilpotent matching-volume estimate, and passage
through finite index are proved. `polynomialVolumeTheorem` inhabits the
volume interface used by the recurrent-section construction. The earlier
conditional reductions remain available as modular assembly lemmas.

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

/-- The nilpotent matching-volume statement in the required normalization.
Its proof is `nilpotentPolynomialVolumeTheorem` below. -/
def NilpotentPolynomialVolumeTheorem : Prop :=
  ∀ (G : Type u) [Group G] [DecidableEq G] [Group.IsNilpotent G],
    ∀ W : WordGeometry G, TwoSidedPolynomialGrowth W.volume

variable {G : Type u} [Group G] [DecidableEq G]

/-- Finite-index reduction, using the nilpotent volume theorem once on a
finitely generated nilpotent subgroup. -/
theorem twoSidedPolynomialGrowth_of_virtuallyNilpotent_of_nilpotent_volume (W : WordGeometry G)
    (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{u})
    (h : Group.IsVirtuallyNilpotent G) : TwoSidedPolynomialGrowth W.volume := by
  obtain ⟨N, hN, hindex⟩ := h
  let : Group.IsNilpotent N := hN
  let : N.FiniteIndex := hindex
  let : Group.FG G := W.fg
  let : Group.FG N := Subgroup.fg_of_index_ne_zero N
  let V := WordGeometry.ofFG N
  exact (twoSidedPolynomialGrowth_iff_subgroup W N V).mpr (nilpotentVolume N V)

/-- The polynomial-volume theorem reduces to the same nilpotent estimate;
the exponent of the initial polynomial upper bound is not fixed. -/
theorem polynomialVolumeTheorem_of_nilpotent_volume {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) (nilpotentVolume : NilpotentPolynomialVolumeTheorem.{0}) :
    PolynomialVolumeTheorem W := fun h =>
  twoSidedPolynomialGrowth_of_virtuallyNilpotent_of_nilpotent_volume W nilpotentVolume
    (virtuallyNilpotent_of_polynomialGrowth W h)

/-- The nilpotent matching-volume proposition is now proved, including
finite groups and groups with torsion. -/
theorem nilpotentPolynomialVolumeTheorem : NilpotentPolynomialVolumeTheorem.{u} :=
  fun _G _ _ _ W => twoSidedPolynomialGrowth_of_nilpotent W

/-- Matching polynomial word-volume bounds for every virtually nilpotent
group with an explicit finite word geometry. -/
theorem twoSidedPolynomialGrowth_of_virtuallyNilpotent (W : WordGeometry G)
    (h : Group.IsVirtuallyNilpotent G) : TwoSidedPolynomialGrowth W.volume :=
  twoSidedPolynomialGrowth_of_virtuallyNilpotent_of_nilpotent_volume W
    nilpotentPolynomialVolumeTheorem h

/-- Polynomial growth implies matching integer-power volume bounds. This
proves the exact formerly external interface, without an unproved theorem
argument. The matching exponent need not equal the supplied upper exponent. -/
theorem polynomialVolumeTheorem {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) : PolynomialVolumeTheorem W :=
  polynomialVolumeTheorem_of_nilpotent_volume W nilpotentPolynomialVolumeTheorem

end RecurrentSections
