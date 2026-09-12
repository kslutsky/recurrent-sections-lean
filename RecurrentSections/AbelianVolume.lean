/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.VolumeBounds
import RecurrentSections.FreeAbelianGeometry
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Polynomial volume bounds for finitely generated abelian groups

Mathlib's `CommGroup.equiv_free_prod_prod_multiplicative_zmod` supplies the
classical structure theorem. The kernel of projection to the finite torsion
factor is free abelian and has finite index. Cubical word balls give matching
bounds there; finite-index and generating-set comparisons give the result
for the original word metric. No nilpotent volume estimate is assumed.
-/

namespace RecurrentSections

open FreeAbelianGeometry

theorem twoSidedPolynomialGrowth_wordGeometry (d : ℕ) :
    TwoSidedPolynomialGrowth (wordGeometry d).volume := by
  refine ⟨2 ^ d, d, by positivity, fun n => ?_⟩
  rw [volume_wordGeometry]
  constructor
  · calc
      (n + 1) ^ d ≤ (2 * n + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      _ ≤ 2 ^ d * (2 * n + 1) ^ d := Nat.le_mul_of_pos_left _ (by positivity)
  · calc
      (2 * n + 1) ^ d ≤ (2 * (n + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * (n + 1) ^ d := mul_pow _ _ _

/-- Every finite word metric on a finitely generated abelian group has
matching polynomial volume bounds. The group may have torsion. -/
theorem twoSidedPolynomialGrowth_of_commGroup {G : Type*} [CommGroup G] [DecidableEq G]
    (W : WordGeometry G) : TwoSidedPolynomialGrowth W.volume := by
  classical
  let : Group.FG G := W.fg
  obtain ⟨ι, j, hι, hj, p, hp, a, ⟨e⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  let F := (i : ι) → Multiplicative (ZMod (p i ^ a i))
  let : ∀ i, NeZero (p i ^ a i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let : Finite F := inferInstance
  let q : G →* F := (MonoidHom.snd (j → Multiplicative ℤ) F).comp e.toMonoidHom
  let N := q.ker
  let : N.FiniteIndex := Subgroup.finiteIndex_ker q
  let : Group.FG N := Subgroup.fg_of_index_ne_zero N
  let V := WordGeometry.ofFG N
  let eN : N ≃* (j → Multiplicative ℤ) :=
    { toFun := fun n => (e n).1
      invFun := fun x => ⟨e.symm (x, 1), by change q (e.symm (x, 1)) = 1; simp [q]⟩
      left_inv := by
        intro n
        apply Subtype.ext
        apply e.injective
        simp only [e.apply_symm_apply]
        apply Prod.ext
        · rfl
        · have hn := n.property
          exact hn.symm
      right_inv := by intro x; simp
      map_mul' := by intro x y; simp }
  let er : (j → Multiplicative ℤ) ≃* Multiplicative (Fin (Fintype.card j) → ℤ) :=
    { toFun := fun x => Multiplicative.ofAdd (fun i => (x ((Fintype.equivFin j).symm i)).toAdd)
      invFun := fun x i => Multiplicative.ofAdd (x.toAdd (Fintype.equivFin j i))
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; apply Multiplicative.ext; funext i; simp
      map_mul' := by intro x y; rfl }
  apply (twoSidedPolynomialGrowth_iff_subgroup W N V).mpr
  exact (twoSidedPolynomialGrowth_iff_mulEquiv V (wordGeometry (Fintype.card j))
    (eN.trans er)).mpr (twoSidedPolynomialGrowth_wordGeometry _)

end RecurrentSections
