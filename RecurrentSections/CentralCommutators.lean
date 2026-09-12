/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace RecurrentSections
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Standard commutator multiplication identity, with our left convention. -/
theorem commutator_mul_left (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, ⁅y, z⁆⁆ * ⁅y, z⁆ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutator_mul_right (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅y, ⁅x, z⁆⁆ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

/-- Powers may be pulled out of a commutator when its value commutes with
the powered argument. Full centrality is unnecessary. -/
theorem commutator_pow_left_of_commute (x y : G) (h : Commute x ⁅x, y⁆) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutator_mul_left,
      commutatorElement_eq_one_iff_mul_comm.mpr (h.pow_left n).eq, one_mul, ih, pow_succ']

theorem commutator_pow_right_of_commute (x y : G) (h : Commute y ⁅x, y⁆) (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', commutator_mul_right, ih,
      commutatorElement_eq_one_iff_mul_comm.mpr (h.pow_right n).eq, mul_one, pow_succ']

/-- Changing an argument by a central factor does not change a commutator. -/
theorem commutator_mul_central_left (x y z : G) (hz : z ∈ Subgroup.center G) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have hzcomm : ⁅z, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz y).symm)
  rw [commutator_mul_left, hzcomm]
  simp

theorem commutator_mul_central_right (x y z : G) (hz : z ∈ Subgroup.center G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv y x, ← commutatorElement_inv (y * z) x,
    commutator_mul_central_left y x z hz]

/-- Equality modulo a central subgroup is sufficient for equality of
commutators. -/
theorem commutator_eq_of_quotient_eq (N : Subgroup G) [N.Normal]
    (hN : N ≤ Subgroup.center G) {g h : G}
    (he : (QuotientGroup.mk' N) g = (QuotientGroup.mk' N) h) (x : G) :
    ⁅g, x⁆ = ⁅h, x⁆ := by
  have hz : h⁻¹ * g ∈ N := by
    have : (QuotientGroup.mk' N) (h⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [← QuotientGroup.ker_mk' N]
    exact this
  have hprod : g = h * (h⁻¹ * g) := by group
  rw [hprod, commutator_mul_central_left h x (h⁻¹ * g) (hN hz)]

end RecurrentSections
