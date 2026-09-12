/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.QuotientGeometry
import RecurrentSections.CentralCommutators
import Mathlib.GroupTheory.Nilpotent

/-! # Integral power compression

The commutator step in the classical nilpotent power-compression proof is
stated using integral radii and exponents bounded by powers of the radius.
Compare Druţu--Kapovich, *Geometric Group Theory*, September 2017 author
draft, Lemma 14.15, p. 503:
https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
The lemma here isolates the calculation with a central quotient and a
central commutator. The supplied compression hypothesis is intended to
come from induction on the lower-central length.
-/

namespace RecurrentSections
open scoped commutatorElement
variable {G : Type*} [Group G] [DecidableEq G]

def PowerCompression (W : WordGeometry G) (g : G) (k : ℕ) : Prop :=
  ∃ C : ℕ, ∀ r n : ℕ, n ≤ r ^ k → W.length (g ^ n) ≤ C * (r + 1)

theorem WordGeometry.length_pow_le (W : WordGeometry G) (g : G) (n : ℕ) :
    W.length (g ^ n) ≤ n * W.length g := by
  induction n with
  | zero => simp [W.length_one]
  | succ n ih =>
    rw [pow_succ]
    exact (W.length_mul_le _ _).trans (by nlinarith)

theorem WordGeometry.length_commutator_le (W : WordGeometry G) (g h : G) :
    W.length ⁅g, h⁆ ≤ 2 * (W.length g + W.length h) := by
  have h₁ := W.length_mul_le g h
  have h₂ := W.length_mul_le (g * h) g⁻¹
  have h₃ := W.length_mul_le (g * h * g⁻¹) h⁻¹
  simp only [W.length_inv] at h₂ h₃
  change W.length (g * h * g⁻¹ * h⁻¹) ≤ _
  omega

/-- A central commutator gains one degree of power compression from the
other argument modulo a central subgroup. Radii are integral and no real
roots or exceptional radii are needed. -/
theorem powerCompression_commutator
    (W : WordGeometry G) (N : Subgroup G) [N.Normal] [DecidableEq (G ⧸ N)] (hN : N ≤ Subgroup.center G)
    (x y : G) (hxy : ⁅x, y⁆ ∈ Subgroup.center G) (k : ℕ)
    (hy : PowerCompression (W.map (QuotientGroup.mk' N) QuotientGroup.mk_surjective)
      ((QuotientGroup.mk' N) y) k) : PowerCompression W ⁅x, y⁆ (k + 1) := by
  let f := QuotientGroup.mk' N
  obtain ⟨L, hL⟩ := hy
  have hx : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hxy x
  have hyc : Commute y ⁅x, y⁆ := Subgroup.mem_center_iff.mp hxy y
  refine ⟨8 * (L + W.length x + 1), fun r n hn => ?_⟩
  let q := r + 1
  let a := n / q ^ k
  let b := n % q ^ k
  have hq : 0 < q := by dsimp [q]; omega
  have hqk : 0 < q ^ k := by positivity
  have hab : a * q ^ k + b = n := by dsimp [a, b]; simpa only [Nat.mul_comm] using Nat.div_add_mod n (q ^ k)
  have hb : b ≤ q ^ k := (Nat.mod_lt n hqk).le
  have ha : a ≤ q := by
    have ha' : a * q ^ k ≤ n := Nat.div_mul_le_self n _
    have hn' : n ≤ q * q ^ k := by
      calc
        n ≤ r ^ (k + 1) := hn
        _ ≤ q ^ (k + 1) := Nat.pow_le_pow_left (by dsimp [q]; omega) _
        _ = q * q ^ k := pow_succ' _ _
    exact Nat.le_of_mul_le_mul_right (ha'.trans hn') hqk
  have hlift : ∀ m ≤ q ^ k, ∃ u : G, f u = f (y ^ m) ∧ W.length u ≤ L * (q + 1) := by
    intro m hm
    obtain ⟨u, hu, hlen⟩ := W.exists_lift_length_eq f QuotientGroup.mk_surjective (f (y ^ m))
    refine ⟨u, hu, hlen.le.trans ?_⟩
    simpa only [map_pow] using hL q m hm
  obtain ⟨u, hu, hulen⟩ := hlift (q ^ k) le_rfl
  obtain ⟨v, hv, hvlen⟩ := hlift b hb
  have hucomm : ⁅u, x ^ a⁆ = ⁅y ^ (q ^ k), x ^ a⁆ := commutator_eq_of_quotient_eq N hN hu _
  have hvcomm : ⁅v, x⁆ = ⁅y ^ b, x⁆ := commutator_eq_of_quotient_eq N hN hv _
  have hpow : ⁅x ^ a, y ^ (q ^ k)⁆ = ⁅x, y⁆ ^ (a * q ^ k) := by
    have hright := commutator_pow_right_of_commute x y hyc (q ^ k)
    rw [commutator_pow_left_of_commute x (y ^ (q ^ k)) (by rw [hright]; exact hx.pow_right _) a,
      hright, ← pow_mul, Nat.mul_comm]
  have he : ⁅u, x ^ a⁆⁻¹ * ⁅v, x⁆⁻¹ = ⁅x, y⁆ ^ n := by
    rw [hucomm, hvcomm, commutatorElement_inv, commutatorElement_inv,
      hpow, commutator_pow_right_of_commute x y hyc, ← pow_add, hab]
  calc
    W.length (⁅x, y⁆ ^ n) = W.length (⁅u, x ^ a⁆⁻¹ * ⁅v, x⁆⁻¹) := congrArg W.length he.symm
    _ ≤ W.length ⁅u, x ^ a⁆⁻¹ + W.length ⁅v, x⁆⁻¹ := W.length_mul_le _ _
    _ = W.length ⁅u, x ^ a⁆ + W.length ⁅v, x⁆ := by rw [W.length_inv, W.length_inv]
    _ ≤ 2 * (W.length u + W.length (x ^ a)) + 2 * (W.length v + W.length x) :=
      Nat.add_le_add (W.length_commutator_le _ _) (W.length_commutator_le _ _)
    _ ≤ 8 * (L + W.length x + 1) * (r + 1) := by
      have hxa := W.length_pow_le x a
      have haq := Nat.mul_le_mul_right (W.length x) ha
      dsimp [q] at hulen hvlen haq
      nlinarith

end RecurrentSections
