/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Growth
import RecurrentSections.WordGeometry

/-! # Numerical polynomial volume bounds and doubling

These definitions and numerical implications are independent of Borel
selection and of Gromov's structure theorem.
-/

namespace RecurrentSections

/-- Two-sided polynomial bounds, with an integer constant absorbing both
the upper constant and the reciprocal of the lower constant. -/
def TwoSidedPolynomialGrowth (v : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n, (n + 1) ^ d ≤ C * v n ∧ v n ≤ C * (n + 1) ^ d

/-- The shift by one includes small radii and finite groups. -/
def VolumeDoubling (v : ℕ → ℕ) (D : ℕ) : Prop :=
  ∀ n, v (2 * n + 1) ≤ D * v n

theorem TwoSidedPolynomialGrowth.doubling {v : ℕ → ℕ}
    (h : TwoSidedPolynomialGrowth v) : ∃ D, 0 < D ∧ VolumeDoubling v D := by
  obtain ⟨C, d, hC, h⟩ := h
  refine ⟨C * C * 2 ^ d, by positivity, fun n => ?_⟩
  calc
    v (2 * n + 1) ≤ C * (2 * n + 1 + 1) ^ d := (h _).2
    _ = C * 2 ^ d * (n + 1) ^ d := by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, mul_pow]; ring
    _ ≤ C * 2 ^ d * (C * v n) := Nat.mul_le_mul_left _ (h n).1
    _ = (C * C * 2 ^ d) * v n := by ring

theorem VolumeDoubling.iterate {v : ℕ → ℕ} {D : ℕ}
    (h : VolumeDoubling v D) (k n : ℕ) :
    v (2 ^ k * n + (2 ^ k - 1)) ≤ D ^ k * v n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < 2 ^ k := by positivity
    have heq : 2 ^ (k + 1) * n + (2 ^ (k + 1) - 1) =
        2 * (2 ^ k * n + (2 ^ k - 1)) + 1 := by
      rw [pow_succ, mul_assoc, mul_left_comm (2 ^ k) 2 n, mul_add]
      omega
    rw [heq]
    exact (h _).trans (by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm]
      using Nat.mul_le_mul_left D ih)

theorem TwoSidedPolynomialGrowth.polynomialGrowth {v : ℕ → ℕ}
    (h : TwoSidedPolynomialGrowth v) : PolynomialGrowth v := by
  obtain ⟨C, d, _, hCd⟩ := h
  exact ⟨C, d, fun n => (hCd n).2⟩

/-- The published polynomial-group volume theorem, in an all-radius
integer normalization. It is proved by `polynomialVolumeTheorem` in
`NilpotentVolume.lean`; the interface is retained for modular use.

Source: E. Breuillard, *Geometry of locally compact groups of polynomial
growth and shape of large balls*, Groups Geom. Dyn. **8** (2014), 669–732,
Theorem 1.1 (Volume asymptotics), p. 670.
https://doi.org/10.4171/GGD/244
https://ems.press/content/serial-article-files/29707
Specialize to the discrete group, counting Haar measure, and the finite
symmetric generating set. The positive limit `|B(n)| / n^d` supplies
matching upper and lower bounds; enlarge one integer constant to absorb
small radii and replace `n^d` by `(n+1)^d`. The common exponent need not
be the exponent in the initial upper bound. This is distinct from Gromov's
polynomial-growth/virtual-nilpotence equivalence. -/
def PolynomialVolumeTheorem {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) : Prop :=
  PolynomialGrowth W.volume → TwoSidedPolynomialGrowth W.volume

/-- Doubling implies a polynomial upper bound, by the elementary
dilation lemma. This direction needs no structure theorem for groups. -/
theorem polynomialGrowth_of_volumeDoubling {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) {D : ℕ} (hD : VolumeDoubling W.volume D) :
    PolynomialGrowth W.volume := by
  apply polynomialGrowth_of_dilation_bound W.volume W.volume_mono (D ^ 3) 0
  intro n _
  exact (W.volume_mono (show 5 * n ≤ 2 ^ 3 * n + (2 ^ 3 - 1) by omega)).trans
    (hD.iterate 3 n)

end RecurrentSections
