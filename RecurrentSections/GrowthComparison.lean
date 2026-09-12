/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Growth
import RecurrentSections.WordComparison

/-! # Polynomial growth and finite-index comparison

These group-theoretic comparisons are independent of the recurrence and
Borel construction modules.
-/

namespace RecurrentSections

/-- Polynomial upper bounds are preserved by multiplicative changes of
volume and linear changes of radius. No monotonicity is required. -/
theorem PolynomialGrowth.of_comparison {u v : ℕ → ℕ}
    (h : PolynomialGrowth u) (A B : ℕ) (hvu : ∀ n, v n ≤ A * u (B * n)) :
    PolynomialGrowth v := by
  obtain ⟨C, d, hC⟩ := h
  refine ⟨A * C * (B + 1) ^ d, d, fun n => ?_⟩
  calc
    v n ≤ A * u (B * n) := hvu n
    _ ≤ A * (C * (B * n + 1) ^ d) := Nat.mul_le_mul_left A (hC _)
    _ ≤ A * (C * ((B + 1) * (n + 1)) ^ d) := by gcongr; nlinarith
    _ = A * C * (B + 1) ^ d * (n + 1) ^ d := by rw [mul_pow]; ring

/-- Polynomial growth is independent of passage to a finite-index subgroup
and of the finite word metrics chosen on the two groups. -/
theorem polynomialGrowth_iff_subgroup {G : Type*} [Group G] [DecidableEq G]
    (W : WordGeometry G) (N : Subgroup G) [N.FiniteIndex] (V : WordGeometry N) :
    PolynomialGrowth W.volume ↔ PolynomialGrowth V.volume := by
  obtain ⟨L, _, hL⟩ := V.exists_volume_le_of_injective W N.subtype Subtype.val_injective
  obtain ⟨A, B, _, _, hAB⟩ := W.exists_volume_le_subgroup N V
  constructor
  · intro h
    exact h.of_comparison 1 L (by simpa using hL)
  · intro h
    exact h.of_comparison A B hAB

end RecurrentSections
