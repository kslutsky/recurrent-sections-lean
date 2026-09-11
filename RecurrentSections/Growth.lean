/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic

/-! # The elementary growth obstruction

This file uses natural-number-valued growth functions. No group structure
is needed for the dilation lemma or for the construction of adverse radii.
-/

namespace RecurrentSections

/-- A polynomial upper bound, including the value at radius zero. -/
def PolynomialGrowth (v : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, v n ≤ C * (n + 1) ^ d

/-- A bounded dilation ratio on a tail forces a polynomial upper bound.
The factor five is convenient but has no mathematical significance. -/
theorem polynomialGrowth_of_dilation_bound (v : ℕ → ℕ)
    (hv : Monotone v) (K M : ℕ)
    (hbound : ∀ m, M ≤ m → v (5 * m) ≤ K * v m) :
    PolynomialGrowth v := by
  have hK : K ≤ 2 ^ K := by
    clear hbound
    induction K with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ k := by positivity
      omega
  refine ⟨v (5 * (M + 1)), K, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 5 * (M + 1)
    · exact (hv (by omega)).trans (Nat.le_mul_of_pos_right _ (by positivity))
    · let m := n / 5 + 1
      have hmM : M ≤ m := by dsimp [m]; omega
      have hmn : m < n := by dsimp [m]; omega
      have hn5 : n ≤ 5 * m := by dsimp [m]; omega
      have hm2 : 2 * (m + 1) ≤ n + 1 := by dsimp [m]; omega
      calc
        v n ≤ v (5 * m) := hv hn5
        _ ≤ K * v m := hbound m hmM
        _ ≤ K * (v (5 * (M + 1)) * (m + 1) ^ K) :=
          Nat.mul_le_mul_left K (ih m hmn)
        _ ≤ 2 ^ K * (v (5 * (M + 1)) * (m + 1) ^ K) :=
          Nat.mul_le_mul_right _ hK
        _ = v (5 * (M + 1)) * (2 * (m + 1)) ^ K := by rw [mul_pow]; ring
        _ ≤ v (5 * (M + 1)) * (n + 1) ^ K := by gcongr

/-- For growth without a polynomial bound, dilation ratios are unbounded
on every tail. Positivity is not needed for this implication. -/
theorem unbounded_dilation (v : ℕ → ℕ) (hv : Monotone v)
    (hpoly : ¬ PolynomialGrowth v) (K M : ℕ) :
    ∃ m, M ≤ m ∧ K * v m < v (5 * m) := by
  by_contra! h
  exact hpoly (polynomialGrowth_of_dilation_bound v hv K M h)

/-- Adverse radii can be chosen strictly increasingly, and above any
specified lower bound depending on the stage and previous radius. -/
theorem exists_adverse_scales (v : ℕ → ℕ) (hv : Monotone v)
    (hpoly : ¬ PolynomialGrowth v) (q : ℕ → ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      (∀ n, 0 < m n) ∧
      (∀ n, 2 ^ (n + 2) * v (m n) < v (5 * m n)) ∧
      q 0 0 ≤ m 0 ∧ (∀ n, q (n + 1) (m n) ≤ m (n + 1)) := by
  classical
  have hex (n M : ℕ) := unbounded_dilation v hv hpoly (2 ^ (n + 2)) M
  let pick (n M : ℕ) := Classical.choose (hex n M)
  have hpick (n M : ℕ) :
      M ≤ pick n M ∧ 2 ^ (n + 2) * v (pick n M) < v (5 * pick n M) :=
    Classical.choose_spec (hex n M)
  let m : ℕ → ℕ := fun n => Nat.rec
    (pick 0 (max 1 (q 0 0)))
    (fun k prev => pick (k + 1) (max (prev + 1) (q (k + 1) prev))) n
  have hzero : m 0 = pick 0 (max 1 (q 0 0)) := rfl
  have hsucc (n : ℕ) :
      m (n + 1) = pick (n + 1) (max (m n + 1) (q (n + 1) (m n))) := rfl
  have hstep (n : ℕ) : m n < m (n + 1) := by
    rw [hsucc]
    have := (hpick (n + 1) (max (m n + 1) (q (n + 1) (m n)))).1
    omega
  have hmono : StrictMono m := strictMono_nat_of_lt_succ hstep
  refine ⟨m, hmono, ?_, ?_, ?_, ?_⟩
  · intro n
    have hpos : 0 < m 0 := by
      rw [hzero]
      have := (hpick 0 (max 1 (q 0 0))).1
      omega
    exact lt_of_lt_of_le hpos (hmono.monotone (Nat.zero_le n))
  · intro n
    cases n with
    | zero => exact (hpick 0 (max 1 (q 0 0))).2
    | succ n => exact (hpick (n + 1) (max (m n + 1) (q (n + 1) (m n)))).2
  · exact (le_max_right _ _).trans (hpick 0 (max 1 (q 0 0))).1
  · intro n
    exact (le_max_right _ _).trans
      (hpick (n + 1) (max (m n + 1) (q (n + 1) (m n)))).1

end RecurrentSections
