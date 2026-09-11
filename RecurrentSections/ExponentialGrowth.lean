/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordGeometry
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RecurrentSections

open Filter
open scoped Topology Pointwise

/-- Subexponential growth in the usual logarithmic normalization. -/
def SubexponentialGrowth (v : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => Real.log (v n : ℝ) / n) atTop (𝓝 0)

variable {G : Type*} [Group G] [DecidableEq G]

namespace WordGeometry

theorem volume_submultiplicative (W : WordGeometry G) (m n : ℕ) :
    W.volume (m + n) ≤ W.volume m * W.volume n := by
  simpa only [volume, ball, pow_add] using
    (Finset.card_mul_le (s := W.generators ^ m) (t := W.generators ^ n))

theorem logVolume_nonneg (W : WordGeometry G) (n : ℕ) :
    0 ≤ Real.log (W.volume n : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast W.volume_pos n

theorem logVolume_subadditive (W : WordGeometry G) :
    Subadditive (fun n => Real.log (W.volume n : ℝ)) := by
  intro m n
  have hm : (0 : ℝ) < W.volume m := by exact_mod_cast W.volume_pos m
  have hn : (0 : ℝ) < W.volume n := by exact_mod_cast W.volume_pos n
  calc
    Real.log (W.volume (m + n) : ℝ) ≤ Real.log ((W.volume m : ℝ) * W.volume n) := by
      apply Real.log_le_log (by exact_mod_cast W.volume_pos (m + n))
      exact_mod_cast W.volume_submultiplicative m n
    _ = _ := Real.log_mul hm.ne' hn.ne'

theorem logVolume_div_bddBelow (W : WordGeometry G) :
    BddBelow (Set.range fun n : ℕ => Real.log (W.volume n : ℝ) / n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (W.logVolume_nonneg n) (Nat.cast_nonneg n)⟩

/-- The word-volume entropy supplied by Fekete's lemma. -/
noncomputable def growthEntropy (W : WordGeometry G) : ℝ :=
  W.logVolume_subadditive.lim

theorem tendsto_growthEntropy (W : WordGeometry G) :
    Tendsto (fun n : ℕ => Real.log (W.volume n : ℝ) / n) atTop (𝓝 W.growthEntropy) :=
  W.logVolume_subadditive.tendsto_lim W.logVolume_div_bddBelow

theorem growthEntropy_nonneg (W : WordGeometry G) : 0 ≤ W.growthEntropy := by
  exact ge_of_tendsto W.tendsto_growthEntropy
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (W.logVolume_nonneg n) (Nat.cast_nonneg n))

theorem growthEntropy_mul_le_logVolume (W : WordGeometry G) (n : ℕ) :
    W.growthEntropy * n ≤ Real.log (W.volume n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simpa using W.logVolume_nonneg 0
  · have h := W.logVolume_subadditive.lim_le_div W.logVolume_div_bddBelow hn
    exact (le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).mp h

theorem exp_growthEntropy_le_volume (W : WordGeometry G) (n : ℕ) :
    Real.exp (W.growthEntropy * n) ≤ W.volume n := by
  simpa only [Real.exp_log (show (0 : ℝ) < W.volume n by exact_mod_cast W.volume_pos n)]
    using Real.exp_le_exp.mpr (W.growthEntropy_mul_le_logVolume n)

theorem volume_le_exp (W : WordGeometry G) (n : ℕ) :
    (W.volume n : ℝ) ≤ Real.exp ((Real.log (W.volume 1 : ℝ) + 1) * n) := by
  have hsub := W.logVolume_subadditive.apply_mul_add_le n 1 0
  have hz : W.volume 0 = 1 := by simp [volume, ball]
  simp only [mul_one, add_zero, hz, Nat.cast_one, Real.log_one, add_zero] at hsub
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : Real.log (W.volume n : ℝ) ≤ (Real.log (W.volume 1 : ℝ) + 1) * n := by
    nlinarith
  simpa only [Real.exp_log (show (0 : ℝ) < W.volume n by exact_mod_cast W.volume_pos n)]
    using Real.exp_le_exp.mpr hlog

theorem subexponentialGrowth_iff_entropy_zero (W : WordGeometry G) :
    SubexponentialGrowth W.volume ↔ W.growthEntropy = 0 := by
  constructor
  · intro h
    exact tendsto_nhds_unique W.tendsto_growthEntropy h
  · intro h
    simpa only [SubexponentialGrowth, h] using W.tendsto_growthEntropy

end WordGeometry
end RecurrentSections
