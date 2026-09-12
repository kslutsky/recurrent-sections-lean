/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordGeometry
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.SpecificLimits.Basic

namespace RecurrentSections

open MeasureTheory
open scoped Pointwise ENNReal

variable {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]

/-- Freeness stated as injectivity of each orbit map. -/
def FreeAction : Prop := ∀ x : X, Function.Injective (fun g : G => g • x)

theorem separated_translates_disjoint (W : WordGeometry G) (m : ℕ)
    {C : Set X} (hfree : FreeAction (G := G) (X := X))
    (hsep : Separated W (m + m) C) :
    (↑(W.ball m) : Set G).PairwiseDisjoint (fun g => g • C) := by
  intro f hf g hg hfg
  apply Set.disjoint_left.mpr
  rintro z ⟨c, hc, hfc⟩ ⟨d, hd, hgd⟩
  change f • c = z at hfc
  change g • d = z at hgd
  have hcd : c = d := hsep c hc d hd (g⁻¹ * f)
    (W.mul_mem_ball (W.inv_mem_ball hg) hf) (by
      rw [mul_smul, hfc, ← hgd, inv_smul_smul])
  subst d
  exact hfg (hfree c (hfc.trans hgd.symm))

variable [MeasurableSpace X] [MeasurableConstSMul G X]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

omit [DecidableEq G] [MeasurableConstSMul G X] [IsProbabilityMeasure μ] in
/-- The union bound for an arbitrary finite family of translates. -/
theorem measure_finite_translates_le (H : Finset G) (C : Set X) :
    μ (⋃ g ∈ H, g • C) ≤ (H.card : ℝ≥0∞) * μ C := by
  simpa only [measure_smul, Finset.sum_const, nsmul_eq_mul] using
    (measure_biUnion_finset_le (μ := μ) H (fun g => g • C))

omit [DecidableEq G] in
/-- Disjoint translates of a measurable set occupy at most total mass one. -/
theorem card_mul_measure_le_one (F : Finset G) {C : Set X}
    (hC : MeasurableSet C)
    (hdisj : (↑F : Set G).PairwiseDisjoint (fun g => g • C)) :
    (F.card : ℝ≥0∞) * μ C ≤ 1 := by
  have hm (g : G) : MeasurableSet (g • C) :=
    (measurableEmbedding_const_smul g).measurableSet_image.mpr hC
  have heq := measure_biUnion_finset (μ := μ) hdisj (fun g _ => hm g)
  have hle : μ (⋃ g ∈ F, g • C) ≤ 1 := prob_le_one
  simpa only [heq, measure_smul, Finset.sum_const, nsmul_eq_mul] using hle

/-- The packing estimate is proved here, not supplied as a black box. -/
theorem measure_neighborhood_le (W : WordGeometry G) (m : ℕ) {C : Set X}
    (hfree : FreeAction (G := G) (X := X)) (hC : MeasurableSet C)
    (hsep : Separated W (10 * m) C) :
    μ (neighborhood W m C) ≤ (W.volume m : ℝ≥0∞) / W.volume (5 * m) := by
  have hdisj := separated_translates_disjoint W (5 * m) hfree
    (by simpa [show 5 * m + 5 * m = 10 * m by omega] using hsep)
  have hmass := card_mul_measure_le_one μ (W.ball (5 * m)) hC hdisj
  have hpos : (W.volume (5 * m) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (W.volume_pos (5 * m)).ne'
  have hfin : (W.volume (5 * m) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hc : μ C ≤ 1 / (W.volume (5 * m) : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).mpr
    simpa [WordGeometry.volume, mul_comm] using hmass
  calc
    μ (neighborhood W m C) ≤ (W.volume m : ℝ≥0∞) * μ C :=
      measure_finite_translates_le μ (W.ball m) C
    _ ≤ (W.volume m : ℝ≥0∞) * (1 / (W.volume (5 * m) : ℝ≥0∞)) :=
      mul_le_mul_right hc _
    _ = _ := by simp [div_eq_mul_inv]

/-- The geometric budget leaves half the probability space uncovered. -/
theorem geometric_budget :
    (∑' n : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) = (2 : ℝ≥0∞)⁻¹ := by
  simp_rw [pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- No family whose measures fit this budget can cover a probability space. -/
theorem not_cover_of_geometric_budget (A : ℕ → Set X)
    (hA : ∀ n, μ (A n) ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2)) :
    (⋃ n, A n) ≠ Set.univ := by
  intro hcover
  have hle : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ := calc
    (1 : ℝ≥0∞) = μ (⋃ n, A n) := by rw [hcover, measure_univ]
    _ ≤ ∑' n, μ (A n) := measure_iUnion_le _
    _ ≤ ∑' n, (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := ENNReal.tsum_le_tsum hA
    _ = _ := geometric_budget
  norm_num at hle

end RecurrentSections
