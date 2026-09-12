/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.ExponentialGrowth
import RecurrentSections.Characterization
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

namespace RecurrentSections

open MeasureTheory Filter
open scoped Pointwise ENNReal Topology

variable {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]
    [MeasurableSpace X] [MeasurableConstSMul G X]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

/-- Packing with independent neighborhood and disjointness radii. -/
theorem measure_neighborhood_le_of_separated (W : WordGeometry G) (a b R : ℕ)
    (hb : b + b ≤ R) {C : Set X}
    (hfree : FreeAction (G := G) (X := X)) (hC : MeasurableSet C)
    (hsep : Separated W R C) :
    μ (neighborhood W a C) ≤ (W.volume a : ℝ≥0∞) / W.volume b := by
  have hsep' : Separated W (b + b) C := by
    intro x hx y hy g hg hxy
    exact hsep x hx y hy g (W.ball_mono hb hg) hxy
  have hmass := card_mul_measure_le_one μ (W.ball b) hC
    (separated_translates_disjoint W b hfree hsep')
  have hpos : (W.volume b : ℝ≥0∞) ≠ 0 := by exact_mod_cast (W.volume_pos b).ne'
  have hfin : (W.volume b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hc : μ C ≤ 1 / (W.volume b : ℝ≥0∞) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).mpr
    simpa only [WordGeometry.volume, mul_comm] using hmass
  calc
    μ (neighborhood W a C) ≤ (W.volume a : ℝ≥0∞) * μ C :=
      measure_finite_translates_le μ (W.ball a) C
    _ ≤ (W.volume a : ℝ≥0∞) * (1 / (W.volume b : ℝ≥0∞)) :=
      mul_le_mul_right hc _
    _ = _ := by simp [div_eq_mul_inv]

omit [Group G] [DecidableEq G] [MulAction G X]
    [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in
/-- The first Borel–Cantelli lemma excludes everywhere frequent membership.
No measurability of the individual sets is needed for this outer-measure form. -/
theorem not_frequent_everywhere_of_summable_measure (A : ℕ → Set X)
    (hsum : (∑' n, μ (A n)) ≠ ⊤) :
    ¬ ∀ x : X, ∀ N : ℕ, ∃ n ≥ N, x ∈ A n := by
  intro h
  have hbc := measure_setOfPred_frequently_eq_zero (μ := μ)
    (p := fun n x => x ∈ A n) hsum
  have heq : {x | ∃ᶠ n in atTop, x ∈ A n} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact frequently_atTop.mpr (h x)
  rw [heq, measure_univ] at hbc
  exact one_ne_zero hbc

omit [SMulInvariantMeasure G X μ] [MeasurableConstSMul G X] in
/-- A summable sequence of small-neighborhood measures precludes recurrence.
The radii need not increase in this general obstruction. -/
theorem not_recurrent_of_summable_neighborhoods (W : WordGeometry G)
    (r : ℕ → ℕ) (C : ℕ → Set X) (ε : ℝ) (hε : 0 < ε)
    (hsum : (∑' n, μ (neighborhood W ⌊ε * (r n : ℝ)⌋₊ (C n))) ≠ ⊤) :
    ¬ Recurrent W r C := by
  intro hrec
  apply not_frequent_everywhere_of_summable_measure μ
    (fun n => neighborhood W ⌊ε * (r n : ℝ)⌋₊ (C n)) hsum
  intro x N
  obtain ⟨n, hn, g, c, hc, hgc, hlen⟩ := hrec ε hε x N
  refine ⟨n, hn, Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩
  · exact (W.mem_ball_iff_length_le _ _).mpr (Nat.le_floor hlen.le)
  · exact ⟨c, hc, hgc⟩

include μ in
/-- The general volume-ratio obstruction for a fixed sequence of radii. -/
theorem not_recurrent_of_summable_ratios (W : WordGeometry G)
    (hfree : FreeAction (G := G) (X := X))
    (r : ℕ → ℕ) (C : ℕ → Set X)
    (hC : ∀ n, MeasurableSet (C n)) (hsep : ∀ n, Separated W (r n) (C n))
    (ε : ℝ) (hε : 0 < ε)
    (hsum : (∑' n, (W.volume ⌊ε * (r n : ℝ)⌋₊ : ℝ≥0∞) /
      W.volume (r n / 2)) ≠ ⊤) :
    ¬ Recurrent W r C := by
  apply not_recurrent_of_summable_neighborhoods μ W r C ε hε
  apply ne_top_of_le_ne_top hsum
  apply ENNReal.tsum_le_tsum
  intro n
  exact measure_neighborhood_le_of_separated μ W _ (r n / 2) (r n)
    (by omega) hfree (hC n) (hsep n)

omit [MulAction G X] [MeasurableSpace X] [MeasurableConstSMul G X]
    [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ] in
/-- Exponential volume bounds make small-neighborhood packing ratios decay
exponentially. All real/integer rounding is included. -/
theorem exponential_ratio_bound (W : WordGeometry G) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ n : ℕ, Real.exp (a * n) ≤ W.volume n)
    (hupper : ∀ n : ℕ, (W.volume n : ℝ) ≤ Real.exp (b * n)) (R : ℕ) :
    (W.volume ⌊(a / (4 * b)) * (R : ℝ)⌋₊ : ℝ) / W.volume (R / 2) ≤
      Real.exp a * Real.exp ((-a / 4) * R) := by
  let ε := a / (4 * b)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbε : b * ε = a / 4 := by dsimp [ε]; field_simp
  have hfloor : (⌊ε * (R : ℝ)⌋₊ : ℝ) ≤ ε * R :=
    Nat.floor_le (mul_nonneg hε.le (Nat.cast_nonneg R))
  have hhalf : (R : ℝ) ≤ 2 * (R / 2 : ℕ) + 2 := by
    exact_mod_cast (show R ≤ 2 * (R / 2) + 2 by omega)
  have hexp : b * (⌊ε * (R : ℝ)⌋₊ : ℝ) - a * (R / 2 : ℕ) ≤
      a + (-a / 4) * R := by
    have h₁ := mul_le_mul_of_nonneg_left hfloor hb.le
    have h₂ := mul_le_mul_of_nonneg_left hhalf ha.le
    have heq : b * (ε * (R : ℝ)) = a / 4 * R := by rw [← mul_assoc, hbε]
    rw [heq] at h₁
    nlinarith
  calc
    (W.volume ⌊ε * (R : ℝ)⌋₊ : ℝ) / W.volume (R / 2) ≤
        Real.exp (b * (⌊ε * (R : ℝ)⌋₊ : ℝ)) / Real.exp (a * (R / 2 : ℕ)) :=
      div_le_div₀ (by positivity) (hupper _) (Real.exp_pos _) (hlower _)
    _ = Real.exp (b * (⌊ε * (R : ℝ)⌋₊ : ℝ) - a * (R / 2 : ℕ)) :=
      (Real.exp_sub _ _).symm
    _ ≤ Real.exp (a + (-a / 4) * R) := Real.exp_le_exp.mpr hexp
    _ = _ := Real.exp_add _ _

include μ in
/-- Exponential growth excludes recurrence for any schedule satisfying the
indicated summability condition; no monotonicity is assumed here. -/
theorem not_recurrent_of_exponential_bounds (W : WordGeometry G)
    (hfree : FreeAction (G := G) (X := X)) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ n : ℕ, Real.exp (a * n) ≤ W.volume n)
    (hupper : ∀ n : ℕ, (W.volume n : ℝ) ≤ Real.exp (b * n))
    (r : ℕ → ℕ) (C : ℕ → Set X)
    (hC : ∀ n, MeasurableSet (C n)) (hsep : ∀ n, Separated W (r n) (C n))
    (hsum : Summable (fun n => Real.exp ((-a / 4) * (r n : ℝ)))) :
    ¬ Recurrent W r C := by
  apply not_recurrent_of_summable_ratios μ W hfree r C hC hsep (a / (4 * b))
    (by positivity)
  have hbudget := (hsum.mul_left (Real.exp a)).tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hbudget
  apply ENNReal.tsum_le_tsum
  intro n
  have hratio := ENNReal.ofReal_le_ofReal (exponential_ratio_bound W a b ha hb hlower hupper (r n))
  simpa only [ENNReal.ofReal_div_of_pos
    (show (0 : ℝ) < W.volume (r n / 2) by exact_mod_cast W.volume_pos _),
    ENNReal.ofReal_natCast] using hratio

include μ in
/-- One recurrent sequence of measurable separated sets, at strictly
increasing integer radii in one free pmp action, forces subexponential
growth. Completeness and maximality are not required. All growth and
measure arguments are proved from mathlib; there are no external inputs. -/
theorem subexponentialGrowth_of_one_recurrent_sequence (W : WordGeometry G)
    (hfree : FreeAction (G := G) (X := X))
    (r : ℕ → ℕ) (hr : StrictMono r) (C : ℕ → Set X)
    (hC : ∀ n, MeasurableSet (C n)) (hsep : ∀ n, Separated W (r n) (C n))
    (hrec : Recurrent W r C) : SubexponentialGrowth W.volume := by
  apply W.subexponentialGrowth_iff_entropy_zero.mpr
  by_contra hn
  have ha : 0 < W.growthEntropy := lt_of_le_of_ne W.growthEntropy_nonneg (Ne.symm hn)
  have hb : 0 < Real.log (W.volume 1 : ℝ) + 1 := by
    have := W.logVolume_nonneg 1
    linarith
  have hsum : Summable (fun n => Real.exp ((-W.growthEntropy / 4) * (r n : ℝ))) :=
    Real.summable_exp_nat_mul_of_ge (by linarith)
      (fun n => by exact_mod_cast hr.id_le n)
  exact not_recurrent_of_exponential_bounds μ W hfree W.growthEntropy
    (Real.log (W.volume 1 : ℝ) + 1) ha hb W.exp_growthEntropy_le_volume
    W.volume_le_exp r C hC hsep hsum hrec

/-- Existence of one recurrent sequence; the radii may depend on the action. -/
def HasSomeRecurrentSections (W : WordGeometry G) : Prop :=
  ∃ r : ℕ → ℕ, StrictMono r ∧ (∀ n, 0 < r n) ∧
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, Separated W (r n) (C n)) ∧
      (∀ n, CompleteSection (G := G) (C n)) ∧ Recurrent W r C

include μ in
theorem subexponentialGrowth_of_some_recurrent_sections (W : WordGeometry G)
    (hfree : FreeAction (G := G) (X := X))
    (hrec : HasSomeRecurrentSections (X := X) W) : SubexponentialGrowth W.volume := by
  obtain ⟨r, hr, _, C, hC, hsep, _, hrecC⟩ := hrec
  exact subexponentialGrowth_of_one_recurrent_sequence μ W hfree r hr C hC hsep hrecC

end RecurrentSections

namespace RecurrentSections

open MeasureTheory

variable {G : Type} [Group G] [DecidableEq G]

/-- Every free standard Borel action has some recurrent sequence, with an
action-dependent increasing positive integer radius schedule. -/
def UniversalFreeSomeRecurrence (W : WordGeometry G) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X],
      FreeAction (G := G) (X := X) → HasSomeRecurrentSections (X := X) W

/-- The existential-radius universal property forces subexponential growth.
The Bernoulli test action is proved in `FreePmpModel.lean`; no external input remains. -/
theorem subexponentialGrowth_of_universalFreeSomeRecurrence (W : WordGeometry G)
    (hrec : UniversalFreeSomeRecurrence W) :
    SubexponentialGrowth W.volume := by
  let := W.countable
  obtain ⟨A⟩ := nonempty_freePmpModel G
  let := A.measurableSpace
  let := A.standardBorel
  let := A.action
  let := A.measurableAction
  let := A.probability
  let := A.invariant
  exact subexponentialGrowth_of_some_recurrent_sections A.measure W A.free
    (hrec A.Space A.free)

end RecurrentSections
