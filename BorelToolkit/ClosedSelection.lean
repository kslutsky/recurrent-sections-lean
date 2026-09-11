/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import BorelToolkit.CountableSelection
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # A fixed measurable selector for closed sets

This is the standard successive-approximation proof of the
Kuratowski--Ryll-Nardzewski selection theorem. The parameter space is
arbitrary measurable; the target is a complete separable metric space.
The chosen point depends only on the closed set, not on its presentation.

Weak measurability (measurable open-hit sets) is an explicit hypothesis.
Deriving it from a Borel graph with compact sections is a different
projection theorem and is not assumed in this module.
-/

namespace BorelToolkit

open Set Filter TopologicalSpace Metric
open scoped Topology

/-- A set-valued family is weakly measurable when hitting each open
target set is a measurable condition on the parameter. -/
def WeaklyMeasurable {X K : Type*} [MeasurableSpace X] [TopologicalSpace K]
    (T : X → Set K) : Prop :=
  ∀ U : Set K, IsOpen U → MeasurableSet {x | (T x ∩ U).Nonempty}

private noncomputable def selectionRadius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

private theorem selectionRadius_pos (n : ℕ) : 0 < selectionRadius n := by
  unfold selectionRadius
  positivity

variable {K : Type*} [MetricSpace K]

private def hit (d : ℕ → K) (T : Set K) (n i : ℕ) : Prop :=
  (T ∩ ball (d i) (selectionRadius n)).Nonempty

private noncomputable def approximant (d : ℕ → K) (T : Set K) : ℕ → K
  | 0 => d (firstWitness (hit d T 0))
  | n + 1 => d (firstWitness (fun i => hit d T (n + 1) i ∧
      dist (d i) (approximant d T n) < 2 * selectionRadius n))

private theorem exists_hit (d : ℕ → K) (hd : DenseRange d)
    {T : Set K} (hT : T.Nonempty) (n : ℕ) : ∃ i, hit d T n i := by
  obtain ⟨z, hz⟩ := hT
  obtain ⟨i, hi⟩ := denseRange_iff.mp hd z (selectionRadius n) (selectionRadius_pos n)
  exact ⟨i, z, hz, by simpa [mem_ball, dist_comm] using hi⟩

private theorem exists_next_hit (d : ℕ → K) (hd : DenseRange d)
    {T : Set K} (n : ℕ) (p : K)
    (hp : (T ∩ ball p (selectionRadius n)).Nonempty) :
    ∃ i, hit d T (n + 1) i ∧ dist (d i) p < 2 * selectionRadius n := by
  obtain ⟨z, hzT, hzp⟩ := hp
  obtain ⟨i, hi⟩ := denseRange_iff.mp hd z (selectionRadius (n + 1))
    (selectionRadius_pos (n + 1))
  have hzi : dist z (d i) < selectionRadius (n + 1) := by simpa [dist_comm] using hi
  refine ⟨i, ⟨z, hzT, hzi⟩, ?_⟩
  have htri := dist_triangle (d i) z p
  have hpos := selectionRadius_pos n
  have hrad : selectionRadius (n + 1) = selectionRadius n / 2 := by
    simp [selectionRadius, pow_succ, div_eq_mul_inv]
  change dist z p < selectionRadius n at hzp
  rw [dist_comm (d i) z] at htri
  rw [hrad] at hzi
  linarith

private theorem approximant_hit (d : ℕ → K) (hd : DenseRange d)
    {T : Set K} (hT : T.Nonempty) (n : ℕ) :
    (T ∩ ball (approximant d T n) (selectionRadius n)).Nonempty := by
  induction n with
  | zero => exact firstWitness_spec (exists_hit d hd hT 0)
  | succ n ih => exact (firstWitness_spec (exists_next_hit d hd n _ ih)).1

private theorem approximant_step (d : ℕ → K) (hd : DenseRange d)
    {T : Set K} (hT : T.Nonempty) (n : ℕ) :
    dist (approximant d T (n + 1)) (approximant d T n) < 2 * selectionRadius n :=
  (firstWitness_spec (exists_next_hit d hd n _ (approximant_hit d hd hT n))).2

private theorem approximant_cauchy (d : ℕ → K) (hd : DenseRange d)
    {T : Set K} (hT : T.Nonempty) : CauchySeq (approximant d T) := by
  apply cauchySeq_of_le_geometric (1 / 2) 2 (by norm_num)
  intro n
  simpa [selectionRadius, dist_comm] using (approximant_step d hd hT n).le

variable [SeparableSpace K] [Nonempty K]

/-- One fixed set selector, using a fixed dense sequence in the target.
Its value on the empty set is immaterial. -/
noncomputable def closedSelector (T : Set K) : K :=
  limUnder atTop (approximant (denseSeq K) T)

theorem closedSelector_mem [CompleteSpace K] {T : Set K}
    (hclosed : IsClosed T) (hT : T.Nonempty) : closedSelector T ∈ T := by
  have ha := (approximant_cauchy (denseSeq K) (denseRange_denseSeq K) hT).tendsto_limUnder
  have hsmall (n : ℕ) : infDist (approximant (denseSeq K) T n) T ≤ selectionRadius n := by
    obtain ⟨z, hzT, hz⟩ := approximant_hit (denseSeq K) (denseRange_denseSeq K) hT n
    exact (infDist_le_dist_of_mem hzT).trans (by simpa [mem_ball, dist_comm] using hz.le)
  have hz : Tendsto (fun n => infDist (approximant (denseSeq K) T n) T) atTop (𝓝 0) :=
    squeeze_zero (fun _ => infDist_nonneg) hsmall
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hc := ((continuous_infDist_pt T).tendsto (closedSelector T)).comp ha
  exact (hclosed.mem_iff_infDist_zero hT).mpr (tendsto_nhds_unique hc hz)

variable [MeasurableSpace K] [BorelSpace K]

omit [SeparableSpace K] [Nonempty K] in
private theorem measurable_approximant {X : Type*} [MeasurableSpace X]
    (d : ℕ → K) (T : X → Set K) (hT : WeaklyMeasurable T) (n : ℕ) :
    Measurable (fun x => approximant d (T x) n) := by
  have hhit (n i : ℕ) : MeasurableSet {x | hit d (T x) n i} :=
    hT _ isOpen_ball
  induction n with
  | zero =>
    exact (measurable_of_countable d).comp
      (measurable_firstWitness (fun i x => hit d (T x) 0 i) (hhit 0))
  | succ n ih =>
    apply (measurable_of_countable d).comp
    apply measurable_firstWitness
    intro i
    exact (hhit (n + 1) i).inter (measurableSet_lt
      ((continuous_const.dist continuous_id).measurable.comp ih) measurable_const)

/-- The fixed limiting map is measurable for every weakly measurable
family of nonempty sets. For closed values, `closedSelector_mem` gives
membership and hence the Kuratowski--Ryll-Nardzewski selector. Standard
Borelness of the parameter space is unnecessary. -/
theorem measurable_closedSelector [CompleteSpace K]
    {X : Type*} [MeasurableSpace X] (T : X → Set K)
    (hT : WeaklyMeasurable T) (hne : ∀ x, (T x).Nonempty) :
    Measurable (fun x => closedSelector (T x)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => measurable_approximant (denseSeq K) T hT n)
  apply tendsto_pi_nhds.mpr
  intro x
  exact (approximant_cauchy (denseSeq K) (denseRange_denseSeq K) (hne x)).tendsto_limUnder

/-- The usual function-valued formulation of measurable selection. -/
theorem exists_measurable_selection [CompleteSpace K]
    {X : Type*} [MeasurableSpace X] (T : X → Set K)
    (hT : WeaklyMeasurable T) (hclosed : ∀ x, IsClosed (T x))
    (hne : ∀ x, (T x).Nonempty) :
    ∃ f : X → K, Measurable f ∧ ∀ x, f x ∈ T x :=
  ⟨fun x => closedSelector (T x), measurable_closedSelector T hT hne,
    fun x => closedSelector_mem (hclosed x) (hne x)⟩

omit [MeasurableSpace K] [BorelSpace K] in
/-- A basic normalization check for the fixed selector. -/
@[simp] theorem closedSelector_singleton [CompleteSpace K] (x : K) :
    closedSelector ({x} : Set K) = x := by
  exact closedSelector_mem isClosed_singleton (singleton_nonempty x)

end BorelToolkit
