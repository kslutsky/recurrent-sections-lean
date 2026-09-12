/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Portions adapted from mathlib: Copyright (c) 2018 Sébastien Gouëzel.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import MetricGeometry.CompactModels
import MetricGeometry.NetTree

/-! # Gromov's common compact embedding theorem

We use coordinated trees of nets and the Fréchet distance embedding, as
in Gromov (1981), Section 6; see also Lang, *Notes on Rectifiability*,
Theorem 1.3. The distance-coordinate and finite-discretization arguments
adapt mathlib's Kuratowski and Arzelà--Ascoli constructions. No
Gromov--Hausdorff subsequence theorem is assumed here.
-/

set_option backward.isDefEq.respectTransparency false

namespace MetricGeometry
noncomputable section
open Set Filter Topology Metric BoundedContinuousFunction

/-- The common coordinate set, with the discrete topology. -/
def NetIndex (N : ℕ → ℕ) := Σ n, NetNode N n

instance (N : ℕ → ℕ) : TopologicalSpace (NetIndex N) := ⊥
instance (N : ℕ → ℕ) : DiscreteTopology (NetIndex N) := ⟨rfl⟩

/-- Fréchet distance coordinates of a bounded metric space. -/
def distanceCoordinates {A I : Type*} [PseudoMetricSpace A]
    [TopologicalSpace I] [DiscreteTopology I]
    (c : I → A) (C : ℝ) (hC : ∀ x y : A, dist x y ≤ C) (x : A) : I →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (fun i => dist x (c i)) C
    (by
      intro i j
      simpa only [Real.dist_eq, dist_comm] using
        (abs_dist_sub_le (c i) (c j) x).trans (hC _ _))

/-- Dense distance coordinates preserve the exact metric. -/
theorem distanceCoordinates_isometry {A I : Type*} [MetricSpace A]
    [TopologicalSpace I] [DiscreteTopology I]
    (c : I → A) (C : ℝ) (hC : ∀ x y : A, dist x y ≤ C)
    (hc : DenseRange c) : Isometry (distanceCoordinates c C hC) := by
  refine Isometry.of_dist_eq fun x y => le_antisymm ?_ ?_
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).2
    intro i
    exact abs_dist_sub_le x y (c i)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 hc x (ε / 2) (by positivity)
    have ht := dist_triangle_right x y (c i)
    have hd := BoundedContinuousFunction.dist_coe_le_dist
      (f := distanceCoordinates c C hC x) (g := distanceCoordinates c C hC y) i
    change dist (dist x (c i)) (dist y (c i)) ≤ _ at hd
    rw [Real.dist_eq] at hd
    have hab := le_abs_self (dist y (c i) - dist x (c i))
    rw [abs_sub_comm] at hab
    linarith

/-- A uniformly bounded family of functions whose coordinates are
uniformly approximable by finite truncations is totally bounded. -/
theorem totallyBounded_tree_coordinates (N : ℕ → ℕ) (C : ℝ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (S : Set (NetIndex N →ᵇ ℝ))
    (hbound : ∀ f ∈ S, ∀ p, f p ∈ Icc 0 C)
    (hcut : ∀ f ∈ S, ∀ n (p : NetIndex N),
      dist (f p) (f ⟨(netCut N n p.1 p.2).1, (netCut N n p.1 p.2).2⟩) ≤ 4 * e n) :
    TotallyBounded S := by
  classical
  refine Metric.totallyBounded_of_finite_discretization fun ε hε => ?_
  obtain ⟨n, hn⟩ := (eventually_atTop.1 ((tendsto_order.1 he).2 (ε / 32) (by positivity)))
  have hen : e n < ε / 32 := hn n le_rfl
  obtain ⟨t, _, htfin, ht⟩ :=
    finite_cover_balls_of_compact (isCompact_Icc : IsCompact (Icc (0 : ℝ) C))
      (e := ε / 8) (by positivity)
  let := htfin.fintype
  have hpick : ∀ y : Icc (0 : ℝ) C, ∃ z : t, dist y.val z.val < ε / 8 := by
    intro y
    obtain ⟨z, hz, hzy⟩ := mem_iUnion₂.1 (ht y.property)
    exact ⟨⟨z, hz⟩, hzy⟩
  choose pick hpick using hpick
  let code : S → NetCap N n → t := fun f p =>
    pick ⟨f.val ⟨p.1, p.2⟩, hbound f.val f.property _⟩
  refine ⟨NetCap N n → t, inferInstance, code, ?_⟩
  intro f g hfg
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (show 0 ≤ ε / 2 by positivity)).2 ?_)
    (by linarith : ε / 2 < ε)
  intro p
  let q := netCut N n p.1 p.2
  let z : NetIndex N := ⟨q.1, q.2⟩
  have hc : (code f q).val = (code g q).val := congrArg (fun F => (F q).val) hfg
  have hf := hpick ⟨f.val z, hbound _ f.property _⟩
  have hg := hpick ⟨g.val z, hbound _ g.property _⟩
  change dist (f.val z) (code f q).val < ε / 8 at hf
  change dist (g.val z) (code g q).val < ε / 8 at hg
  rw [← hc] at hg
  have hmid := dist_triangle_right (f.val z) (g.val z) (code f q).val
  have hleft := hcut _ f.property n p
  have hright := hcut _ g.property n p
  have htri := dist_triangle4_right (f.val p) (g.val p) (f.val z) (g.val z)
  change dist (f.val p) (f.val z) ≤ 4 * e n at hleft
  change dist (g.val p) (g.val z) ≤ 4 * e n at hright
  linarith

/-- A uniformly coverable, uniformly bounded family admits exact
isometric embeddings into one compact metric space. The individual
spaces need not be complete or compact. -/
theorem exists_common_compact_embedding {ι : Type*} (A : ι → Type*) [∀ n, MetricSpace (A n)]
    (hne : ∀ n, Nonempty (A n))
    (hdiam : ∃ C : ℝ, ∀ n (x y : A n), dist x y ≤ C)
    (hcover : UniformlyCoverable A) :
    ∃ (K : Type) (metric : MetricSpace K),
      letI := metric
      CompactSpace K ∧ ∃ f : ∀ n, A n → K, ∀ n, Isometry (f n) := by
  classical
  let := hne
  let : ∀ n, Inhabited (A n) := fun n => Classical.inhabited_of_nonempty (hne n)
  obtain ⟨C, hC⟩ := hdiam
  let D := max C 1
  let e : ℕ → ℝ := fun n => D * (1 / 2) ^ n
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hepos (n : ℕ) : 0 < e n := mul_pos hD (by positivity)
  have hes (n : ℕ) : e (n + 1) = e n / 2 := by dsimp [e]; rw [pow_succ]; ring
  have helim : Tendsto e atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1))
  choose M hM using fun n => hcover (e (n + 1)) (hepos _)
  let N : ℕ → ℕ := fun n => M n + 1
  have hq : ∀ n a, ∃ q : Fin (N n) → A a, ∀ x, ∃ i, dist x (q i) ≤ e (n + 1) := by
    intro n a
    obtain ⟨S, hS, hcov⟩ := hM n a
    obtain ⟨q, hq⟩ := exists_net_labels S hS
    refine ⟨q, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hcov x
    obtain ⟨i, rfl⟩ := hq y hy
    exact ⟨i, hxy⟩
  choose q hq using hq
  let c (a : ι) := netCenters (default : A a) N e (fun n => q n a)
  have hccov (a : ι) (n : ℕ) (x : A a) : ∃ p, dist x (c a n p) ≤ e n := by
    apply netCenters_cover _ N e (fun n => q n a) ?_ ?_ (fun n => hq n a) n x
    · intro n; rw [hes]; linarith [hepos n]
    · intro x; change dist x default ≤ D * (1 / 2) ^ 0
      simpa only [pow_zero, mul_one] using (hC a x default).trans (le_max_left C 1)
  let coord (a : ι) : NetIndex N → A a := fun p => c a p.1 p.2
  have hdense (a : ι) : DenseRange (coord a) := by
    apply Metric.denseRange_iff.2
    intro x ε hε
    obtain ⟨n, hn⟩ := eventually_atTop.1 ((tendsto_order.1 helim).2 ε hε)
    obtain ⟨p, hp⟩ := hccov a n x
    exact ⟨⟨n, p⟩, hp.trans_lt (hn n le_rfl)⟩
  let f (a : ι) := distanceCoordinates (coord a) C (hC a)
  have hf (a : ι) : Isometry (f a) := distanceCoordinates_isometry _ _ _ (hdense a)
  let S : Set (NetIndex N →ᵇ ℝ) := range (fun p : Σ a, A a => f p.1 p.2)
  have hS : TotallyBounded S := by
    apply totallyBounded_tree_coordinates N C e helim S
    · rintro _ ⟨⟨a, x⟩, rfl⟩ p
      exact ⟨dist_nonneg, hC a x (coord a p)⟩
    · rintro _ ⟨⟨a, x⟩, rfl⟩ n p
      have hc := dist_netCut_le N (c a) e (fun n => (hepos n).le) hes
        (netCenters_step _ N e (fun n => q n a) (fun n => (hepos n).le)) n p.1 p.2
      have hh := abs_dist_sub_le (coord a p)
        (coord a ⟨(netCut N n p.1 p.2).1, (netCut N n p.1 p.2).2⟩) x
      apply le_trans ?_ hc
      simpa only [f, distanceCoordinates, BoundedContinuousFunction.mkOfDiscrete,
        BoundedContinuousFunction.coe_mk, Real.dist_eq, dist_comm] using hh
  have hK : IsCompact (closure S) := hS.closure.isCompact_of_isClosed isClosed_closure
  let K := closure S
  let : CompactSpace K := isCompact_iff_compactSpace.1 hK
  refine ⟨K, inferInstance, inferInstance, ?_⟩
  let F (a : ι) (x : A a) : K := ⟨f a x, subset_closure ⟨⟨a, x⟩, rfl⟩⟩
  exact ⟨F, fun a => Isometry.of_dist_eq (fun x y => (hf a).dist_eq x y)⟩

/-- The formerly external common compact embedding input is proved. -/
theorem commonCompactEmbeddingTheorem : CommonCompactEmbeddingTheorem := by
  intro A m
  let := m
  intro _ hne hdiam hcover
  exact exists_common_compact_embedding A hne hdiam hcover

end
end MetricGeometry
