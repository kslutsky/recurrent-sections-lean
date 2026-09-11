/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.StandardInputs

namespace RecurrentSections

open Set MeasureTheory

variable {G X K : Type} [Group G] [DecidableEq G] [MulAction G X]
    [MetricSpace K] [CompactSpace K]

def returnConfig (W : WordGeometry G) (r : ℕ → ℕ) (φ : ℕ → G → K)
    (A : ℕ → Set X) (n : ℕ) (x : X) : Set (K × K) :=
  {p | ∃ g, g ∈ W.ball (3 * r n) ∧ g • x ∈ A n ∧ (φ n 1, φ n g) = p}

def returnCluster (W : WordGeometry G) (r : ℕ → ℕ) (φ : ℕ → G → K)
    (A : ℕ → Set X) (x : X) : Set (K × K) :=
  tailCluster (fun n => returnConfig W r φ A n x) ∩ {p | dist p.1 p.2 ≤ 2}

theorem returnCluster_compact (W : WordGeometry G) (r : ℕ → ℕ)
    (φ : ℕ → G → K) (A : ℕ → Set X) (x : X) :
    IsCompact (returnCluster W r φ A x) := by
  exact ((tailCluster_closed _).inter
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const)).isCompact

theorem returnCluster_nonempty (W : WordGeometry G) (r : ℕ → ℕ)
    (hr : ∀ n, 0 < r n) (φ : ℕ → G → K) (hφ : ScaledModels W r φ)
    (A : ℕ → Set X) (hnet : ∀ n x, ∃ g ∈ W.ball (r n), g • x ∈ A n)
    (x : X) : (returnCluster W r φ A x).Nonempty := by
  apply tailCluster_inter_nonempty _
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const)
  intro n
  obtain ⟨g, hg, hga⟩ := hnet n x
  have hg3 : g ∈ W.ball (3 * r n) := W.ball_mono (by omega) hg
  refine ⟨(φ n 1, φ n g), ⟨g, hg3, hga, rfl⟩, ?_⟩
  have heq := hφ n 1 g (W.one_mem_ball _) hg3
  simp only [inv_one, one_mul] at heq
  have hlen := (W.mem_ball_iff_length_le g (r n)).mp hg
  have hrpos : (0 : ℝ) < r n := by exact_mod_cast hr n
  have hle : (W.length g : ℝ) ≤ r n := by exact_mod_cast hlen
  change dist (φ n 1) (φ n g) ≤ 2
  nlinarith

theorem radius_eventually_large (r : ℕ → ℕ) (hr : StrictMono r)
    (L ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, L < ε * (r n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (L / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hnr : N ≤ r n := hn.trans (hr.id_le n)
  have hnr' : (N : ℝ) ≤ r n := by exact_mod_cast hnr
  have hL := (div_lt_iff₀ hε).mp hN
  nlinarith

omit [CompactSpace K] in
/-- The invariant-cluster step, including the margin between radii two
and three. Both coordinates are retained so no convergent-origin
subsequence is needed. This is part of the formalized construction. -/
theorem returnCluster_smul (W : WordGeometry G) (r : ℕ → ℕ)
    (hrmono : StrictMono r) (hr : ∀ n, 0 < r n)
    (φ : ℕ → G → K) (hφ : ScaledModels W r φ) (A : ℕ → Set X)
    (h : G) (x : X) : returnCluster W r φ A (h • x) = returnCluster W r φ A x := by
  have forward (h : G) (x : X) :
      returnCluster W r φ A x ⊆ returnCluster W r φ A (h • x) := by
    intro p hp
    refine ⟨?_, hp.2⟩
    apply (mem_tailCluster_iff _ p).mpr
    intro ε hε N
    let δ : ℝ := min (ε / 3) (1 / 4)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδε : δ ≤ ε / 3 := min_le_left _ _
    have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
    obtain ⟨N₀, hlarge⟩ := radius_eventually_large r hrmono (W.length h) δ hδ
    obtain ⟨n, hn, q, hq, hd⟩ := (mem_tailCluster_iff _ p).mp hp.1 δ hδ (max N N₀)
    obtain ⟨g, hg, hga, rfl⟩ := hq
    have hN : N ≤ n := (le_max_left _ _).trans hn
    have hN₀ : N₀ ≤ n := (le_max_right _ _).trans hn
    have hrpos : (0 : ℝ) < r n := by exact_mod_cast hr n
    have hfst : dist (φ n 1) p.1 < δ := (max_lt_iff.mp hd).1
    have hsnd : dist (φ n g) p.2 < δ := (max_lt_iff.mp hd).2
    have htri := dist_triangle (φ n 1) p.1 (φ n g)
    have htri' := dist_triangle p.1 p.2 (φ n g)
    have hnorm : dist (φ n 1) (φ n g) < 2 + 2 * δ := by
      have hcut : dist p.1 p.2 ≤ 2 := hp.2
      rw [dist_comm p.2 (φ n g)] at htri'
      linarith
    have hscale := hφ n 1 g (W.one_mem_ball _) hg
    simp only [inv_one, one_mul] at hscale
    have hnorm' := mul_lt_mul_of_pos_right hnorm hrpos
    have hh := hlarge n hN₀
    have hlen := W.length_mul_le g h⁻¹
    rw [W.length_inv] at hlen
    have hlen' : (W.length (g * h⁻¹) : ℝ) ≤ W.length g + W.length h := by
      exact_mod_cast hlen
    have hnew : (W.length (g * h⁻¹) : ℝ) < 3 * (r n : ℝ) := by
      have hδmul := mul_le_mul_of_nonneg_right hδ4 hrpos.le
      nlinarith
    have hg' : g * h⁻¹ ∈ W.ball (3 * r n) := by
      apply (W.mem_ball_iff_length_le _ _).mpr
      exact_mod_cast hnew.le
    have htrans := hφ n g (g * h⁻¹) hg hg'
    simp only [← mul_assoc, inv_mul_cancel, one_mul, W.length_inv] at htrans
    have hdist : dist (φ n (g * h⁻¹)) (φ n g) < δ := by
      rw [dist_comm]
      nlinarith
    refine ⟨n, hN, (φ n 1, φ n (g * h⁻¹)), ?_, ?_⟩
    · refine ⟨g * h⁻¹, hg', ?_, rfl⟩
      simpa only [mul_smul, inv_smul_smul] using hga
    · have hpairs : dist (φ n 1, φ n (g * h⁻¹)) (φ n 1, φ n g) < δ := by
        simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hdist
      have := dist_triangle (φ n 1, φ n (g * h⁻¹)) (φ n 1, φ n g) p
      linarith
  apply Set.Subset.antisymm
  · simpa using forward h⁻¹ (h • x)
  · exact forward h x

variable [MeasurableSpace X] [MeasurableConstSMul G X]
    [MeasurableSpace K] [BorelSpace K]

theorem measurableSet_returnCluster_graph (W : WordGeometry G) (r : ℕ → ℕ)
    (φ : ℕ → G → K) (A : ℕ → Set X) (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet {p : X × (K × K) | p.2 ∈ returnCluster W r φ A p.1} := by
  letI := W.countable
  let B (n : ℕ) (g : G) : Set X := {x | g ∈ W.ball (3 * r n) ∧ g • x ∈ A n}
  have hB (n : ℕ) (g : G) : MeasurableSet (B n g) := by
    by_cases hg : g ∈ W.ball (3 * r n)
    · have heq : B n g = (fun x => g • x) ⁻¹' A n := by ext x; simp [B, hg]
      rw [heq]
      exact (hA n).preimage (measurable_const_smul g)
    · simp [B, hg]
  have hgraph := measurableSet_tailCluster_graph (fun n g => (φ n 1, φ n g)) B hB
  have hF (n : ℕ) (x : X) : {z | ∃ i, x ∈ B n i ∧ (φ n 1, φ n i) = z} =
      returnConfig W r φ A n x := by
    ext z
    simp only [B, returnConfig, mem_setOf_eq, and_assoc]
  simp_rw [hF] at hgraph
  have hclosed : IsClosed {p : K × K | dist p.1 p.2 ≤ 2} :=
    isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  exact hgraph.inter (hclosed.measurableSet.preimage measurable_snd)

end RecurrentSections
