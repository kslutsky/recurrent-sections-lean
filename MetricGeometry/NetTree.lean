/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import MetricGeometry.FiniteNets
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # A common tree of finite nets

The distance-coordinate construction in Gromov's common compact embedding
proof. See Gromov (1981), Section 6, and Lang, *Notes on Rectifiability*,
Theorem 1.3. The tree and the estimates are independent of groups.
-/

set_option backward.isDefEq.respectTransparency false

namespace MetricGeometry
noncomputable section
open Set Filter Topology Metric

/-- Nodes at level `n` in a tree with prescribed finite branching. -/
def NetNode (N : ℕ → ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => NetNode N n × Fin (N n)

instance netNodeFintype (N : ℕ → ℕ) : ∀ n, Fintype (NetNode N n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := netNodeFintype N n; inferInstanceAs (Fintype (NetNode N n × Fin (N n)))

/-- All nodes up to a fixed level. -/
abbrev NetCap (N : ℕ → ℕ) (n : ℕ) := Σ k : Fin (n + 1), NetNode N k

/-- Truncate a node at level `n`, keeping earlier nodes unchanged. -/
def netCut (N : ℕ → ℕ) (n : ℕ) : ∀ m, NetNode N m → NetCap N n
  | 0, p => ⟨⟨0, by omega⟩, p⟩
  | m + 1, p => if h : m + 1 ≤ n then ⟨⟨m + 1, by omega⟩, p⟩
      else netCut N n m p.1

@[simp] theorem netCut_of_le (N : ℕ → ℕ) {n m : ℕ} (h : m ≤ n)
    (p : NetNode N m) : netCut N n m p = ⟨⟨m, by omega⟩, p⟩ := by
  cases m with
  | zero => rfl
  | succ m => simp [netCut, h]

/-- Geometric control of each edge bounds the distance to every truncation. -/
theorem dist_netCut_le {A : Type*} [PseudoMetricSpace A] (N : ℕ → ℕ)
    (c : ∀ n, NetNode N n → A) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hs : ∀ n, e (n + 1) = e n / 2)
    (hc : ∀ n (p : NetNode N (n + 1)), dist (c (n + 1) p) (c n p.1) ≤ 2 * e n)
    (n m : ℕ) (p : NetNode N m) :
    dist (c m p) (c (netCut N n m p).1 (netCut N n m p).2) ≤ 4 * e n := by
  have aux : ∀ m, n ≤ m → ∀ p : NetNode N m,
      dist (c m p) (c (netCut N n m p).1 (netCut N n m p).2) ≤
        4 * e n - 4 * e m := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro p; rw [netCut_of_le N (le_refl n)]; simp
    | succ m hnm ih =>
      intro p
      have hgt : ¬m + 1 ≤ n := by omega
      rw [show netCut N n (m + 1) p = netCut N n m p.1 from dif_neg hgt]
      have ht := dist_triangle (c (m + 1) p) (c m p.1)
        (c (netCut N n m p.1).1 (netCut N n m p.1).2)
      have hi := ih p.1
      have hh := hc m p
      rw [hs m]
      linarith
  by_cases h : m ≤ n
  · rw [netCut_of_le N h]; simp only [dist_self]; exact mul_nonneg (by norm_num) (he n)
  · have hh := aux m (by omega) p
    linarith [he m]

/-- A finite set with at most `M` points can be padded to `M+1` labels. -/
theorem exists_net_labels {A : Type*} [Nonempty A] (S : Finset A) {M : ℕ}
    (hS : S.card ≤ M) : ∃ f : Fin (M + 1) → A, ∀ x ∈ S, x ∈ range f := by
  classical
  let f : Fin (M + 1) → A := fun i =>
    if h : i.val < S.card then (S.equivFin.symm ⟨i.val, h⟩).val else Classical.ofNonempty
  refine ⟨f, fun x hx => ?_⟩
  let j := S.equivFin ⟨x, hx⟩
  refine ⟨⟨j.val, by have := j.isLt; omega⟩, ?_⟩
  simp [f, j.isLt, j]

/-- Refine a node by a labelled global net, rejecting children too far
from their parent. Rejected labels repeat the parent. -/
def netCenters {A : Type*} [PseudoMetricSpace A] (a : A) (N : ℕ → ℕ)
    (e : ℕ → ℝ) (q : ∀ n, Fin (N n) → A) : ∀ n, NetNode N n → A
  | 0, _ => a
  | n + 1, p => if dist (q n p.2) (netCenters a N e q n p.1) ≤ 2 * e n
      then q n p.2 else netCenters a N e q n p.1

theorem netCenters_step {A : Type*} [PseudoMetricSpace A] (a : A) (N : ℕ → ℕ)
    (e : ℕ → ℝ) (q : ∀ n, Fin (N n) → A) (he : ∀ n, 0 ≤ e n)
    (n : ℕ) (p : NetNode N (n + 1)) :
    dist (netCenters a N e q (n + 1) p) (netCenters a N e q n p.1) ≤ 2 * e n := by
  dsimp only [netCenters]
  split_ifs with h
  · exact h
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (he n)

theorem netCenters_cover {A : Type*} [PseudoMetricSpace A] (a : A) (N : ℕ → ℕ)
    (e : ℕ → ℝ) (q : ∀ n, Fin (N n) → A)
    (he : ∀ n, e (n + 1) ≤ e n) (hbase : ∀ x, dist x a ≤ e 0)
    (hq : ∀ n x, ∃ i, dist x (q n i) ≤ e (n + 1)) :
    ∀ n x, ∃ p, dist x (netCenters a N e q n p) ≤ e n := by
  intro n
  induction n with
  | zero => intro x; exact ⟨(), hbase x⟩
  | succ n ih =>
    intro x
    obtain ⟨p, hp⟩ := ih x
    obtain ⟨i, hi⟩ := hq n x
    have hclose : dist (q n i) (netCenters a N e q n p) ≤ 2 * e n := by
      have ht := dist_triangle_left (q n i) (netCenters a N e q n p) x
      linarith [he n]
    refine ⟨(p, i), ?_⟩
    simpa only [netCenters, if_pos hclose] using hi

end
end MetricGeometry
