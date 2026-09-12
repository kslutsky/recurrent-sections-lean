/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Portions adapted from mathlib: Copyright (c) 2022 Sébastien Gouëzel.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic

/-! # Countable separation of analytic sets

Novikov's countable separation theorem, proved by the cylinder refinement
argument, following the Mokobodzki proof in Srivastava, *A Course on
Borel Sets*, Theorem 4.6.1. The proof extends mathlib's two-set Lusin
separation construction (file authors Sébastien Gouëzel and Felix Weilacher).
-/

set_option backward.isDefEq.respectTransparency false

namespace BorelToolkit
open Set Function Filter Topology MeasureTheory TopologicalSpace PiNat
noncomputable section

/-- A family has measurable supersets with empty intersection. -/
def MeasurablySeparatedFamily {X : Type*} [MeasurableSpace X] (s : ℕ → Set X) : Prop :=
  ∃ B : ℕ → Set X, (∀ i, MeasurableSet (B i)) ∧ (∀ i, s i ⊆ B i) ∧ ⋂ i, B i = ∅

theorem MeasurablySeparatedFamily.mono {X : Type*} [MeasurableSpace X]
    {s t : ℕ → Set X} (h : MeasurablySeparatedFamily t) (hst : ∀ i, s i ⊆ t i) :
    MeasurablySeparatedFamily s := by
  obtain ⟨B, hB, htB, hBe⟩ := h
  exact ⟨B, hB, fun i => (hst i).trans (htB i), hBe⟩

/-- Countable unions in one coordinate preserve separability. -/
theorem separatedFamily_update_iUnion {X : Type*} [MeasurableSpace X]
    (s : ℕ → Set X) (i : ℕ) (t : ℕ → Set X)
    (h : ∀ k, MeasurablySeparatedFamily (update s i (t k))) :
    MeasurablySeparatedFamily (update s i (⋃ k, t k)) := by
  classical
  choose B hBm hBs hBe using h
  let D : ℕ → Set X := fun j => if j = i then ⋃ k, B k j else ⋂ k, B k j
  refine ⟨D, fun j => ?_, fun j => ?_, ?_⟩
  · dsimp only [D]
    split_ifs
    · exact MeasurableSet.iUnion (fun k => hBm k j)
    · exact MeasurableSet.iInter (fun k => hBm k j)
  · by_cases hji : j = i
    · subst j
      simp only [D, if_pos rfl, update_self]
      exact iUnion_mono (fun k => by simpa using hBs k i)
    · simp only [D, if_neg hji, update_of_ne hji]
      exact subset_iInter (fun k => by simpa [hji] using hBs k j)
  · apply eq_empty_iff_forall_notMem.2
    intro x hx
    have hi := mem_iInter.1 hx i
    simp only [D, if_pos rfl, mem_iUnion] at hi
    obtain ⟨k, hk⟩ := hi
    have hall : x ∈ ⋂ j, B k j := by
      apply mem_iInter.2
      intro j
      by_cases hji : j = i
      · simpa [hji] using hk
      · have hj := mem_iInter.1 hx j
        simp only [D, if_neg hji, mem_iInter] at hj
        exact hj k
    simp [hBe k] at hall

/-- A nonseparable family remains nonseparable after refining one
cylinder by one more coordinate, for a suitable choice of that coordinate. -/
theorem exists_inseparable_cylinder_update {X : Type*} [MeasurableSpace X]
    (f : ℕ → (ℕ → ℕ) → X) (p : ℕ → ℕ → ℕ) (d : ℕ → ℕ) (i : ℕ)
    (h : ¬ MeasurablySeparatedFamily (fun j => f j '' cylinder (p j) (d j))) :
    ∃ k, ¬ MeasurablySeparatedFamily
      (update (fun j => f j '' cylinder (p j) (d j)) i
        (f i '' cylinder (update (p i) (d i) k) (d i + 1))) := by
  by_contra! hh
  have H := separatedFamily_update_iUnion (fun j => f j '' cylinder (p j) (d j)) i
    (fun k => f i '' cylinder (update (p i) (d i) k) (d i + 1)) hh
  rw [← image_iUnion, iUnion_cylinder_update (p i) (d i), update_eq_self] at H
  exact h H

/-- One simultaneous finite refinement of a nonseparable cylinder family. -/
theorem exists_inseparable_refinement {X : Type*} [MeasurableSpace X]
    (f : ℕ → (ℕ → ℕ) → X) (n : ℕ) (p : ℕ → ℕ → ℕ)
    (h : ¬ MeasurablySeparatedFamily (fun i => f i '' cylinder (p i) (n - i))) :
    ∃ q : ℕ → ℕ → ℕ, (∀ i, q i ∈ cylinder (p i) (n - i)) ∧
      ¬ MeasurablySeparatedFamily (fun i => f i '' cylinder (q i) (n + 1 - i)) := by
  classical
  let d (m i : ℕ) := if i < m then n + 1 - i else n - i
  have aux : ∀ m, m ≤ n + 1 → ∃ q : ℕ → ℕ → ℕ,
      (∀ i, q i ∈ cylinder (p i) (n - i)) ∧
      ¬ MeasurablySeparatedFamily (fun i => f i '' cylinder (q i) (d m i)) := by
    intro m hm
    induction m with
    | zero => exact ⟨p, fun i => self_mem_cylinder _ _, by simpa [d] using h⟩
    | succ m ih =>
      obtain ⟨q, hqp, hq⟩ := ih (by omega)
      obtain ⟨k, hk⟩ := exists_inseparable_cylinder_update f q (d m) m hq
      let q' := update q m (update (q m) (n - m) k)
      refine ⟨q', fun i => ?_, ?_⟩
      · by_cases him : i = m
        · subst i
          dsimp only [q']
          rw [update_self]
          intro j hj
          rw [update_of_ne (by omega : j ≠ n - m)]
          exact hqp m j hj
        · simpa [q', him] using hqp i
      · convert hk using 1
        apply Iff.of_eq
        congr 1
        funext i
        by_cases him : i = m
        · subst i
          simp only [q', update_self, d, lt_self_iff_false, if_false, Nat.lt_succ_self, if_true]
          congr 2
          omega
        · have hiff : i < m + 1 ↔ i < m := by omega
          simp [q', update_of_ne him, d, hiff]
  obtain ⟨q, hqp, hq⟩ := aux (n + 1) le_rfl
  refine ⟨q, hqp, ?_⟩
  convert hq using 1
  apply Iff.of_eq
  congr 1
  funext i
  congr 2
  dsimp [d]
  split_ifs with hi
  · rfl
  · omega

/-- Novikov separation for continuous images of Baire space. -/
theorem separatedFamily_ranges {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (f : ℕ → (ℕ → ℕ) → X) (hf : ∀ i, Continuous (f i))
    (hempty : ⋂ i, range (f i) = ∅) :
    MeasurablySeparatedFamily (fun i => range (f i)) := by
  classical
  by_contra h
  let A := {p : ℕ × (ℕ → ℕ → ℕ) //
    ¬ MeasurablySeparatedFamily (fun i => f i '' cylinder (p.2 i) (p.1 - i))}
  have hex (p : A) : ∃ q : A, q.1.1 = p.1.1 + 1 ∧
      ∀ i, q.1.2 i ∈ cylinder (p.1.2 i) (p.1.1 - i) := by
    obtain ⟨q, hq, hn⟩ := exists_inseparable_refinement f p.1.1 p.1.2 p.2
    exact ⟨⟨⟨p.1.1 + 1, q⟩, hn⟩, rfl, hq⟩
  choose F hFn hFp using hex
  let p0 : A := ⟨⟨0, fun _ _ => 0⟩, by simpa using h⟩
  let p (n : ℕ) : A := F^[n] p0
  have prec (n : ℕ) : p (n + 1) = F (p n) := by simp only [p, iterate_succ', comp_apply]
  have pnum (n : ℕ) : (p n).1.1 = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [prec, hFn, ih]
  have stable (i k : ℕ) : ∀ n, k + i + 1 ≤ n →
      (p n).1.2 i k = (p (k + i + 1)).1.2 i k := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have hh := hFp (p n) i k (by rw [pnum]; omega)
      rw [prec, hh, ih]
  let x (i k : ℕ) := (p (k + i + 1)).1.2 i k
  have inseparable (n : ℕ) :
      ¬ MeasurablySeparatedFamily (fun i => f i '' cylinder (x i) (n - i)) := by
    convert (p n).2 using 1
    apply Iff.of_eq
    congr 1
    funext i
    congr 1
    rw [pnum, ← mem_cylinder_iff_eq]
    intro k hk
    exact (stable i k n (by omega)).symm
  have hexne : ∃ i, f 0 (x 0) ≠ f i (x i) := by
    by_contra! heq
    have hh : f 0 (x 0) ∈ ⋂ i, range (f i) :=
      mem_iInter.2 (fun i => ⟨x i, (heq i).symm⟩)
    simp [hempty] at hh
  obtain ⟨i, hi⟩ := hexne
  have hi0 : i ≠ 0 := by rintro rfl; exact hi rfl
  obtain ⟨U, V, hU, hV, hfx, hfy, hUV⟩ := t2_separation hi
  let : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  obtain ⟨ε, hε, hbU⟩ := Metric.mem_nhds_iff.1
    ((hf 0).continuousAt.preimage_mem_nhds (hU.mem_nhds hfx))
  obtain ⟨δ, hδ, hbV⟩ := Metric.mem_nhds_iff.1
    ((hf i).continuousAt.preimage_mem_nhds (hV.mem_nhds hfy))
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (lt_min hε hδ)
    (by norm_num : (1 : ℝ) / 2 < 1)
  have hfirst : f 0 '' cylinder (x 0) (k + i - 0) ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    apply hbU
    have hh := cylinder_anti (x 0) (show k ≤ k + i - 0 by omega) hz
    exact (mem_cylinder_iff_dist_le.1 hh).trans_lt (hk.trans_le (min_le_left _ _))
  have hsecond : f i '' cylinder (x i) (k + i - i) ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    apply hbV
    have hh := cylinder_anti (x i) (show k ≤ k + i - i by omega) hz
    exact (mem_cylinder_iff_dist_le.1 hh).trans_lt (hk.trans_le (min_le_right _ _))
  apply inseparable (k + i)
  let B (j : ℕ) := if j = 0 then U else if j = i then V else univ
  refine ⟨B, fun j => ?_, fun j => ?_, ?_⟩
  · dsimp only [B]
    split_ifs
    · exact hU.measurableSet
    · exact hV.measurableSet
    · exact MeasurableSet.univ
  · by_cases hj : j = 0
    · subst j; simpa [B] using hfirst
    · by_cases hji : j = i
      · subst j; simpa [B, hi0] using hsecond
      · simp [B, hj, hji]
  · apply eq_empty_iff_forall_notMem.2
    intro z hz
    have hzU : z ∈ U := by simpa [B] using mem_iInter.1 hz 0
    have hzV : z ∈ V := by simpa [B, hi0] using mem_iInter.1 hz i
    exact Set.disjoint_left.1 hUV hzU hzV

/-- **Novikov's countable separation theorem.** Countably many analytic
sets with empty intersection have Borel supersets with empty intersection. -/
theorem analytic_countable_separation {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (s : ℕ → Set X) (hs : ∀ i, AnalyticSet (s i)) (he : ⋂ i, s i = ∅) :
    MeasurablySeparatedFamily s := by
  classical
  by_cases h : ∃ i, s i = ∅
  · obtain ⟨i, hi⟩ := h
    refine ⟨fun j => if j = i then ∅ else univ, fun j => ?_, fun j => ?_, ?_⟩
    · dsimp only; split_ifs <;> measurability
    · dsimp only; split_ifs with hj
      · subst j; simp [hi]
      · exact subset_univ _
    · apply eq_empty_iff_forall_notMem.2
      intro x hx
      simpa using mem_iInter.1 hx i
  · have hf : ∀ i, ∃ f : (ℕ → ℕ) → X, Continuous f ∧ range f = s i := by
      intro i
      have hh := hs i
      rw [AnalyticSet] at hh
      rcases hh with hempty | ⟨f, hf, heq⟩
      · exact (h ⟨i, hempty⟩).elim
      · exact ⟨f, hf, heq⟩
    choose f hf heq using hf
    have hr : (fun i => range (f i)) = s := funext heq
    exact hr ▸ separatedFamily_ranges f hf (hr.symm ▸ he)

end
end BorelToolkit
