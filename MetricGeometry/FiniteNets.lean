/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Finite separated nets

This module has no group, measure, or recurrence dependencies.
-/

namespace MetricGeometry

/-- A finite metric set has an internal net whose distinct centers are
farther apart than its covering radius. The radius may be zero. -/
theorem exists_separated_net {X : Type*} [PseudoMetricSpace X]
    (S : Finset X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ N : Finset X, N ⊆ S ∧
      (∀ x ∈ N, ∀ y ∈ N, x ≠ y → δ < dist x y) ∧
      ∀ x ∈ S, ∃ y ∈ N, dist x y ≤ δ := by
  classical
  let good (N : Finset X) := ∀ x ∈ N, ∀ y ∈ N, x ≠ y → δ < dist x y
  let candidates := S.powerset.filter good
  have hn : candidates.Nonempty := ⟨∅, by simp [candidates, good]⟩
  obtain ⟨N, hN, hmax⟩ := candidates.exists_max_image Finset.card hn
  have hNs : N ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hN).1
  have hNg : good N := (Finset.mem_filter.mp hN).2
  refine ⟨N, hNs, hNg, ?_⟩
  intro x hx
  by_contra! hfar
  have hxN : x ∉ N := by
    intro hxN
    have : δ < 0 := by simpa using hfar x hxN
    exact not_lt_of_ge hδ this
  have hins : insert x N ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hNs), ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | haN
    · subst a
      rcases Finset.mem_insert.mp hb with hbx | hbN
      · exact (hab hbx.symm).elim
      · exact hfar b hbN
    · rcases Finset.mem_insert.mp hb with hbx | hbN
      · subst b
        simpa [dist_comm] using hfar a haN
      · exact hNg a haN b hbN hab
  have := hmax (insert x N) hins
  rw [Finset.card_insert_of_notMem hxN] at this
  omega

end MetricGeometry
