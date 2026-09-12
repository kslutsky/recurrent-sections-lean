/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace RecurrentSections
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The three-subgroups lemma modulo an arbitrary normal subgroup. -/
theorem commutator_commutator_le_of_rotate (A B C N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅B, C⁆, A⁆ ≤ N) (h₂ : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  have hmap₁ : (⁅⁅B, C⁆, A⁆).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h₁
  have hmap₂ : (⁅⁅C, A⁆, B⁆).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact h₂
  rw [Subgroup.map_commutator, Subgroup.map_commutator] at hmap₁ hmap₂
  have h := Subgroup.commutator_commutator_eq_bot_of_rotate hmap₁ hmap₂
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  exact h

/-- Weights in the lower central series add under commutators. The indexing
starts at zero, so terms `i` and `j` land in term `i+j+1`. -/
theorem commutator_top_lowerCentralSeries_le (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) := by
  induction i generalizing j with
  | zero =>
    simpa only [Nat.zero_add, Subgroup.lowerCentralSeries_zero,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm] using
      (le_refl ((⊤ : Subgroup G).lowerCentralSeries (j + 1)))
  | succ i ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply commutator_commutator_le_of_rotate
    · rw [Subgroup.commutator_comm ⊤, ← Subgroup.lowerCentralSeries_succ,
        Subgroup.commutator_comm]
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (j + 1)
    · calc
        ⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G).lowerCentralSeries i⁆, ⊤⁆
            ≤ ⁅(⊤ : Subgroup G).lowerCentralSeries (i + j + 1), ⊤⁆ :=
          Subgroup.commutator_mono (by simpa only [Subgroup.commutator_comm] using ih j) le_rfl
        _ = (⊤ : Subgroup G).lowerCentralSeries (i + 1 + j + 1) := by
          rw [← Subgroup.lowerCentralSeries_succ]
          congr 1
          omega

/-- The corresponding relative statement for every subgroup, without a
normality or nilpotence assumption on that subgroup. -/
theorem lowerCentralSeries_commutator_le (S : Subgroup G) (i j : ℕ) :
    ⁅S.lowerCentralSeries i, S.lowerCentralSeries j⁆ ≤ S.lowerCentralSeries (i + j + 1) := by
  have h := Subgroup.map_mono (f := S.subtype)
    (commutator_top_lowerCentralSeries_le (G := S) i j)
  simpa only [Subgroup.map_commutator, Subgroup.top_subtype_lowerCentralSeries] using h

end RecurrentSections
