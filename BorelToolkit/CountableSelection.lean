/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-! # Least measurable witnesses, including empty sections -/

namespace BorelToolkit

open Set

/-- The first natural-number witness, or zero if there is no witness. -/
noncomputable def firstWitness (P : ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ n, P n then Nat.find h else 0

theorem firstWitness_spec {P : ℕ → Prop} (h : ∃ n, P n) : P (firstWitness P) := by
  classical
  simp only [firstWitness, dif_pos h]
  exact Nat.find_spec h

theorem firstWitness_eq_iff (P : ℕ → Prop) (n : ℕ) :
    firstWitness P = n ↔ (P n ∧ ∀ m < n, ¬ P m) ∨ (n = 0 ∧ ¬ ∃ m, P m) := by
  classical
  by_cases h : ∃ m, P m
  · simp [firstWitness, h, Nat.find_eq_iff]
  · have hn : ¬ P n := fun hn => h ⟨n, hn⟩
    simp [firstWitness, h, hn, eq_comm]

/-- Least-witness selection is measurable even when some fibers are
empty; on those fibers the prescribed default is zero. -/
theorem measurable_firstWitness {X : Type*} [MeasurableSpace X]
    (P : ℕ → X → Prop) (hP : ∀ n, MeasurableSet {x | P n x}) :
    Measurable (fun x => firstWitness (fun n => P n x)) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {x | firstWitness (fun n => P n x) = n}
  simp only [firstWitness_eq_iff, ofPred_or, ofPred_and, ofPred_forall]
  apply MeasurableSet.union
  · exact (hP n).inter (MeasurableSet.iInter fun m =>
      MeasurableSet.iInter fun _ => (hP m).compl)
  · by_cases hn : n = 0
    · convert (MeasurableSet.iUnion hP).compl using 1
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, hn, true_and, mem_compl_iff, mem_iUnion]
    · simp [hn]

end BorelToolkit
