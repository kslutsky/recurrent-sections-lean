/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic

/-! # Measurable minimization over a finite family

Only measurability of pairwise cost comparisons is required. The parameter
space is an arbitrary measurable space; it need not be standard Borel.
-/

namespace BorelToolkit

open Set

/-- A finite family admits a measurable minimizer whenever its pairwise
cost comparisons are measurable. No topology on the cost space is needed. -/
theorem exists_measurable_argmin {X I V : Type*}
    [MeasurableSpace X] [MeasurableSpace I] [Fintype I] [Nonempty I] [LinearOrder V]
    (cost : I → X → V)
    (hcmp : ∀ i j, MeasurableSet {x | cost i x ≤ cost j x}) :
    ∃ f : X → I, Measurable f ∧ ∀ x i, cost (f x) x ≤ cost i x := by
  classical
  letI : Encodable I := Encodable.ofCountable I
  let good (x : X) (n : ℕ) := ∃ i : I, Encodable.encode i = n ∧
    ∀ j, cost i x ≤ cost j x
  have hex (x : X) : ∃ n, good x n := by
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image (fun i => cost i x)
      Finset.univ_nonempty
    exact ⟨Encodable.encode i, i, rfl, fun j => hi j (Finset.mem_univ _)⟩
  have hm (n : ℕ) : MeasurableSet {x | good x n} := by
    simp only [good, setOf_exists, setOf_and, setOf_forall]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : Encodable.encode i = n
    · simpa [hi] using MeasurableSet.iInter (fun j => hcmp i j)
    · simp [hi]
  let decode (n : ℕ) : I := (Encodable.decode (α := I) n).getD (Classical.ofNonempty)
  refine ⟨fun x => decode (Nat.find (hex x)),
    (measurable_of_countable decode).comp (measurable_find hex hm), ?_⟩
  intro x j
  obtain ⟨i, hi, hmin⟩ := Nat.find_spec (hex x)
  simpa [decode, ← hi] using hmin j

/-- A measurable selector from an arbitrary fixed finite candidate set.
The equality fibers are measurable without any measurable structure on
the candidate type. This supports finite choices in very large spaces. -/
theorem exists_finite_minimizer {X I V : Type*}
    [MeasurableSpace X] [LinearOrder V] (S : Finset I) (hS : S.Nonempty)
    (cost : I → X → V)
    (hcmp : ∀ i ∈ S, ∀ j ∈ S, MeasurableSet {x | cost i x ≤ cost j x}) :
    ∃ f : X → I, (∀ i, MeasurableSet {x | f x = i}) ∧
      (∀ x, f x ∈ S) ∧ ∀ x i, i ∈ S → cost (f x) x ≤ cost i x := by
  classical
  letI : MeasurableSpace S := ⊤
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨f, hf, hmin⟩ := exists_measurable_argmin (fun i : S => cost i.1)
    (fun i j => hcmp i.1 i.2 j.1 j.2)
  refine ⟨fun x => (f x).1, fun i => ?_, fun x => (f x).2, ?_⟩
  · exact hf (show MeasurableSet {j : S | j.1 = i} from trivial)
  · intro x i hi
    exact hmin x ⟨i, hi⟩

/-- Borel nearest-point choice from a fixed finite family in a metric
space. No standard Borel parameter-space theorem is used. -/
theorem exists_finite_nearest {I K : Type*} [PseudoMetricSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K]
    (S : Finset I) (hS : S.Nonempty) (p : I → K) :
    ∃ f : K → I, (∀ i, MeasurableSet {z | f z = i}) ∧
      (∀ z, f z ∈ S) ∧ ∀ z i, i ∈ S → dist (p (f z)) z ≤ dist (p i) z := by
  apply exists_finite_minimizer S hS (fun i z => dist (p i) z)
  intro i _ j _
  exact measurableSet_le (continuous_const.dist continuous_id).measurable
    (continuous_const.dist continuous_id).measurable

end BorelToolkit
