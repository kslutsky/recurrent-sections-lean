/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import BorelToolkit.AnalyticSeparation

/-! # Borel relations with open sections

The Kunugui--Novikov rectangle decomposition, using countable analytic
separation followed by Lusin separation. See Srivastava, *A Course on
Borel Sets*, Theorems 4.7.1--4.7.2.
-/

set_option backward.isDefEq.respectTransparency false

namespace BorelToolkit
open Set Function Filter Topology MeasureTheory TopologicalSpace
noncomputable section

theorem analytic_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : AnalyticSet s) (ht : AnalyticSet t) : AnalyticSet (s ∩ t) := by
  have h : ∀ b : Bool, AnalyticSet (if b then s else t) := by intro b; cases b <;> simp [hs, ht]
  convert AnalyticSet.iInter h using 1
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro hx b
    cases b
    · exact hx.2
    · exact hx.1
  · intro hx
    exact ⟨by simpa using hx true, by simpa using hx false⟩

theorem analytic_union {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : AnalyticSet s) (ht : AnalyticSet t) : AnalyticSet (s ∪ t) := by
  have h : ∀ b : Bool, AnalyticSet (if b then s else t) := by intro b; cases b <;> simp [hs, ht]
  convert AnalyticSet.iUnion h using 1
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (hs | ht)
    · exact ⟨true, hs⟩
    · exact ⟨false, ht⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb

/-- A numbered open basis, padding unused codes with the empty set.
This formulation also includes the empty space. -/
theorem exists_numbered_open_basis (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y] :
    ∃ V : ℕ → Set Y, (∀ n, IsOpen (V n)) ∧
      ∀ U : Set Y, IsOpen U → ∀ y ∈ U, ∃ n, y ∈ V n ∧ V n ⊆ U := by
  classical
  let V (n : ℕ) : Set Y := (Encodable.decode (α := countableBasis Y) n).elim ∅ Subtype.val
  refine ⟨V, fun n => ?_, fun U hU y hy => ?_⟩
  · dsimp only [V]
    cases Encodable.decode (α := countableBasis Y) n with
    | none => exact isOpen_empty
    | some s => exact isOpen_of_mem_countableBasis s.property
  · obtain ⟨s, hs, hys, hsU⟩ := (isBasis_countableBasis Y).exists_subset_of_mem_open hy hU
    refine ⟨Encodable.encode (⟨s, hs⟩ : countableBasis Y), ?_⟩
    simpa [V] using And.intro hys hsU

/-- **Kunugui--Novikov.** A Borel relation with open vertical sections
is a countable union of products of Borel sets and open sets. -/
theorem exists_borel_open_rectangles
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (B : Set (X × Y)) (hB : MeasurableSet B)
    (hopen : ∀ x, IsOpen {y | (x, y) ∈ B}) :
    ∃ (D : ℕ → Set X) (V : ℕ → Set Y),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, IsOpen (V n)) ∧ B = ⋃ n, D n ×ˢ V n := by
  classical
  obtain ⟨V, hV, hbase⟩ := exists_numbered_open_basis Y
  let bad (n : ℕ) : Set X := {x | ∃ y, y ∈ V n ∧ (x, y) ∉ B}
  have hbad (n : ℕ) : AnalyticSet (bad n) := by
    have hh : MeasurableSet {p : X × Y | p.2 ∈ V n ∧ p ∉ B} :=
      (measurable_snd (hV n).measurableSet).inter hB.compl
    convert hh.analyticSet_image measurable_fst using 1
    ext x
    simp [bad]
  let C (n : ℕ) : Set (X × Y) := {p | p ∈ B ∧ (p.1 ∈ bad n ∨ p.2 ∉ V n)}
  have hCa (n : ℕ) : AnalyticSet (C n) := by
    exact analytic_inter hB.analyticSet
      (analytic_union ((hbad n).preimage continuous_fst)
        ((measurable_snd (hV n).measurableSet.compl).analyticSet))
  have hCe : ⋂ n, C n = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    rintro ⟨x, y⟩ hp
    have hpB := (mem_iInter.1 hp 0).1
    obtain ⟨n, hyn, hn⟩ := hbase _ (hopen x) y hpB
    rcases (mem_iInter.1 hp n).2 with hx | hy
    · obtain ⟨z, hzn, hz⟩ := hx
      exact hz (hn hzn)
    · exact hy hyn
  obtain ⟨E, hEm, hCE, hEe⟩ := analytic_countable_separation C hCa hCe
  let P (n : ℕ) := Prod.fst '' (B \ E n)
  have hsep (n : ℕ) : MeasurablySeparable (P n) (bad n) := by
    apply ((hB.diff (hEm n)).analyticSet_image measurable_fst).measurablySeparable (hbad n)
    apply Set.disjoint_left.2
    rintro x ⟨⟨_, y⟩, hp, rfl⟩ hx
    exact hp.2 (hCE n ⟨hp.1, Or.inl hx⟩)
  choose D hPD hbadD hDm using hsep
  refine ⟨D, V, hDm, hV, ?_⟩
  ext p
  constructor
  · intro hp
    have hex : ∃ n, p ∉ E n := by
      by_contra! hh
      have := mem_iInter.2 hh
      simp [hEe] at this
    obtain ⟨n, hn⟩ := hex
    apply mem_iUnion.2
    refine ⟨n, hPD n ⟨p, ⟨hp, hn⟩, rfl⟩, ?_⟩
    by_contra hy
    exact hn (hCE n ⟨hp, Or.inr hy⟩)
  · intro hp
    obtain ⟨n, hxn, hyn⟩ := mem_iUnion.1 hp
    by_contra hnot
    exact Set.disjoint_left.1 (hbadD n) ⟨p.2, hyn, hnot⟩ hxn

end
end BorelToolkit
