/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import BorelToolkit.ClosedSelection
import BorelToolkit.CompactProjectionProof
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Separation.GDelta

/-! # Compact-section projection and fixed selection

The projection theorem is proved in `CompactProjectionProof`, using
Novikov separation and the Kunugui--Novikov rectangle decomposition.
This module derives weak measurability and fixed compact-set selection.
The selection algorithm itself is proved in `ClosedSelection`.
-/

namespace BorelToolkit

open Set TopologicalSpace

universe u v

/-- The compact-section Borel projection theorem, including empty
sections. A proved inhabitant is `compactSectionProjectionTheorem`. -/
def CompactSectionProjectionTheorem : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] [StandardBorelSpace X],
    ∀ (K : Type v) [MetricSpace K] [CompleteSpace K] [SeparableSpace K]
      [MeasurableSpace K] [BorelSpace K],
    ∀ R : Set (X × K), MeasurableSet R →
      (∀ x, IsCompact {y | (x, y) ∈ R}) → MeasurableSet {x | ∃ y, (x, y) ∈ R}

/-- The formerly external compact-section projection input is proved. -/
theorem compactSectionProjectionTheorem : CompactSectionProjectionTheorem.{u, v} := by
  intro X _ _ K _ _ _ _ _ R hR hcompact
  exact measurableSet_proj_of_compact_sections R hR hcompact

/-- Compact sections and a Borel graph give weak measurability. Open
target sets are handled as countable unions of closed sets. -/
theorem weaklyMeasurable_of_compact_graph
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    {K : Type v} [MetricSpace K] [CompleteSpace K] [SeparableSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (T : X → Set K) (hT : ∀ x, IsCompact (T x))
    (hgraph : MeasurableSet {p : X × K | p.2 ∈ T p.1}) : WeaklyMeasurable T := by
  intro U hU
  obtain ⟨V, hVopen, hV⟩ := isGδ_iff_eq_iInter_nat.mp hU.isClosed_compl.isGδ
  have hUeq : U = ⋃ n, (V n)ᶜ := by
    calc
      U = (Uᶜ)ᶜ := (compl_compl U).symm
      _ = (⋂ n, V n)ᶜ := by rw [hV]
      _ = _ := compl_iInter _
  have hm (n : ℕ) : MeasurableSet {x | ∃ y, y ∈ T x ∧ y ∈ (V n)ᶜ} := by
    apply compactSectionProjectionTheorem X K {p : X × K | p.2 ∈ T p.1 ∧ p.2 ∈ (V n)ᶜ}
    · exact hgraph.inter (measurable_snd (hVopen n).isClosed_compl.measurableSet)
    · intro x
      exact (hT x).inter_right (hVopen n).isClosed_compl
  convert MeasurableSet.iUnion hm using 1
  ext x
  constructor
  · rintro ⟨y, hyT, hyU⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hUeq ▸ hyU)
    exact mem_iUnion.mpr ⟨n, y, hyT, hn⟩
  · intro hx
    obtain ⟨n, y, hyT, hn⟩ := mem_iUnion.mp hx
    exact ⟨y, hyT, hUeq.symm ▸ mem_iUnion.mpr ⟨n, hn⟩⟩

/-- A fixed, presentation-independent selector for compact-section
Borel families, with no external selection or projection assumption. -/
theorem measurable_closedSelector_of_compact_graph
    {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    {K : Type v} [MetricSpace K] [CompleteSpace K] [SeparableSpace K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K]
    (T : X → Set K) (hT : ∀ x, IsCompact (T x)) (hne : ∀ x, (T x).Nonempty)
    (hgraph : MeasurableSet {p : X × K | p.2 ∈ T p.1}) :
    Measurable (fun x => closedSelector (T x)) :=
  measurable_closedSelector T (weaklyMeasurable_of_compact_graph T hT hgraph) hne

end BorelToolkit
