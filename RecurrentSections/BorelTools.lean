/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.StandardInputs
import BorelToolkit.ActionGraph
import BorelToolkit.FiniteSelection
import BorelToolkit.CompactProjection

/-! # From the reusable Borel toolkit to recurrent cross sections

This module contains only the action-specific adapters. Import
`BorelToolkit` or its individual modules to use the general theorems
without any cross-section or group-growth dependencies.
-/

namespace RecurrentSections

open Set BorelToolkit MeasurableSpace

variable {G X : Type} [Group G] [DecidableEq G] [MulAction G X]

/-- The finite orbit-distance graph associated with a word ball. -/
abbrev orbitGraph (W : WordGeometry G) (R : ℕ) : SimpleGraph X :=
  finiteActionGraph (W.ball R) (fun _ hg => W.inv_mem_ball hg)

theorem separated_iff_independent (W : WordGeometry G) (R : ℕ) (C : Set X) :
    Separated W R C ↔ (orbitGraph W R).IsIndepSet C := by
  constructor
  · intro h x hx y hy hne hadj
    obtain ⟨_, g, hg, hxy⟩ := hadj
    exact hne (h x hx y hy g hg hxy)
  · intro h x hx y hy g hg hxy
    by_contra hne
    exact h hx hy hne ⟨hne, g, hg, hxy⟩

variable [MeasurableSpace X] [CountablySeparated X] [MeasurableConstSMul G X]

/-- Seeded Borel extension is proved for every action on a countably
separated measurable space, with no freeness assumption. -/
theorem borelExtension (W : WordGeometry G) : BorelExtension (X := X) W := by
  intro R C hCm hCi
  obtain ⟨D, hCD, _, hDm, hDi, hdom⟩ := exists_maximal_extension
    (orbitGraph (X := X) W R) (finiteActionGraph_measurable _ _)
    (finiteActionGraph_finite _ _) univ C MeasurableSet.univ hCm
    (subset_univ _) ((separated_iff_independent W R C).mp hCi)
  refine ⟨D, hCD, hDm, (separated_iff_independent W R D).mpr hDi, ?_⟩
  intro x
  obtain hx | ⟨y, hy, _, g, hg, hxy⟩ := hdom x (mem_univ x)
  · exact ⟨1, W.one_mem_ball R, by simpa using hx⟩
  · exact ⟨g, hg, hxy.symm ▸ hy⟩

omit [MeasurableSpace X] [CountablySeparated X] [MeasurableConstSMul G X] in
/-- The exact local multiplicity condition in the cross-section proof
implies the closed-neighborhood bound required by the general coloring lemma. -/
theorem localMultiplicity_ncard (W : WordGeometry G) (R M : ℕ) (D : Set X)
    (h : LocalMultiplicity W R M D) (x : X) (hx : x ∈ D) :
    (closedNeighbors (orbitGraph W R) D x).ncard ≤ M := by
  classical
  let N := closedNeighbors (orbitGraph W R) D x
  have hn : N.Finite := ((finiteActionGraph_finite (X := X) (W.ball R)
    (fun _ hg => W.inv_mem_ball hg) x).insert x).subset inter_subset_right
  letI : Fintype N := hn.fintype
  have hc := h x hx N Subtype.val Subtype.val_injective (fun i => i.2.1) (fun i => ?_)
  · change N.ncard ≤ M
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hc
  · rcases i.2.2 with heq | hadj
    · exact ⟨1, W.one_mem_ball R, by simpa using heq.symm⟩
    · exact hadj.2

/-- The bounded-degree Borel coloring input is now a checked corollary
of the general graph theorem. -/
theorem borelColoring (W : WordGeometry G) : BorelColoring (X := X) W := by
  intro R M _ D hDm hbound
  obtain ⟨C, hCm, hCi, hCc⟩ := exists_finite_independent_cover
    (orbitGraph (X := X) W R) (finiteActionGraph_measurable _ _)
    (finiteActionGraph_finite _ _) M D hDm (localMultiplicity_ncard W R M D hbound)
  exact ⟨C, hCm, fun i => (separated_iff_independent W R (C i)).mpr (hCi i), hCc⟩

/-- The fixed compact-set selection interface follows from the proved
closed-set selector and the proved compact-section projection theorem. -/
theorem compactChoice
    (K : Type) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [Nonempty K] : Nonempty (CompactChoice K) := by
  refine ⟨⟨closedSelector, ?_, ?_⟩⟩
  · intro T hT hne
    exact closedSelector_mem hT.isClosed hne
  · intro X _ _ T hT hne hgraph
    exact measurable_closedSelector_of_compact_graph T hT hne hgraph

/-- All action-specific Borel inputs are assembled from proved reusable
lemmas. No descriptive-set-theoretic, graph, or selection theorem remains
as an external hypothesis. -/
theorem standardBorelTools (W : WordGeometry G) : StandardBorelTools W where
  extension := by
    intro X _ _ _ _
    exact borelExtension W
  coloring := by
    intro X _ _ _ _
    exact borelColoring W
  compactChoice := by
    intro K _ _ _ _ _
    exact compactChoice K
  finiteNearest := by
    intro K _ _ _ _ S hS p
    exact exists_finite_nearest S hS p

end RecurrentSections
