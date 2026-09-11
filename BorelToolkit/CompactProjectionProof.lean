/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import BorelToolkit.OpenSections

/-! # Projection of Borel sets with compact sections

Novikov's compact-section projection theorem, the compact-section case of
Arsenin--Kunugui. We use the rectangle decomposition and finite subcovers,
then embed the target into the Hilbert cube. See Srivastava, *A Course on
Borel Sets*, Theorem 4.7.11 and its alternative proof.
-/

set_option backward.isDefEq.respectTransparency false

namespace BorelToolkit
open Set Function Filter Topology MeasureTheory TopologicalSpace
noncomputable section

/-- With a compact target, closed sections suffice for Borel projection. -/
theorem measurableSet_proj_of_closed_sections_compact
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (R : Set (X × Y)) (hR : MeasurableSet R)
    (hclosed : ∀ x, IsClosed {y | (x, y) ∈ R}) :
    MeasurableSet {x | ∃ y, (x, y) ∈ R} := by
  classical
  obtain ⟨D, V, hD, hV, hrect⟩ := exists_borel_open_rectangles Rᶜ hR.compl
    (fun x => (hclosed x).isOpen_compl)
  let U : Set X := ⋃ (s : Finset ℕ) (_ : univ ⊆ ⋃ n ∈ s, V n), ⋂ n ∈ s, D n
  have hUm : MeasurableSet U := by
    apply MeasurableSet.iUnion
    intro s
    apply MeasurableSet.iUnion
    intro _
    exact MeasurableSet.biInter (Finset.countable_toSet s) (fun n _ => hD n)
  have hU : U = {x | ∀ y, (x, y) ∉ R} := by
    ext x
    constructor
    · intro hx y hy
      obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 hx
      obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 (hs (mem_univ y))
      have hxDn := mem_iInter₂.1 hx n hn
      have hxy : (x, y) ∈ Rᶜ := hrect.symm ▸ mem_iUnion.2 ⟨n, hxDn, hyn⟩
      exact hxy hy
    · intro hx
      have hcov : univ ⊆ ⋃ n ∈ {n | x ∈ D n}, V n := by
        intro y _
        have hxy : (x, y) ∈ Rᶜ := hx y
        rw [hrect] at hxy
        obtain ⟨n, hxn, hyn⟩ := mem_iUnion.1 hxy
        exact mem_iUnion₂.2 ⟨n, hxn, hyn⟩
      obtain ⟨t, htD, htfin, htcover⟩ := isCompact_univ.elim_finite_subcover_image
        (fun n (_ : n ∈ {n | x ∈ D n}) => hV n) hcov
      apply mem_iUnion₂.2
      refine ⟨htfin.toFinset, ?_, ?_⟩
      · intro y hy
        obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 (htcover hy)
        exact mem_iUnion₂.2 ⟨n, by simpa using hn, hyn⟩
      · exact mem_iInter₂.2 (fun n hn => htD (by simpa using hn))
  rw [hU] at hUm
  convert hUm.compl using 1
  ext x
  simp

/-- **Compact-section Borel projection.** Empty sections are allowed.
The parameter space need only have a standard Borel structure. -/
theorem measurableSet_proj_of_compact_sections
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (R : Set (X × Y)) (hR : MeasurableSet R)
    (hcompact : ∀ x, IsCompact {y | (x, y) ∈ R}) :
    MeasurableSet {x | ∃ y, (x, y) ∈ R} := by
  letI := upgradeStandardBorel X
  obtain ⟨e, he⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := Y)
  let H := ℕ → unitInterval
  let F : X × Y → X × H := fun p => (p.1, e p.2)
  have hFm : Measurable F := measurable_fst.prodMk (he.continuous.measurable.comp measurable_snd)
  have hFi : Injective F := by
    intro p q hpq
    exact Prod.ext (congrArg (fun z : X × H => z.1) hpq)
      (he.injective (congrArg (fun z : X × H => z.2) hpq))
  have himage : MeasurableSet (F '' R) := hR.image_of_measurable_injOn hFm hFi.injOn
  have hsection (x : X) : {z : H | (x, z) ∈ F '' R} = e '' {y | (x, y) ∈ R} := by
    ext z
    constructor
    · rintro ⟨⟨x', y⟩, hp, heq⟩
      have hx : x' = x := congrArg Prod.fst heq
      subst x'
      exact ⟨y, hp, congrArg Prod.snd heq⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(x, y), hy, rfl⟩
  have hc (x : X) : IsClosed {z : H | (x, z) ∈ F '' R} := by
    rw [hsection]
    exact ((hcompact x).image he.continuous).isClosed
  have hm := measurableSet_proj_of_closed_sections_compact (F '' R) himage hc
  convert hm using 1
  ext x
  change (∃ y, (x, y) ∈ R) ↔ ∃ z, (x, z) ∈ F '' R
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e y, (x, y), hy, rfl⟩
  · rintro ⟨z, ⟨a, y⟩, hy, heq⟩
    have hax : a = x := congrArg (fun z : X × H => z.1) heq
    subst a
    exact ⟨y, hy⟩

end
end BorelToolkit
