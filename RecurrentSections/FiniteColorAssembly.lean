/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.StandardInputs

namespace RecurrentSections

open Set MeasureTheory

variable {G X : Type} [Group G] [DecidableEq G] [MulAction G X]
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableConstSMul G X]

/-- Invariant selection of a recurrent color. Compact selection on the
finite color space is a standard input; recurrence, invariance,
measurability of the loci, and separation of the assembled sets are proved. -/
theorem finite_color_assembly (W : WordGeometry G) (tools : StandardBorelTools W)
    (r : ℕ → ℕ) (hr : StrictMono r) (M : ℕ) (hM : 0 < M)
    (D : Fin M → ℕ → Set X) (hD : ∀ i n, MeasurableSet (D i n))
    (hsep : ∀ i n, Separated W (r n) (D i n))
    (hrec : Recurrent W r (fun n => ⋃ i, D i n)) :
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, Separated W (r n) (C n)) ∧
      (∀ n, CompleteSection (G := G) (C n)) ∧ Recurrent W r C := by
  classical
  let metric : MetricSpace (Fin M) := MetricSpace.induced (fun i : Fin M => (i.val : ℝ)) (by
    intro i j hij
    change (i.val : ℝ) = (j.val : ℝ) at hij
    apply Fin.ext
    exact_mod_cast hij) inferInstance
  letI := metric
  letI : TopologicalSpace (Fin M) := metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Fin M) := borel (Fin M)
  letI : BorelSpace (Fin M) := ⟨rfl⟩
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨choice⟩ := tools.compactChoice (Fin M)
  let T (x : X) : Set (Fin M) := {i | RecursAt W r (D i) x}
  have hTc (x : X) : IsCompact (T x) := (Set.toFinite _).isCompact
  have hTn (x : X) : (T x).Nonempty :=
    recursAt_finite_union W r D x ((recurrent_iff_recursAt W r _).mp hrec x)
  have hTm : MeasurableSet {p : X × Fin M | p.2 ∈ T p.1} := by
    have heq : {p : X × Fin M | p.2 ∈ T p.1} =
        ⋃ i : Fin M, {x | RecursAt W r (D i) x} ×ˢ {i} := by
      ext p
      simp only [T, mem_setOf_eq, mem_iUnion, mem_prod, mem_singleton_iff]
      constructor
      · intro h; exact ⟨p.2, h, rfl⟩
      · rintro ⟨i, h, rfl⟩; exact h
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      (measurableSet_recursAt W r (D i) (hD i)).prod (MeasurableSet.singleton i)
  have hTi (g : G) (x : X) : T (g • x) = T x := by
    ext i
    exact recursAt_smul W r hr (D i) g x
  let f (x : X) : Fin M := choice.select (T x)
  have hf : Measurable f := choice.measurable X T hTc hTn hTm
  have hfi (g : G) (x : X) : f (g • x) = f x := congrArg choice.select (hTi g x)
  have hfr (x : X) : RecursAt W r (D (f x)) x := choice.mem (T x) (hTc x) (hTn x)
  let C₀ (n : ℕ) : Set X := {x | x ∈ D (f x) n}
  have hC₀ (n : ℕ) : MeasurableSet (C₀ n) := by
    have heq : C₀ n = ⋃ i : Fin M, D i n ∩ {x | f x = i} := by
      ext x
      simp only [C₀, mem_setOf_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro h; exact ⟨f x, h, rfl⟩
      · rintro ⟨i, h, hi⟩; simpa [hi] using h
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      (hD i n).inter ((MeasurableSet.singleton i).preimage hf)
  have hCsep (n : ℕ) : Separated W (r n) (C₀ n) := by
    intro x hx y hy g hg hxy
    have hfy : f y = f x := by rw [← hxy]; exact hfi g x
    apply hsep (f x) n x hx y ?_ g hg hxy
    simpa only [C₀, mem_setOf_eq, hfy] using hy
  have hCrec (x : X) : RecursAt W r C₀ x := by
    intro k N
    obtain ⟨n, hn, g, c, hc, hgc, hlen⟩ := hfr x k N
    have hfc : f c = f x := by rw [← hgc]; exact (hfi g c).symm
    exact ⟨n, hn, g, c, by simpa only [C₀, mem_setOf_eq, hfc] using hc, hgc, hlen⟩
  have hext (n : ℕ) := tools.extension X (r n) (C₀ n) (hC₀ n) (hCsep n)
  choose C hsub hCm hCs hdom using hext
  refine ⟨C, hCm, hCs, ?_, (recurrent_iff_recursAt W r C).mpr ?_⟩
  · intro n x
    obtain ⟨g, _, hg⟩ := hdom n x
    exact ⟨g⁻¹, g • x, hg, inv_smul_smul g x⟩
  · intro x
    exact recursAt_mono W r hsub (hCrec x)

end RecurrentSections
