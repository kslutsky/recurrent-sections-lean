/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Restriction of a measure-preserving map to a conull invariant set -/

namespace BorelToolkit

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : Set X}

/-- The subtype measure on a measurable conull set maps back to the original measure. -/
theorem measurePreserving_conull_subtype (hs : MeasurableSet s)
    (hfull : ∀ᵐ x ∂μ, x ∈ s) :
    MeasurePreserving (Subtype.val : s → X) (μ.comap Subtype.val) μ := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hfull] using
    (measurePreserving_subtype_coe (μa := μ) hs)

/-- A measure-preserving map restricts to any measurable conull forward-invariant set.
Neither invertibility nor a probability hypothesis is required. -/
theorem measurePreserving_restrict_conull {f : X → X} (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) (hinv : Set.MapsTo f s s) :
    MeasurePreserving (fun x : s => (⟨f x, hinv x.property⟩ : s))
      (μ.comap Subtype.val) (μ.comap Subtype.val) := by
  have hm : Measurable (fun x : s => (⟨f x, hinv x.property⟩ : s)) :=
    (hf.measurable.comp measurable_subtype_coe).subtype_mk
  have hc := measurePreserving_conull_subtype hs hfull
  refine ⟨hm, (MeasurableEmbedding.subtype_coe hs).map_injective ?_⟩
  rw [Measure.map_map measurable_subtype_coe hm]
  exact (hf.comp hc).map_eq.trans hc.map_eq.symm

end BorelToolkit
