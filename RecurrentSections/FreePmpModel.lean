/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Packing
import BorelToolkit.Bernoulli
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! # A free probability-preserving standard Borel model for every countable group

This is the classical Bernoulli construction on the free part of `[0,1]^G`.
It applies to finite groups as well as infinite countable groups.
-/

namespace RecurrentSections

open MeasureTheory

/-- A free probability-preserving Borel test action. Its existence for every
countable group is proved below by restricting an atomless Bernoulli shift. -/
structure FreePmpModel (G : Type) [Group G] where
  Space : Type
  [measurableSpace : MeasurableSpace Space]
  [standardBorel : StandardBorelSpace Space]
  [action : MulAction G Space]
  [measurableAction : MeasurableConstSMul G Space]
  measure : Measure Space
  [probability : IsProbabilityMeasure measure]
  [invariant : SMulInvariantMeasure G Space measure]
  free : FreeAction (G := G) (X := Space)

/-- No external mathematical input is needed to construct the test action. -/
theorem nonempty_freePmpModel (G : Type) [Group G] [Countable G] :
    Nonempty (FreePmpModel G) := by
  refine ⟨{
    Space := BorelToolkit.Bernoulli.FreeSpace G unitInterval
    measure := BorelToolkit.Bernoulli.freeMeasure volume
    free := BorelToolkit.Bernoulli.free
  }⟩

end RecurrentSections
