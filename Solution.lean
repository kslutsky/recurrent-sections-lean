/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections

/-! # Proved Palomar statements

This module imports the complete development, including Aaron Hill's pinned
Gromov formalization. Each theorem below implements the identically named
statement in `Challenge.lean`. The Challenge is never imported here.
-/

open MeasureTheory

namespace PalomarRecurrence

open RecurrentSections

variable {G : Type} [Group G] [DecidableEq G]

/-- Polynomial growth is characterized by prescribed-radius recurrence in
all standard Borel actions, allowing arbitrary stabilizers. -/
theorem recurrence_iff_polynomialGrowth (W : WordGeometry G) :
    UniversalRecurrence W ↔ PolynomialGrowth W.volume :=
  RecurrentSections.recurrence_iff_polynomialGrowth_of_standard_theorems W

/-- Equivalently, universal prescribed-radius recurrence characterizes virtual
nilpotence. Mathlib defines this as existence of a nilpotent subgroup of finite
index; the subgroup need not be normal. -/
theorem recurrence_iff_virtuallyNilpotent (W : WordGeometry G) :
    UniversalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  RecurrentSections.recurrence_iff_virtuallyNilpotent_of_standard_theorems W

/-- Quantifying over free actions alone still characterizes polynomial growth. -/
theorem freeRecurrence_iff_polynomialGrowth (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ PolynomialGrowth W.volume :=
  RecurrentSections.freeRecurrence_iff_polynomialGrowth_of_standard_theorems W

/-- The free-action property is also equivalent to virtual nilpotence. -/
theorem freeRecurrence_iff_virtuallyNilpotent (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  RecurrentSections.freeRecurrence_iff_virtuallyNilpotent_of_standard_theorems W

end PalomarRecurrence

namespace PalomarRecurrence

open RecurrentSections

/-- One everywhere recurrent sequence in one free probability-preserving
action forces subexponential growth. Strictly increasing integer radii,
measurability, and separation are assumed; complete sections are unnecessary. -/
theorem one_sequence_implies_subexponentialGrowth
    {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]
    [MeasurableSpace X] [MeasurableConstSMul G X]
    (W : WordGeometry G) (μ : Measure X)
    [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
    (hfree : FreeAction (G := G) (X := X))
    (r : ℕ → ℕ) (hr : StrictMono r) (C : ℕ → Set X)
    (hC : ∀ n, MeasurableSet (C n))
    (hsep : ∀ n, Separated W (r n) (C n))
    (hrec : Recurrent W r C) : SubexponentialGrowth W.volume :=
  RecurrentSections.subexponentialGrowth_of_one_recurrent_sequence μ W hfree r hr C hC hsep hrec

end PalomarRecurrence
