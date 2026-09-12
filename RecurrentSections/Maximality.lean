/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Sufficiency

namespace RecurrentSections

open MeasureTheory

variable {G X : Type} [Group G] [DecidableEq G] [MulAction G X]

/-- Maximality among all separated supersets, not merely Borel supersets. -/
def MaximalSeparated (W : WordGeometry G) (R : ℕ) (C : Set X) : Prop :=
  Separated W R C ∧ ∀ D : Set X, C ⊆ D → Separated W R D → D ⊆ C

theorem maximalSeparated_of_dominating (W : WordGeometry G) (R : ℕ) (C : Set X)
    (hsep : Separated W R C) (hdom : ∀ x : X, ∃ g ∈ W.ball R, g • x ∈ C) :
    MaximalSeparated W R C := by
  refine ⟨hsep, ?_⟩
  intro D hCD hD x hx
  obtain ⟨g, hg, hgc⟩ := hdom x
  have heq := hD x hx (g • x) (hCD hgc) g hg rfl
  exact heq ▸ hgc

variable [MeasurableSpace X] [MeasurableConstSMul G X]

def HasRecurrentMaximalSections (W : WordGeometry G) : Prop :=
  ∀ r : ℕ → ℕ, StrictMono r → (∀ n, 0 < r n) →
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, MaximalSeparated W (r n) (C n)) ∧
      (∀ n, CompleteSection (G := G) (C n)) ∧ Recurrent W r C

variable [StandardBorelSpace X]

theorem maximalSections_of_sections (W : WordGeometry G) (tools : StandardBorelTools W)
    (hrec : HasRecurrentSections (X := X) W) : HasRecurrentMaximalSections (X := X) W := by
  classical
  intro r hr hrpos
  obtain ⟨C, hCm, hCs, _, hCr⟩ := hrec r hr hrpos
  have hext (n : ℕ) := tools.extension X (r n) (C n) (hCm n) (hCs n)
  choose D hsub hDm hDs hdom using hext
  refine ⟨D, hDm, (fun n => maximalSeparated_of_dominating W (r n) (D n) (hDs n) (hdom n)),
    ?_, (recurrent_iff_recursAt W r D).mpr ?_⟩
  · intro n x
    obtain ⟨g, _, hg⟩ := hdom n x
    exact ⟨g⁻¹, g • x, hg, inv_smul_smul g x⟩
  · intro x
    exact recursAt_mono W r hsub ((recurrent_iff_recursAt W r C).mp hCr x)

def UniversalMaximalRecurrence (W : WordGeometry G) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X], HasRecurrentMaximalSections (X := X) W

theorem universalMaximalRecurrence_of_polynomialGrowth (W : WordGeometry G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W)
    (hpoly : PolynomialGrowth W.volume) : UniversalMaximalRecurrence W := by
  intro X _ _ _ _
  exact maximalSections_of_sections W tools
    (universalRecurrence_of_polynomialGrowth W geometry tools hpoly X)

theorem universalRecurrence_of_universalMaximalRecurrence (W : WordGeometry G)
    (hrec : UniversalMaximalRecurrence W) : UniversalRecurrence W := by
  intro X _ _ _ _ r hr hrpos
  obtain ⟨C, hm, hs, hc, hrecC⟩ := hrec X r hr hrpos
  exact ⟨C, hm, (fun n => (hs n).1), hc, hrecC⟩

/-- The characterization with the paper's stronger maximality requirement. -/
theorem maximalRecurrence_iff_virtuallyNilpotent (W : WordGeometry G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W) :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G := by
  constructor
  · intro h
    exact virtuallyNilpotent_of_universalRecurrence W
      (universalRecurrence_of_universalMaximalRecurrence W h)
  · intro h
    exact universalMaximalRecurrence_of_polynomialGrowth W geometry tools (polynomialGrowth_of_virtuallyNilpotent W h)

end RecurrentSections
