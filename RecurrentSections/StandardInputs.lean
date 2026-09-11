/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.CompactLimits

namespace RecurrentSections

open MeasureTheory

/-- The standard Borel selector for nonempty compact subsets, combined
with the compact-section projection theorem. The same selector is used
for equal compact sets; no invariance or recurrence conclusion is assumed. -/
structure CompactChoice (K : Type) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] where
  select : Set K → K
  mem : ∀ T : Set K, IsCompact T → T.Nonempty → select T ∈ T
  measurable : ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    (T : X → Set K), (∀ x, IsCompact (T x)) → (∀ x, (T x).Nonempty) →
    MeasurableSet {p : X × K | p.2 ∈ T p.1} → Measurable (fun x => select (T x))

variable {G : Type} [Group G] [DecidableEq G]

/-- Scaled isometric embeddings of finite word balls. No action is involved. -/
def ScaledModels (W : WordGeometry G) (r : ℕ → ℕ) {K : Type} [MetricSpace K]
    (φ : ℕ → G → K) : Prop :=
  ∀ n g h, g ∈ W.ball (3 * r n) → h ∈ W.ball (3 * r n) →
    dist (φ n g) (φ n h) * (r n : ℝ) = (W.length (g⁻¹ * h) : ℝ)

/-- The uniform packing bound for a doubling word metric, in finite-family
form. It is a statement about the group metric alone. -/
def GroupPacking (W : WordGeometry G) (M : ℕ) : Prop :=
  ∀ R : ℕ, 0 < R → ∀ (I : Type) [Fintype I] (f : I → G),
    (∀ i, W.length (f i) ≤ 7 * R) →
    (∀ i j, i ≠ j → R < W.length (f j * (f i)⁻¹)) → Fintype.card I ≤ M

/-- Published geometric inputs: polynomial-growth groups have doubling
word metrics (Breuillard), and uniformly totally bounded compact metric
spaces of bounded diameter admit common compact models (Gromov).
These hypotheses contain no Borel-action or cross-section statement. -/
structure PolynomialGeometry (W : WordGeometry G) : Prop where
  packing : PolynomialGrowth W.volume → ∃ M : ℕ, 0 < M ∧ GroupPacking W M
  models : PolynomialGrowth W.volume → ∀ r : ℕ → ℕ, StrictMono r →
    (∀ n, 0 < r n) → ∃ (K : Type) (metric : MetricSpace K),
      letI := metric
      CompactSpace K ∧ ∃ φ : ℕ → G → K, ScaledModels W r φ

variable {X : Type} [MulAction G X]

/-- Uniform cardinal bounds on orbit-ball intersections, including the center. -/
def LocalMultiplicity (W : WordGeometry G) (R M : ℕ) (D : Set X) : Prop :=
  ∀ y ∈ D, ∀ (I : Type) [Fintype I] (f : I → X), Function.Injective f →
    (∀ i, f i ∈ D) → (∀ i, ∃ g ∈ W.ball R, g • y = f i) → Fintype.card I ≤ M

variable [MeasurableSpace X] [MeasurableConstSMul G X]

/-- Borel maximal independent-set extension, with its usual domination property. -/
def BorelExtension (W : WordGeometry G) : Prop :=
  ∀ R : ℕ, ∀ C : Set X, MeasurableSet C → Separated W R C →
    ∃ D : Set X, C ⊆ D ∧ MeasurableSet D ∧ Separated W R D ∧
      ∀ x : X, ∃ g ∈ W.ball R, g • x ∈ D

/-- The bounded-degree Borel coloring theorem, stated for orbit-distance graphs. -/
def BorelColoring (W : WordGeometry G) : Prop :=
  ∀ R M : ℕ, 0 < M → ∀ D : Set X, MeasurableSet D → LocalMultiplicity W R M D →
    ∃ C : Fin M → Set X, (∀ i, MeasurableSet (C i)) ∧
      (∀ i, Separated W R (C i)) ∧ D = ⋃ i, C i

/-- Standard descriptive-set-theoretic and finite-minimization inputs.
All recurrence and invariant-recentering deductions are proved separately. -/
structure StandardBorelTools (W : WordGeometry G) : Prop where
  extension : ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X], BorelExtension (X := X) W
  coloring : ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    [MulAction G X] [MeasurableConstSMul G X], BorelColoring (X := X) W
  compactChoice : ∀ (K : Type) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [Nonempty K], Nonempty (CompactChoice K)
  finiteNearest : ∀ (K : Type) [MetricSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K], ∀ (S : Finset G), S.Nonempty → ∀ p : G → K,
      ∃ h : K → G, (∀ g, MeasurableSet {z | h z = g}) ∧
        (∀ z, h z ∈ S) ∧ (∀ z g, g ∈ S → dist (p (h z)) z ≤ dist (p g) z)

end RecurrentSections
