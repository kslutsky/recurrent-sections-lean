/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import MetricGeometry.FiniteNets
import Mathlib.Topology.MetricSpace.Isometry

/-! # Uniform coverings and the common compact embedding theorem

`CommonCompactEmbeddingTheorem` records the precise statement used by the
application. `MetricGeometry.CommonEmbedding` proves it, in stronger
generality. These modules are independent of groups, actions, and recurrence.
-/

namespace MetricGeometry

/-- Uniform finite internal covering numbers, at every positive radius. -/
def UniformlyCoverable {ι : Type*} (A : ι → Type*) [∀ n, MetricSpace (A n)] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, ∃ S : Finset (A n),
    S.card ≤ N ∧ ∀ x : A n, ∃ y ∈ S, dist x y ≤ ε

/-- Gromov's common compact realization theorem for a countable family
of nonempty compact metric spaces of uniformly bounded diameter and
uniform covering numbers. All members embed, with their exact metrics.
The proof in `CommonEmbedding` constructs all embeddings simultaneously;
no subsequence-only conclusion is substituted. -/
def CommonCompactEmbeddingTheorem : Prop :=
  ∀ (A : ℕ → Type) (m : ∀ n, MetricSpace (A n)),
    letI := m
    (∀ n, CompactSpace (A n)) → (∀ n, Nonempty (A n)) →
    (∃ C : ℝ, ∀ n (x y : A n), dist x y ≤ C) → UniformlyCoverable A →
    ∃ (K : Type) (metric : MetricSpace K),
      letI := metric
      CompactSpace K ∧ ∃ f : ∀ n, A n → K, ∀ n, Isometry (f n)

end MetricGeometry
