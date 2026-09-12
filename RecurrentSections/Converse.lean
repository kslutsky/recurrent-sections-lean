/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.GromovTheorem
import RecurrentSections.Packing
import Mathlib.GroupTheory.Nilpotent
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace RecurrentSections

open MeasureTheory
open scoped Pointwise ENNReal

/-- A useful conversion of an integer dilation inequality into a measure budget. -/
theorem ratio_le_geometric {a b n : ℕ} (hb : 0 < b)
    (hab : 2 ^ (n + 2) * a ≤ b) :
    (a : ℝ≥0∞) / b ≤ (2 : ℝ≥0∞)⁻¹ ^ (n + 2) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb.ne'
  have hk0 : (2 : ℝ≥0∞) ^ (n + 2) ≠ 0 := by positivity
  have hkfin : (2 : ℝ≥0∞) ^ (n + 2) ≠ ⊤ := by finiteness
  have hcast : (2 : ℝ≥0∞) ^ (n + 2) * a ≤ b := by exact_mod_cast hab
  have hdiv : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (n + 2) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hkfin)).mpr
    simpa [mul_comm] using hcast
  apply (ENNReal.div_le_iff hb0 (ENNReal.natCast_ne_top b)).mpr
  simpa [ENNReal.inv_pow, div_eq_mul_inv, mul_comm] using hdiv

variable {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]

/-- The single value `ε = 1/10` in recurrence implies a covering at radii `mₙ`.
This isolates all rounding and word-distance details from the measure argument. -/
theorem recurrent_implies_cover (W : WordGeometry G) (m : ℕ → ℕ)
    (C : ℕ → Set X) (hrec : Recurrent W (fun n => 10 * m n) C) :
    (⋃ n, neighborhood W (m n) (C n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, _, g, c, hc, hgc, hlen⟩ := hrec (1 / 10) (by norm_num) x 0
  have hlt : (W.length g : ℝ) < (m n : ℝ) := by
    push_cast at hlen
    linarith
  have hle : W.length g ≤ m n := by exact_mod_cast hlt.le
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨g, Set.mem_iUnion.mpr ⟨(W.mem_ball_iff_length_le g (m n)).mpr hle, ?_⟩⟩
  exact ⟨c, hc, hgc⟩

variable [MeasurableSpace X] [MeasurableConstSMul G X]

/-- The prescribed-radii property for a fixed action. Maximality is not
required; the converse therefore also applies to maximal cross sections. -/
def HasRecurrentSections (W : WordGeometry G) : Prop :=
  ∀ r : ℕ → ℕ, StrictMono r → (∀ n, 0 < r n) →
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, Separated W (r n) (C n)) ∧
      (∀ n, CompleteSection (G := G) (C n)) ∧ Recurrent W r C

/-- The core converse. Nonpolynomial growth produces a schedule that
precludes everywhere recurrence in every free pmp action. The lower
bound `q` may depend on both the stage and the preceding scale. -/
theorem adverse_schedule (W : WordGeometry G)
    (hpoly : ¬ PolynomialGrowth W.volume) (q : ℕ → ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ n, 0 < m n) ∧
      q 0 0 ≤ m 0 ∧ (∀ n, q (n + 1) (m n) ≤ m (n + 1)) ∧
      ∀ (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ],
        FreeAction (G := G) (X := X) →
        ∀ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) →
          (∀ n, Separated W (10 * m n) (C n)) →
          ¬ Recurrent W (fun n => 10 * m n) C := by
  obtain ⟨m, hmono, hpos, hratio, hq0, hq⟩ :=
    exists_adverse_scales W.volume W.volume_mono hpoly q
  refine ⟨m, hmono, hpos, hq0, hq, ?_⟩
  intro μ _ _ hfree C hC hsep hrec
  apply not_cover_of_geometric_budget μ (fun n => neighborhood W (m n) (C n))
    (fun n => ?_) (recurrent_implies_cover W m C hrec)
  exact (measure_neighborhood_le μ W (m n) hfree (hC n) (hsep n)).trans
    (ratio_le_geometric (W.volume_pos (5 * m n)) (hratio n).le)

/-- The converse still holds if prescribed schedules must obey any fixed
lower bound depending on the stage and the previous radius. Completeness
and maximality of the separated sets are unnecessary. -/
theorem polynomialGrowth_of_recurrent_with_lowerBounds (W : WordGeometry G)
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
    (hfree : FreeAction (G := G) (X := X)) (q : ℕ → ℕ → ℕ)
    (hrec : ∀ r : ℕ → ℕ, StrictMono r → (∀ n, 0 < r n) →
      q 0 0 ≤ r 0 → (∀ n, q (n + 1) (r n) ≤ r (n + 1)) →
      ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
        (∀ n, Separated W (r n) (C n)) ∧ Recurrent W r C) :
    PolynomialGrowth W.volume := by
  by_contra hpoly
  obtain ⟨m, hmono, hpos, hq0, hq, hbad⟩ :=
    adverse_schedule (X := X) W hpoly (fun n prev => q n (10 * prev))
  have hrmono : StrictMono (fun n => 10 * m n) := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (hmono hij) (by decide)
  have hrq0 : q 0 0 ≤ 10 * m 0 := by simpa using hq0.trans (by omega)
  have hrq (n : ℕ) : q (n + 1) (10 * m n) ≤ 10 * m (n + 1) :=
    (hq n).trans (by omega)
  obtain ⟨C, hC, hsep, hrecC⟩ := hrec (fun n => 10 * m n) hrmono
    (fun n => Nat.mul_pos (by decide) (hpos n)) hrq0 hrq
  exact hbad μ hfree C hC hsep hrecC

/-- Recurrence for every prescribed schedule in one free pmp action forces
polynomial growth. This theorem has no unformalized mathematical inputs. -/
theorem polynomialGrowth_of_recurrent (W : WordGeometry G)
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
    (hfree : FreeAction (G := G) (X := X))
    (hrec : HasRecurrentSections (X := X) W) : PolynomialGrowth W.volume := by
  by_contra hpoly
  obtain ⟨m, hmono, hpos, _, _, hbad⟩ :=
    adverse_schedule (X := X) W hpoly (fun _ _ => 0)
  have hrmono : StrictMono (fun n => 10 * m n) := by
    intro i j hij
    exact Nat.mul_lt_mul_of_pos_left (hmono hij) (by decide)
  obtain ⟨C, hC, hsep, _, hrecC⟩ := hrec (fun n => 10 * m n) hrmono
    (fun n => Nat.mul_pos (by decide) (hpos n))
  exact hbad μ hfree C hC hsep hrecC

/-- Recurrence for every schedule in one free probability-preserving action
implies virtual nilpotence. The Gromov step is proved by the pinned external
formalization imported in `GromovTheorem.lean`, with no mathematical input
argument remaining. See that module for full attribution and references. -/
theorem virtuallyNilpotent_of_recurrent (W : WordGeometry G)
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]
    (hfree : FreeAction (G := G) (X := X))
    (hrec : HasRecurrentSections (X := X) W) : Group.IsVirtuallyNilpotent G :=
  virtuallyNilpotent_of_polynomialGrowth W (polynomialGrowth_of_recurrent W μ hfree hrec)

end RecurrentSections
