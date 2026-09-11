/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Converse

namespace RecurrentSections

open MeasureTheory
open scoped Pointwise

variable {G X : Type*} [Group G] [DecidableEq G]

namespace WordGeometry

theorem length_one (W : WordGeometry G) : W.length 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (W.mem_ball_iff_length_le 1 0).mp (W.one_mem_ball 0)

theorem length_inv (W : WordGeometry G) (g : G) : W.length g⁻¹ = W.length g := by
  apply Nat.le_antisymm
  · exact (W.mem_ball_iff_length_le _ _).mp
      (W.inv_mem_ball ((W.mem_ball_iff_length_le _ _).mpr le_rfl))
  · simpa using (W.mem_ball_iff_length_le _ _).mp
      (W.inv_mem_ball ((W.mem_ball_iff_length_le g⁻¹ _).mpr le_rfl))

theorem length_mul_le (W : WordGeometry G) (g h : G) :
    W.length (g * h) ≤ W.length g + W.length h :=
  (W.mem_ball_iff_length_le _ _).mp (W.mul_mem_ball
    ((W.mem_ball_iff_length_le _ _).mpr le_rfl)
    ((W.mem_ball_iff_length_le _ _).mpr le_rfl))

theorem countable (W : WordGeometry G) : Countable G := by
  have h : (⋃ n, (W.ball n : Set G)) = Set.univ := by
    ext g
    simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_univ, iff_true]
    exact W.generates g
  exact Set.countable_univ_iff.mp (h ▸ Set.countable_iUnion (fun n => (W.ball n).countable_toSet))

end WordGeometry

variable [MulAction G X]

/-- A countable-tolerance formulation of recurrence at one point. -/
def RecursAt (W : WordGeometry G) (r : ℕ → ℕ) (C : ℕ → Set X) (x : X) : Prop :=
  ∀ k N : ℕ, ∃ n, N ≤ n ∧ ∃ g : G, ∃ c ∈ C n,
    g • c = x ∧ (k + 1) * W.length g < r n

theorem recurrent_iff_recursAt (W : WordGeometry G) (r : ℕ → ℕ)
    (C : ℕ → Set X) : Recurrent W r C ↔ ∀ x, RecursAt W r C x := by
  constructor
  · intro h x k N
    obtain ⟨n, hn, g, c, hc, heq, hlen⟩ :=
      h (1 / (k + 1 : ℝ)) (by positivity) x N
    refine ⟨n, hn, g, c, hc, heq, ?_⟩
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hl : (k + 1 : ℝ) * W.length g < r n := by
      rw [mul_comm]
      apply (lt_div_iff₀ hk).mp
      simpa [div_eq_mul_inv, mul_comm] using hlen
    exact_mod_cast hl
  · intro h ε hε x N
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    obtain ⟨n, hn, g, c, hc, heq, hlen⟩ := h x k N
    refine ⟨n, hn, g, c, hc, heq, ?_⟩
    have hkpos : (0 : ℝ) < k + 1 := by positivity
    have hke : 1 ≤ ε * (k + 1 : ℝ) := by
      have := (div_lt_iff₀ hε).mp hk
      nlinarith
    have hl : (W.length g : ℝ) < (r n : ℝ) / (k + 1) := by
      apply (lt_div_iff₀ hkpos).mpr
      exact_mod_cast (by simpa [mul_comm] using hlen)
    apply hl.trans_le
    apply (div_le_iff₀ hkpos).mpr
    have := mul_le_mul_of_nonneg_right hke (show (0 : ℝ) ≤ r n by positivity)
    nlinarith

theorem recursAt_mono (W : WordGeometry G) (r : ℕ → ℕ)
    {C D : ℕ → Set X} (hCD : ∀ n, C n ⊆ D n) {x : X}
    (h : RecursAt W r C x) : RecursAt W r D x := by
  intro k N
  obtain ⟨n, hn, g, c, hc, heq, hlen⟩ := h k N
  exact ⟨n, hn, g, c, hCD n hc, heq, hlen⟩

theorem recursAt_smul (W : WordGeometry G) (r : ℕ → ℕ) (hr : StrictMono r)
    (C : ℕ → Set X) (h : G) (x : X) :
    RecursAt W r C (h • x) ↔ RecursAt W r C x := by
  have forward (h : G) (x : X) (hx : RecursAt W r C x) :
      RecursAt W r C (h • x) := by
    intro k N
    obtain ⟨n, hn, g, c, hc, heq, hlen⟩ :=
      hx (2 * k + 1) (max N (2 * (k + 1) * W.length h + 1))
    refine ⟨n, (le_max_left _ _).trans hn, h * g, c, hc, ?_, ?_⟩
    · simp only [mul_smul, heq]
    · have hnr : n ≤ r n := hr.id_le n
      have hh := W.length_mul_le h g
      have hlarge : 2 * (k + 1) * W.length h < r n := by omega
      nlinarith
  constructor
  · intro hx
    simpa using forward h⁻¹ (h • x) hx
  · exact forward h x

/-- A finite union can recur only if one of its colors recurs at that point. -/
theorem recursAt_finite_union {ι : Type*} [Fintype ι]
    (W : WordGeometry G) (r : ℕ → ℕ) (D : ι → ℕ → Set X) (x : X)
    (hrec : RecursAt W r (fun n => ⋃ i, D i n) x) :
    ∃ i, RecursAt W r (D i) x := by
  classical
  by_contra! hnone
  have hbad : ∀ i, ∃ k N, ¬ ∃ n, N ≤ n ∧ ∃ g : G, ∃ c ∈ D i n,
      g • c = x ∧ (k + 1) * W.length g < r n := by
    simpa only [RecursAt, not_forall] using hnone
  choose k N hbad using hbad
  let K := Finset.univ.sup k
  let T := Finset.univ.sup N
  obtain ⟨n, hn, g, c, hc, heq, hlen⟩ := hrec K T
  obtain ⟨i, hci⟩ := Set.mem_iUnion.mp hc
  have hk : k i ≤ K := Finset.le_sup (f := k) (Finset.mem_univ i)
  have hN : N i ≤ T := Finset.le_sup (f := N) (Finset.mem_univ i)
  exact hbad i ⟨n, hN.trans hn, g, c, hci, heq,
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hlen⟩

variable [MeasurableSpace X] [MeasurableConstSMul G X]

theorem measurableSet_recursAt (W : WordGeometry G) (r : ℕ → ℕ)
    (C : ℕ → Set X) (hC : ∀ n, MeasurableSet (C n)) :
    MeasurableSet {x | RecursAt W r C x} := by
  letI := W.countable
  have heq : {x | RecursAt W r C x} =
      ⋂ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n),
        ⋃ g : G, ⋃ (_ : (k + 1) * W.length g < r n), g • C n := by
    ext x
    simp only [Set.mem_setOf_eq, RecursAt, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h k N
      obtain ⟨n, hn, g, c, hc, heq, hlen⟩ := h k N
      exact ⟨n, hn, g, hlen, c, hc, heq⟩
    · intro h k N
      obtain ⟨n, hn, g, hlen, c, hc, heq⟩ := h k N
      exact ⟨n, hn, g, c, hc, heq, hlen⟩
  rw [heq]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      MeasurableSet.iUnion fun g => MeasurableSet.iUnion fun _ =>
        (measurableEmbedding_const_smul g).measurableSet_image.mpr (hC n)

end RecurrentSections
