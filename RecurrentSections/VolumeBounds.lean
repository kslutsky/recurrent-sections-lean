/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.PolynomialGeometry
import RecurrentSections.GrowthComparison

/-! # Normalizing two-sided polynomial volume bounds

These lemmas prove the all-radius and integer-constant normalization of
positive polynomial volume asymptotics, and the finite-group case.
The general implication from a polynomial upper bound to matching lower
bounds is not inferred from an arbitrary growth function.
-/

namespace RecurrentSections
open Set Filter Topology

/-- Matching polynomial bounds pass across a comparison in both directions.
The lower estimate uses monotonicity of the target and a positive dilation;
it preserves the original exponent, although that exponent is existential
in `TwoSidedPolynomialGrowth`. -/
theorem TwoSidedPolynomialGrowth.of_comparison {u v : ℕ → ℕ}
    (h : TwoSidedPolynomialGrowth u) (hv : Monotone v)
    (A B C D : ℕ) (hB : 0 < B)
    (huv : ∀ n, u n ≤ A * v (B * n)) (hvu : ∀ n, v n ≤ C * u (D * n)) :
    TwoSidedPolynomialGrowth v := by
  obtain ⟨K, d, hK, hb⟩ := h
  let M := B ^ d * K * A + C * K * (D + 1) ^ d + 1
  refine ⟨M, d, by dsimp [M]; omega, fun n => ⟨?_, ?_⟩⟩
  · have hdiv : n + 1 ≤ B * (n / B + 1) := by
      have := Nat.mod_lt n hB
      have := Nat.mod_add_div n B
      nlinarith
    calc
      (n + 1) ^ d ≤ (B * (n / B + 1)) ^ d := Nat.pow_le_pow_left hdiv d
      _ = B ^ d * (n / B + 1) ^ d := mul_pow _ _ _
      _ ≤ B ^ d * (K * u (n / B)) := Nat.mul_le_mul_left _ (hb _).1
      _ ≤ B ^ d * (K * (A * v (B * (n / B)))) := by gcongr; exact huv _
      _ ≤ B ^ d * (K * (A * v n)) := by gcongr; exact hv (Nat.mul_div_le n B)
      _ = (B ^ d * K * A) * v n := by ring
      _ ≤ M * v n := Nat.mul_le_mul_right _ (by dsimp [M]; omega)
  · calc
      v n ≤ C * u (D * n) := hvu n
      _ ≤ C * (K * (D * n + 1) ^ d) := Nat.mul_le_mul_left C (hb _).2
      _ ≤ C * (K * ((D + 1) * (n + 1)) ^ d) := by gcongr; nlinarith
      _ = (C * K * (D + 1) ^ d) * (n + 1) ^ d := by rw [mul_pow]; ring
      _ ≤ M * (n + 1) ^ d := Nat.mul_le_mul_right _ (by dsimp [M]; omega)

/-- Finitely many exceptional radii can be absorbed into one integer
constant, provided the volume is everywhere positive. -/
theorem twoSidedPolynomialGrowth_of_eventually {v : ℕ → ℕ}
    (hv : ∀ n, 0 < v n) (C d : ℕ)
    (h : ∀ᶠ n in atTop, (n + 1) ^ d ≤ C * v n ∧ v n ≤ C * (n + 1) ^ d) :
    TwoSidedPolynomialGrowth v := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  let K := C + (M + 1) ^ d + (∑ i ∈ Finset.range M, v i) + 1
  have hCK : C ≤ K := by dsimp [K]; omega
  refine ⟨K, d, by dsimp [K]; omega, fun n => ?_⟩
  by_cases hn : M ≤ n
  · exact ⟨(hM n hn).1.trans (Nat.mul_le_mul_right _ hCK),
      (hM n hn).2.trans (Nat.mul_le_mul_right _ hCK)⟩
  · have hsum : v n ≤ ∑ i ∈ Finset.range M, v i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (v i)) (Finset.mem_range.2 (by omega))
    have hp : (n + 1) ^ d ≤ (M + 1) ^ d := Nat.pow_le_pow_left (by omega) d
    have hlo : (n + 1) ^ d ≤ K := by dsimp [K]; omega
    have hhi : v n ≤ K := by dsimp [K]; omega
    exact ⟨hlo.trans (Nat.le_mul_of_pos_right K (hv n)),
      hhi.trans (Nat.le_mul_of_pos_right K (by positivity))⟩

/-- Positive asymptotic ratios give eventual integer multiplicative
bounds in both directions. Neither sequence is assumed monotone. -/
theorem eventual_mul_bounds_of_tendsto_ratio {u v : ℕ → ℕ} {c : ℝ}
    (hu : ∀ᶠ n in atTop, 0 < u n) (hc : 0 < c)
    (hlim : Tendsto (fun n => (v n : ℝ) / u n) atTop (𝓝 c)) :
    ∃ C : ℕ, ∀ᶠ n in atTop, u n ≤ C * v n ∧ v n ≤ C * u n := by
  obtain ⟨C, hC⟩ := exists_nat_gt (max (c + 1) (1 / (c / 2)))
  have hCupper : c + 1 ≤ (C : ℝ) := (le_max_left _ _).trans hC.le
  have hClower : 1 / (c / 2) ≤ (C : ℝ) := (le_max_right _ _).trans hC.le
  have hhalf : 0 < c / 2 := by positivity
  have hscale : 1 ≤ (C : ℝ) * (c / 2) := (div_le_iff₀ hhalf).1 hClower
  have hlow := (tendsto_order.1 hlim).1 (c / 2) (by linarith)
  have hhigh := (tendsto_order.1 hlim).2 (c + 1) (by linarith)
  refine ⟨C, ?_⟩
  filter_upwards [hu, hlow, hhigh] with n hun hln hhn
  have hur : (0 : ℝ) < u n := by exact_mod_cast hun
  have hlo : c / 2 * (u n : ℝ) ≤ v n := (le_div_iff₀ hur).1 hln.le
  have hhi : (v n : ℝ) ≤ (c + 1) * u n := (div_le_iff₀ hur).1 hhn.le
  have hlower : (u n : ℝ) ≤ (C : ℝ) * v n := by
    calc
      (u n : ℝ) = 1 * u n := by ring
      _ ≤ ((C : ℝ) * (c / 2)) * u n := mul_le_mul_of_nonneg_right hscale hur.le
      _ = (C : ℝ) * (c / 2 * u n) := by ring
      _ ≤ (C : ℝ) * v n := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg _)
  have hupper : (v n : ℝ) ≤ (C : ℝ) * u n :=
    hhi.trans (mul_le_mul_of_nonneg_right hCupper hur.le)
  exact ⟨by exact_mod_cast hlower, by exact_mod_cast hupper⟩

/-- The normalization of polynomial volume asymptotics as usually
published, with denominator `n^d`, including the exceptional radius zero. -/
theorem twoSidedPolynomialGrowth_of_tendsto_ratio {v : ℕ → ℕ}
    (hv : ∀ n, 0 < v n) (d : ℕ) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n => (v n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 c)) :
    TwoSidedPolynomialGrowth v := by
  have hlim' : Tendsto (fun n => (v n : ℝ) / ((n ^ d : ℕ) : ℝ)) atTop (𝓝 c) := by
    simpa only [Nat.cast_pow] using hlim
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n ^ d := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    positivity
  obtain ⟨C, hC⟩ := eventual_mul_bounds_of_tendsto_ratio hpos hc hlim'
  apply twoSidedPolynomialGrowth_of_eventually hv (2 ^ d * C) d
  filter_upwards [hC, eventually_ge_atTop 1] with n hn hposn
  have hshift : (n + 1) ^ d ≤ 2 ^ d * n ^ d := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) d
  constructor
  · calc
      (n + 1) ^ d ≤ 2 ^ d * n ^ d := hshift
      _ ≤ 2 ^ d * (C * v n) := Nat.mul_le_mul_left _ hn.1
      _ = (2 ^ d * C) * v n := by ring
  · calc
      v n ≤ C * n ^ d := hn.2
      _ ≤ C * (n + 1) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
      _ ≤ (2 ^ d * C) * (n + 1) ^ d := by gcongr; exact Nat.le_mul_of_pos_left C (by positivity)

/-- Finite groups have two-sided volume bounds of degree zero. -/
theorem twoSidedPolynomialGrowth_of_finite {G : Type*} [Group G] [DecidableEq G]
    [Finite G] (W : WordGeometry G) : TwoSidedPolynomialGrowth W.volume := by
  let := Fintype.ofFinite G
  refine ⟨Fintype.card G, 0, Fintype.card_pos, fun n => ?_⟩
  simp only [pow_zero, mul_one]
  exact ⟨Nat.mul_pos Fintype.card_pos (W.volume_pos n),
    Finset.card_le_univ (W.ball n)⟩

/-- In the finite case the exact formerly external input is discharged. -/
theorem polynomialVolumeTheorem_of_finite {G : Type} [Group G] [DecidableEq G]
    [Finite G] (W : WordGeometry G) : PolynomialVolumeTheorem W :=
  fun _ => twoSidedPolynomialGrowth_of_finite W

/-- Matching polynomial bounds are invariant under passage to finite index.
Both directions preserve the common exponent in the numerical comparison. -/
theorem twoSidedPolynomialGrowth_iff_subgroup {G : Type*} [Group G] [DecidableEq G]
    (W : WordGeometry G) (N : Subgroup G) [N.FiniteIndex] (V : WordGeometry N) :
    TwoSidedPolynomialGrowth W.volume ↔ TwoSidedPolynomialGrowth V.volume := by
  obtain ⟨L, hLpos, hL⟩ := V.exists_volume_le_of_injective W N.subtype Subtype.val_injective
  obtain ⟨A, B, _, hBpos, hAB⟩ := W.exists_volume_le_subgroup N V
  constructor
  · intro h
    exact h.of_comparison V.volume_mono A B 1 L hBpos hAB (by simpa using hL)
  · intro h
    exact h.of_comparison W.volume_mono 1 L A B hLpos (by simpa using hL) hAB

/-- Changing a finite symmetric generating set does not change the existence
of matching polynomial bounds. -/
theorem twoSidedPolynomialGrowth_iff_wordGeometry {G : Type*} [Group G] [DecidableEq G]
    (W V : WordGeometry G) :
    TwoSidedPolynomialGrowth W.volume ↔ TwoSidedPolynomialGrowth V.volume := by
  obtain ⟨L, hLpos, hL⟩ := W.exists_volume_le_of_injective V (MonoidHom.id G) Function.injective_id
  obtain ⟨M, hMpos, hM⟩ := V.exists_volume_le_of_injective W (MonoidHom.id G) Function.injective_id
  constructor
  · intro h
    exact h.of_comparison V.volume_mono 1 L 1 M hLpos (by simpa using hL) (by simpa using hM)
  · intro h
    exact h.of_comparison W.volume_mono 1 M 1 L hMpos (by simpa using hM) (by simpa using hL)

/-- Matching polynomial volume bounds are invariant under group isomorphism. -/
theorem twoSidedPolynomialGrowth_iff_mulEquiv {G H : Type*} [Group G] [Group H]
    [DecidableEq G] [DecidableEq H] (W : WordGeometry G) (V : WordGeometry H) (e : G ≃* H) :
    TwoSidedPolynomialGrowth W.volume ↔ TwoSidedPolynomialGrowth V.volume := by
  obtain ⟨L, hLpos, hL⟩ := W.exists_volume_le_of_injective V e.toMonoidHom e.injective
  obtain ⟨M, hMpos, hM⟩ := V.exists_volume_le_of_injective W e.symm.toMonoidHom e.symm.injective
  constructor
  · intro h
    exact h.of_comparison V.volume_mono 1 L 1 M hLpos (by simpa using hL) (by simpa using hM)
  · intro h
    exact h.of_comparison W.volume_mono 1 M 1 L hMpos (by simpa using hM) (by simpa using hL)

end RecurrentSections
