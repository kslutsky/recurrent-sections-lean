/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.StandardInputs
import MetricGeometry.CommonEmbedding

/-! # Packing and covering from volume doubling

The counting arguments require only a doubling bound on word balls.
Polynomial growth enters through the separate published volume-growth
theorem; none of the counting lemmas assumes a Borel action.
-/

namespace RecurrentSections

open scoped Pointwise

/-- Two-sided polynomial bounds, with an integer constant absorbing both
the upper constant and the reciprocal of the lower constant. -/
def TwoSidedPolynomialGrowth (v : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n, (n + 1) ^ d ≤ C * v n ∧ v n ≤ C * (n + 1) ^ d

/-- The shift by one includes small radii and finite groups. -/
def VolumeDoubling (v : ℕ → ℕ) (D : ℕ) : Prop :=
  ∀ n, v (2 * n + 1) ≤ D * v n

theorem TwoSidedPolynomialGrowth.doubling {v : ℕ → ℕ}
    (h : TwoSidedPolynomialGrowth v) : ∃ D, 0 < D ∧ VolumeDoubling v D := by
  obtain ⟨C, d, hC, h⟩ := h
  refine ⟨C * C * 2 ^ d, by positivity, fun n => ?_⟩
  calc
    v (2 * n + 1) ≤ C * (2 * n + 1 + 1) ^ d := (h _).2
    _ = C * 2 ^ d * (n + 1) ^ d := by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, mul_pow]; ring
    _ ≤ C * 2 ^ d * (C * v n) := Nat.mul_le_mul_left _ (h n).1
    _ = (C * C * 2 ^ d) * v n := by ring

theorem VolumeDoubling.iterate {v : ℕ → ℕ} {D : ℕ}
    (h : VolumeDoubling v D) (k n : ℕ) :
    v (2 ^ k * n + (2 ^ k - 1)) ≤ D ^ k * v n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < 2 ^ k := by positivity
    have heq : 2 ^ (k + 1) * n + (2 ^ (k + 1) - 1) =
        2 * (2 ^ k * n + (2 ^ k - 1)) + 1 := by
      rw [pow_succ, mul_assoc, mul_left_comm (2 ^ k) 2 n, mul_add]
      omega
    rw [heq]
    exact (h _).trans (by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm]
      using Nat.mul_le_mul_left D ih)

variable {G : Type*} [Group G] [DecidableEq G]

namespace WordGeometry

theorem length_eq_zero (W : WordGeometry G) {g : G} : W.length g = 0 ↔ g = 1 := by
  constructor
  · intro h
    have := (W.mem_ball_iff_length_le g 0).mpr (Nat.le_of_eq h)
    simpa [ball] using this
  · rintro rfl
    exact W.length_one

/-- The left word metric divided by a positive integer. Kept as an
explicit structure to avoid selecting a generating set by typeclass search. -/
noncomputable abbrev scaledMetric (W : WordGeometry G) (R : ℕ) (hR : 0 < R) :
    MetricSpace G where
  dist x y := (W.length (x⁻¹ * y) : ℝ) / R
  dist_self x := by simp [W.length_one]
  dist_comm x y := by
    rw [← W.length_inv (x⁻¹ * y)]
    simp
  dist_triangle x y z := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg R)
    exact_mod_cast (show W.length (x⁻¹ * z) ≤
      W.length (x⁻¹ * y) + W.length (y⁻¹ * z) from by
        simpa [mul_assoc] using W.length_mul_le (x⁻¹ * y) (y⁻¹ * z))
  eq_of_dist_eq_zero := by
    intro x y h
    have : W.length (x⁻¹ * y) = 0 := by
      have := (div_eq_zero_iff.mp h).resolve_right (by exact_mod_cast hR.ne')
      exact_mod_cast this
    exact inv_mul_eq_one.mp (W.length_eq_zero.mp this)

end WordGeometry

/-- The exact finite metric space used at each scale. -/
noncomputable abbrev scaledBallMetric (W : WordGeometry G) (R : ℕ) (hR : 0 < R) :
    MetricSpace {g // g ∈ W.ball (3 * R)} :=
  letI := W.scaledMetric R hR
  inferInstance

/-- Disjoint right translates of a word ball fit in the enlarged ambient
ball. This finite counting estimate is independent of volume growth. -/
theorem card_mul_volume_le (W : WordGeometry G) (L m : ℕ)
    {I : Type*} [Fintype I] (f : I → G)
    (hf : ∀ i, W.length (f i) ≤ L)
    (hsep : ∀ i j, i ≠ j → 2 * m < W.length (f j * (f i)⁻¹)) :
    Fintype.card I * W.volume m ≤ W.volume (L + m) := by
  let F : I × {g // g ∈ W.ball m} → {g // g ∈ W.ball (L + m)} :=
    fun p => ⟨p.2.1 * f p.1, by
      simpa [Nat.add_comm] using W.mul_mem_ball p.2.2
        ((W.mem_ball_iff_length_le _ _).mpr (hf p.1))⟩
  have hF : Function.Injective F := by
    rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ heq
    have hab : a * f i = b * f j := congrArg Subtype.val heq
    have hij : i = j := by
      by_contra hne
      have hid : f j * (f i)⁻¹ = b⁻¹ * a := by
        calc
          f j * (f i)⁻¹ = b⁻¹ * (b * f j) * (f i)⁻¹ := by group
          _ = b⁻¹ * (a * f i) * (f i)⁻¹ := by rw [hab]
          _ = b⁻¹ * a := by group
      have hh := W.mul_mem_ball (W.inv_mem_ball hb) ha
      have hlen := (W.mem_ball_iff_length_le _ _).mp hh
      have hgt := hsep i j hne
      rw [hid] at hgt
      omega
    subst j
    have : a = b := mul_right_cancel hab
    subst b
    rfl
  simpa [WordGeometry.volume, Fintype.card_prod] using Fintype.card_le_of_injective F hF

/-- The right-word packing bound used by the recurrence construction
follows from volume doubling, with no exceptional radius. -/
theorem groupPacking_of_doubling {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) {D : ℕ}
    (hD : VolumeDoubling W.volume D) : GroupPacking W (D ^ 5) := by
  intro R _ I _ f hf hsep
  let m := R / 2
  have hcount := card_mul_volume_le W (7 * R) m f hf (fun i j hij =>
    lt_of_le_of_lt (by dsimp [m]; omega) (hsep i j hij))
  have hrad : 7 * R + m ≤ 2 ^ 5 * m + (2 ^ 5 - 1) := by dsimp [m]; omega
  have hbound := (W.volume_mono hrad).trans (hD.iterate 5 m)
  exact Nat.le_of_mul_le_mul_right (hcount.trans hbound) (W.volume_pos m)

/-- A quantitative internal net for a rescaled word ball. The number of
centers depends on the requested resolution, but not on the scale. -/
theorem scaledBall_cover (W : WordGeometry G) {D : ℕ}
    (hD : VolumeDoubling W.volume D) (R q k : ℕ)
    (hR : 0 < R) (hq : 0 < q) (hk : 4 * q ≤ 2 ^ k) :
    letI := scaledBallMetric W R hR
    ∃ N : Finset {g // g ∈ W.ball (3 * R)}, N.card ≤ D ^ k ∧
      ∀ x, ∃ y ∈ N, dist x y ≤ (2 * (R / q) : ℕ) / (R : ℝ) := by
  letI := scaledBallMetric W R hR
  let m := R / q
  obtain ⟨N, _, hsep, hcover⟩ := MetricGeometry.exists_separated_net
    (Finset.univ : Finset {g // g ∈ W.ball (3 * R)})
    (δ := (2 * m : ℕ) / (R : ℝ)) (by positivity)
  refine ⟨N, ?_, fun x => hcover x (Finset.mem_univ _)⟩
  let f : {x // x ∈ N} → G := fun i => i.1.1⁻¹
  have hf (i : {x // x ∈ N}) : W.length (f i) ≤ 3 * R := by
    simpa [f, W.length_inv] using (W.mem_ball_iff_length_le _ _).mp i.1.2
  have hsp (i j : {x // x ∈ N}) (hij : i ≠ j) :
      2 * m < W.length (f j * (f i)⁻¹) := by
    have hh := hsep j.1 j.2 i.1 i.2 (fun heq => hij (Subtype.ext heq.symm))
    change (2 * m : ℕ) / (R : ℝ) < (W.length (j.1.1⁻¹ * i.1.1) : ℝ) / R at hh
    have := (div_lt_div_iff_of_pos_right (show (0 : ℝ) < R by exact_mod_cast hR)).mp hh
    simpa [f] using (show 2 * m < W.length (j.1.1⁻¹ * i.1.1) by exact_mod_cast this)
  have hcount := card_mul_volume_le W (3 * R) m f hf hsp
  have hsmall : m ≤ R := Nat.div_le_self _ _
  have hquot : R < q * (m + 1) := by
    dsimp [m]
    have := Nat.mod_lt R hq
    have := Nat.mod_add_div R q
    nlinarith
  have hp : 0 < 2 ^ k := by positivity
  have hrad : 3 * R + m ≤ 2 ^ k * m + (2 ^ k - 1) := by
    have hmul := Nat.mul_le_mul_right (m + 1) hk
    have hpow : 2 ^ k - 1 + 1 = 2 ^ k := by omega
    nlinarith
  have hbound := (W.volume_mono hrad).trans (hD.iterate k m)
  simpa using Nat.le_of_mul_le_mul_right (hcount.trans hbound) (W.volume_pos m)

/-- Volume doubling verifies the hypotheses of the common compact
embedding theorem. The radius sequence need only be positive. -/
theorem scaledModels_of_doubling {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G)
    {D : ℕ} (hD : VolumeDoubling W.volume D) (r : ℕ → ℕ)
    (hr : ∀ n, 0 < r n) :
    ∃ (K : Type) (metric : MetricSpace K),
      letI := metric
      CompactSpace K ∧ ∃ φ : ℕ → G → K, ScaledModels W r φ := by
  classical
  let A (n : ℕ) := {g // g ∈ W.ball (3 * r n)}
  let metric : ∀ n, MetricSpace (A n) := fun n => scaledBallMetric W (r n) (hr n)
  letI := metric
  have hcompact (n : ℕ) : CompactSpace (A n) := by
    letI : Fintype (A n) := inferInstanceAs (Fintype {g // g ∈ W.ball (3 * r n)})
    exact Finite.compactSpace
  have hnonempty (n : ℕ) : Nonempty (A n) := ⟨⟨1, W.one_mem_ball _⟩⟩
  have hdiam : ∃ C : ℝ, ∀ n (x y : A n), dist x y ≤ C := by
    refine ⟨6, fun n x y => ?_⟩
    change (W.length (x.1⁻¹ * y.1) : ℝ) / r n ≤ 6
    apply (div_le_iff₀ (show (0 : ℝ) < r n by exact_mod_cast hr n)).mpr
    have hlen := (W.mem_ball_iff_length_le _ _).mp
      (W.mul_mem_ball (W.inv_mem_ball x.2) y.2)
    have : W.length (x.1⁻¹ * y.1) ≤ 6 * r n := by omega
    exact_mod_cast this
  have hcover : MetricGeometry.UniformlyCoverable A := by
    intro ε hε
    obtain ⟨q, hq⟩ := exists_nat_gt (2 / ε)
    have hqpos : 0 < q := by
      have : (0 : ℝ) < q := lt_trans (by positivity : (0 : ℝ) < 2 / ε) hq
      exact_mod_cast this
    have hεq : 2 < ε * q := by
      have := (div_lt_iff₀ hε).mp hq
      linarith
    refine ⟨D ^ (4 * q), fun n => ?_⟩
    obtain ⟨N, hN, hcov⟩ := scaledBall_cover W hD (r n) q (4 * q)
      (hr n) hqpos (Nat.lt_two_pow_self.le)
    refine ⟨N, hN, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hcov x
    refine ⟨y, hy, hxy.trans ?_⟩
    apply (div_le_iff₀ (show (0 : ℝ) < r n by exact_mod_cast hr n)).mpr
    have hm : ((r n / q : ℕ) : ℝ) * q ≤ r n := by
      exact_mod_cast Nat.div_mul_le_self (r n) q
    have hmul := mul_le_mul_of_nonneg_left hm hε.le
    have hnonneg : (0 : ℝ) ≤ (r n / q : ℕ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  obtain ⟨K, mK, hK, f, hf⟩ := MetricGeometry.commonCompactEmbeddingTheorem A metric hcompact hnonempty hdiam hcover
  letI := mK
  refine ⟨K, mK, hK, ?_⟩
  let φ (n : ℕ) (g : G) :=
    if hg : g ∈ W.ball (3 * r n) then f n ⟨g, hg⟩ else f n ⟨1, W.one_mem_ball _⟩
  refine ⟨φ, fun n g h hg hh => ?_⟩
  dsimp only [φ]
  rw [dif_pos hg, dif_pos hh, (hf n).dist_eq]
  change ((W.length (g⁻¹ * h) : ℝ) / r n) * r n = _
  exact div_mul_cancel₀ _ (by exact_mod_cast (hr n).ne')

/-- The published polynomial-group volume theorem, in an all-radius
integer normalization. This deep input is not proved in this project.

Source: E. Breuillard, *Geometry of locally compact groups of polynomial
growth and shape of large balls*, Groups Geom. Dyn. **8** (2014), 669–732,
Theorem 1.1 (Volume asymptotics), p. 670.
https://doi.org/10.4171/GGD/244
https://ems.press/content/serial-article-files/29707
Specialize to the discrete group, counting Haar measure, and the finite
symmetric generating set. The positive limit `|B(n)| / n^d` supplies
matching upper and lower bounds; enlarge one integer constant to absorb
small radii and replace `n^d` by `(n+1)^d`. The common exponent need not
be the exponent in the initial upper bound. This is distinct from Gromov's
polynomial-growth/virtual-nilpotence equivalence. -/
def PolynomialVolumeTheorem {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) : Prop :=
  PolynomialGrowth W.volume → TwoSidedPolynomialGrowth W.volume

/-- Doubling implies a polynomial upper bound, by the elementary
dilation lemma. This direction needs no structure theorem for groups. -/
theorem polynomialGrowth_of_volumeDoubling {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) {D : ℕ} (hD : VolumeDoubling W.volume D) :
    PolynomialGrowth W.volume := by
  apply polynomialGrowth_of_dilation_bound W.volume W.volume_mono (D ^ 3) 0
  intro n _
  exact (W.volume_mono (show 5 * n ≤ 2 ^ 3 * n + (2 ^ 3 - 1) by omega)).trans
    (hD.iterate 3 n)

/-- All geometry required by the construction follows from volume
doubling, without an external embedding theorem. -/
theorem polynomialGeometry_of_volumeDoubling {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) {D : ℕ} (hD : VolumeDoubling W.volume D) : PolynomialGeometry W := by
  have hDpos : 0 < D := by
    have hh := hD 0
    have hv := W.volume_pos 1
    by_contra! hz
    have heq : D = 0 := Nat.eq_zero_of_le_zero hz
    simp [heq] at hh
    omega
  exact {
    packing := fun _ => ⟨D ^ 5, by positivity, groupPacking_of_doubling W hD⟩
    models := fun _ r _ hr => scaledModels_of_doubling W hD r hr }

/-- Both fields of the geometry interface are now derived from the sole
remaining volume-growth input. Common compact embedding is proved. -/
theorem polynomialGeometry_of_standard_theorems {G : Type} [Group G] [DecidableEq G]
    (W : WordGeometry G) (volume : PolynomialVolumeTheorem W) : PolynomialGeometry W where
  packing hp := by
    obtain ⟨D, hDpos, hD⟩ := (volume hp).doubling
    exact ⟨D ^ 5, by positivity, groupPacking_of_doubling W hD⟩
  models hp r _ hr := by
    obtain ⟨D, _, hD⟩ := (volume hp).doubling
    exact scaledModels_of_doubling W hD r hr

end RecurrentSections
