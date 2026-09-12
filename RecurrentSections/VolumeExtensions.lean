/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.VolumeBounds
import RecurrentSections.QuotientGeometry

namespace RecurrentSections
open scoped Pointwise
variable {G : Type*} [Group G] [DecidableEq G]

/-- A matching lower estimate at linearly dilated, shifted radii suffices.
Submultiplicativity absorbs the shift before the usual metric comparison. -/
theorem twoSidedPolynomialGrowth_of_shifted_lower (W : WordGeometry G)
    (d A B C : ℕ) (hB : 0 < B)
    (hupper : ∀ n, W.volume n ≤ A * (n + 1) ^ d)
    (hlower : ∀ n, (n + 1) ^ d ≤ C * W.volume (B * (n + 1))) :
    TwoSidedPolynomialGrowth W.volume := by
  have hu : TwoSidedPolynomialGrowth (fun n => (n + 1) ^ d) :=
    ⟨1, d, by omega, fun n => by simp⟩
  apply hu.of_comparison W.volume_mono (C * W.volume B) B A 1 hB
  · intro n
    calc
      (n + 1) ^ d ≤ C * W.volume (B * (n + 1)) := hlower n
      _ = C * W.volume (B + B * n) := by congr 2; ring
      _ ≤ C * (W.volume B * W.volume (B * n)) :=
        Nat.mul_le_mul_left C (W.volume_submultiplicative B (B * n))
      _ = _ := by ring
  · intro n
    simpa using hupper n

/-- Matching quotient and intrinsic subgroup volumes give matching ambient
volume when both directions of the subgroup's power distortion are controlled.
No nilpotence or centrality is assumed in this counting statement. -/
theorem twoSidedPolynomialGrowth_of_normal_subgroup_distortion
    (W : WordGeometry G) (N : Subgroup G) [N.Normal] [DecidableEq (G ⧸ N)]
    (V : WordGeometry N) (k A B : ℕ)
    (hupper : ∀ n : ℕ, ∀ g : N, (g : G) ∈ W.ball n → V.length g ≤ A * (n + 1) ^ k)
    (hcompression : ∀ r : ℕ, (V.ball (r ^ k)).image N.subtype ⊆ W.ball (B * (r + 1)))
    (hV : TwoSidedPolynomialGrowth V.volume)
    (hQ : TwoSidedPolynomialGrowth (W.map (QuotientGroup.mk' N) QuotientGroup.mk_surjective).volume) :
    TwoSidedPolynomialGrowth W.volume := by
  classical
  let q := QuotientGroup.mk' N
  let Q := W.map q QuotientGroup.mk_surjective
  obtain ⟨CV, e, hCV, hVe⟩ := hV
  obtain ⟨CQ, d, hCQ, hQd⟩ := hQ
  have hker_upper (n : ℕ) : W.kernelVolume q n ≤ V.volume (A * (n + 1) ^ k) := by
    have hsub : W.kernelBall q n ⊆ (V.ball (A * (n + 1) ^ k)).image N.subtype := by
      intro g hg
      obtain ⟨hg, hqg⟩ := Finset.mem_filter.mp hg
      have hN : g ∈ N := (QuotientGroup.eq_one_iff g).mp hqg
      exact Finset.mem_image.mpr ⟨⟨g, hN⟩,
        (V.mem_ball_iff_length_le _ _).mpr (hupper n ⟨g, hN⟩ hg), rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hker_lower (r : ℕ) : V.volume (r ^ k) ≤ W.kernelVolume q (B * (r + 1)) := by
    have hsub : (V.ball (r ^ k)).image N.subtype ⊆ W.kernelBall q (B * (r + 1)) := by
      intro g hg
      refine Finset.mem_filter.mpr ⟨hcompression r hg, ?_⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
      exact (QuotientGroup.eq_one_iff _).mpr a.property
    have hc : ((V.ball (r ^ k)).image N.subtype).card = (V.ball (r ^ k)).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    change (V.ball (r ^ k)).card ≤ (W.kernelBall q (B * (r + 1))).card
    rw [← hc]
    exact Finset.card_le_card hsub
  let U := CQ * CV * ((A + 1) * 2 ^ k) ^ e
  have hvolume_upper (n : ℕ) : W.volume n ≤ U * (n + 1) ^ (d + k * e) := by
    have hsmall : A * (2 * n + 1) ^ k + 1 ≤ ((A + 1) * 2 ^ k) * (n + 1) ^ k := by
      have hp : (2 * n + 1) ^ k ≤ (2 * (n + 1)) ^ k := by gcongr; omega
      have hpos : 1 ≤ (2 * (n + 1)) ^ k := by
        have hp : 0 < (2 * (n + 1)) ^ k := by positivity
        omega
      calc
        A * (2 * n + 1) ^ k + 1 ≤ (A + 1) * (2 * (n + 1)) ^ k := by nlinarith
        _ = _ := by rw [mul_pow]; ring
    calc
      W.volume n ≤ Q.volume n * W.kernelVolume q (2 * n) :=
        W.volume_le_map_volume_mul_kernelVolume q QuotientGroup.mk_surjective n
      _ ≤ Q.volume n * V.volume (A * (2 * n + 1) ^ k) := Nat.mul_le_mul_left _ (hker_upper _)
      _ ≤ (CQ * (n + 1) ^ d) * (CV * (A * (2 * n + 1) ^ k + 1) ^ e) :=
        Nat.mul_le_mul (hQd n).2 (hVe _).2
      _ ≤ (CQ * (n + 1) ^ d) * (CV * (((A + 1) * 2 ^ k) * (n + 1) ^ k) ^ e) := by gcongr
      _ = U * (n + 1) ^ (d + k * e) := by
        dsimp [U]
        rw [mul_pow, ← pow_mul, pow_add]
        ring
  have hvolume_lower (n : ℕ) :
      (n + 1) ^ (d + k * e) ≤ (CQ * CV) * W.volume ((2 * B + 1) * (n + 1)) := by
    have hv : ((n + 1) ^ k) ^ e ≤ CV * V.volume ((n + 1) ^ k) :=
      (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (hVe _).1
    calc
      (n + 1) ^ (d + k * e) = (n + 1) ^ d * ((n + 1) ^ k) ^ e := by rw [pow_add, pow_mul]
      _ ≤ (CQ * Q.volume n) * (CV * V.volume ((n + 1) ^ k)) :=
        Nat.mul_le_mul (hQd n).1 hv
      _ = (CQ * CV) * (Q.volume n * V.volume ((n + 1) ^ k)) := by ring
      _ ≤ (CQ * CV) * (Q.volume n * W.kernelVolume q (B * (n + 1 + 1))) := by
        gcongr
        exact hker_lower (n + 1)
      _ ≤ (CQ * CV) * W.volume (n + B * (n + 1 + 1)) :=
        Nat.mul_le_mul_left _ (W.map_volume_mul_kernelVolume_le q QuotientGroup.mk_surjective _ _)
      _ ≤ (CQ * CV) * W.volume ((2 * B + 1) * (n + 1)) := by
        gcongr
        exact W.volume_mono (by nlinarith)
  exact twoSidedPolynomialGrowth_of_shifted_lower W (d + k * e) U (2 * B + 1)
    (CQ * CV) (by omega) hvolume_upper hvolume_lower

end RecurrentSections
