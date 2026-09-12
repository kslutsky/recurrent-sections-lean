/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordGeometry
import Mathlib.GroupTheory.Schreier

/-! # Comparison of finite word metrics

Homomorphisms are Lipschitz for finite word metrics. A finite-index subgroup
has comparable word-ball cardinalities, without a normality assumption.
These are the elementary word-metric comparisons used in passing polynomial
volume bounds between finite-index subgroups and their ambient groups.
-/

namespace RecurrentSections.WordGeometry

open scoped Pointwise

variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]

theorem closure_generators (W : WordGeometry G) :
    Subgroup.closure (W.generators : Set G) = ⊤ := by
  apply top_unique
  intro g htop
  clear htop
  obtain ⟨n, hn⟩ := W.generates g
  induction n generalizing g with
  | zero =>
    have hg : g = 1 := by simpa using hn
    subst g
    exact Subgroup.one_mem _
  | succ n ih =>
    rw [pow_succ] at hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hn
    exact Subgroup.mul_mem _ (ih ha) (Subgroup.subset_closure hb)

theorem fg (W : WordGeometry G) : Group.FG G :=
  ⟨W.generators, W.closure_generators⟩

/-- A finite generating set can be made symmetric and contain the identity. -/
theorem nonempty_ofFG (G : Type*) [Group G] [DecidableEq G] [Group.FG G] :
    Nonempty (WordGeometry G) := by
  classical
  obtain ⟨S, hS⟩ := Group.FG.out (G := G)
  let T := insert 1 (S ∪ S⁻¹)
  have hTinv : ∀ g ∈ T, g⁻¹ ∈ T := by
    intro g hg
    simpa only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_inv',
      inv_eq_one, inv_inv, or_comm, or_left_comm] using hg
  refine ⟨⟨T, by simp [T], hTinv, fun g => ?_⟩⟩
  have hg : g ∈ Subgroup.closure (S : Set G) := hS ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact ⟨1, by simpa [T] using (Or.inr (Or.inl hg) : g = 1 ∨ g ∈ S ∨ g⁻¹ ∈ S)⟩
  | one => exact ⟨0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by simpa only [pow_add] using Finset.mul_mem_mul hm hn⟩
  | inv a hmem ha =>
    clear hmem
    obtain ⟨n, hn⟩ := ha
    refine ⟨n, ?_⟩
    induction n generalizing a with
    | zero => simpa using hn
    | succ n ih =>
      rw [pow_succ] at hn
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_mul.mp hn
      simpa only [pow_succ', mul_inv_rev] using Finset.mul_mem_mul (hTinv y hy) (ih x hx)

noncomputable def ofFG (G : Type*) [Group G] [DecidableEq G] [Group.FG G] :
    WordGeometry G := Classical.choice (nonempty_ofFG G)

theorem image_ball_subset (W : WordGeometry G) (V : WordGeometry H) (f : G →* H)
    {L : ℕ} (hL : ∀ g ∈ W.generators, f g ∈ V.ball L) (n : ℕ) :
    (W.ball n).image f ⊆ V.ball (L * n) := by
  intro h hh
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
  clear hh
  induction n generalizing g with
  | zero =>
    have hg1 : g = 1 := by simpa [ball] using hg
    subst g
    simpa using V.one_mem_ball 0
  | succ n ih =>
    rw [ball, pow_succ] at hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hg
    simpa only [map_mul, Nat.mul_succ] using V.mul_mem_ball (ih a ha) (hL b hb)

/-- The constant is independent of the element and radius. -/
theorem exists_length_map_le (W : WordGeometry G) (V : WordGeometry H) (f : G →* H) :
    ∃ L : ℕ, 0 < L ∧ ∀ g, V.length (f g) ≤ L * W.length g := by
  let L := 1 + ∑ g ∈ W.generators, V.length (f g)
  have hL (g : G) (hg : g ∈ W.generators) : f g ∈ V.ball L := by
    apply (V.mem_ball_iff_length_le _ _).mpr
    have hsum : V.length (f g) ≤ ∑ x ∈ W.generators, V.length (f x) :=
      Finset.single_le_sum (fun x _ => Nat.zero_le (V.length (f x))) hg
    dsimp [L]
    omega
  refine ⟨L, by dsimp [L]; omega, fun g => ?_⟩
  apply (V.mem_ball_iff_length_le _ _).mp
  exact W.image_ball_subset V f hL _ (Finset.mem_image.mpr
    ⟨g, (W.mem_ball_iff_length_le _ _).mpr le_rfl, rfl⟩)

theorem exists_volume_le_of_injective (W : WordGeometry G) (V : WordGeometry H)
    (f : G →* H) (hf : Function.Injective f) :
    ∃ L : ℕ, 0 < L ∧ ∀ n, W.volume n ≤ V.volume (L * n) := by
  obtain ⟨L, hL, hlength⟩ := W.exists_length_map_le V f
  refine ⟨L, hL, fun n => ?_⟩
  rw [volume, ← Finset.card_image_of_injective _ hf]
  apply Finset.card_le_card
  intro h hh
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
  apply (V.mem_ball_iff_length_le _ _).mpr
  exact (hlength g).trans (Nat.mul_le_mul_left L ((W.mem_ball_iff_length_le _ _).mp hg))

/-- Word-ball cardinalities in a finite-index subgroup control ambient balls.
No normality hypothesis is required. The multiplicative constant is the
number of representatives in a finite right transversal. -/
theorem exists_volume_le_subgroup (W : WordGeometry G) (N : Subgroup G)
    [N.FiniteIndex] (V : WordGeometry N) :
    ∃ K L : ℕ, 0 < K ∧ 0 < L ∧ ∀ n, W.volume n ≤ K * V.volume (L * n) := by
  classical
  obtain ⟨R₀, hR, hR1⟩ := N.exists_isComplement_right 1
  let R := hR.finite_right.toFinset
  have hRmem (g : G) : g ∈ R ↔ g ∈ R₀ := Set.Finite.mem_toFinset _
  let t (g : G) : N := ⟨g * (hR.toRightFun g : G)⁻¹, hR.mul_inv_toRightFun_mem g⟩
  let L := 1 + ∑ g ∈ R * W.generators, V.length (t g)
  have hL (g : G) (hg : g ∈ R * W.generators) : t g ∈ V.ball L := by
    apply (V.mem_ball_iff_length_le _ _).mpr
    have hsum : V.length (t g) ≤ ∑ x ∈ R * W.generators, V.length (t x) :=
      Finset.single_le_sum (fun x _ => Nat.zero_le (V.length (t x))) hg
    dsimp [L]
    omega
  have hcover (n : ℕ) (g : G) (hg : g ∈ W.ball n) :
      ∃ h ∈ V.ball (L * n), ∃ r ∈ R, (h : G) * r = g := by
    induction n generalizing g with
    | zero =>
      have hg1 : g = 1 := by simpa [ball] using hg
      subst g
      exact ⟨1, V.one_mem_ball 0, 1, (hRmem 1).mpr hR1, by simp⟩
    | succ n ih =>
      rw [ball, pow_succ] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hg
      obtain ⟨h, hh, r, hr, rfl⟩ := ih a ha
      refine ⟨h * t (r * b), ?_, hR.toRightFun (r * b),
        (hRmem _).mpr (hR.toRightFun _).property, ?_⟩
      · simpa only [Nat.mul_succ] using V.mul_mem_ball hh (hL _ (Finset.mul_mem_mul hr hb))
      · simp only [Subgroup.coe_mul, t]
        group
  refine ⟨R.card, L, Finset.card_pos.mpr ⟨1, (hRmem 1).mpr hR1⟩,
    by dsimp [L]; omega, fun n => ?_⟩
  calc
    W.volume n ≤ (((V.ball (L * n)) ×ˢ R).image (fun p => (p.1 : G) * p.2)).card := by
      apply Finset.card_le_card
      intro g hg
      obtain ⟨h, hh, r, hr, rfl⟩ := hcover n g hg
      exact Finset.mem_image.mpr ⟨(h, r), Finset.mem_product.mpr ⟨hh, hr⟩, rfl⟩
    _ ≤ ((V.ball (L * n)) ×ˢ R).card := Finset.card_image_le
    _ = R.card * V.volume (L * n) := by rw [Finset.card_product, mul_comm]; rfl

end RecurrentSections.WordGeometry
