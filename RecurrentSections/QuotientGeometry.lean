/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordGeometry
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace RecurrentSections.WordGeometry
open scoped Pointwise

variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]

/-- The exact image generating set under a surjective homomorphism. -/
def map (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f) : WordGeometry H where
  generators := W.generators.image f
  one_mem := Finset.mem_image.mpr ⟨1, W.one_mem, map_one f⟩
  inv_mem h hh := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image.mpr ⟨g⁻¹, W.inv_mem g hg, map_inv f g⟩
  generates h := by
    obtain ⟨g, rfl⟩ := hf h
    obtain ⟨n, hn⟩ := W.generates g
    exact ⟨n, (Finset.image_pow f W.generators n) ▸ Finset.mem_image.mpr ⟨g, hn, rfl⟩⟩

theorem map_ball (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    (W.map f hf).ball n = (W.ball n).image f := (Finset.image_pow f W.generators n).symm

theorem map_length_le (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f) (g : G) :
    (W.map f hf).length (f g) ≤ W.length g := by
  apply ((W.map f hf).mem_ball_iff_length_le _ _).mp
  rw [W.map_ball]
  exact Finset.mem_image.mpr ⟨g, (W.mem_ball_iff_length_le _ _).mpr le_rfl, rfl⟩

theorem exists_lift_length_eq (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f) (h : H) :
    ∃ g : G, f g = h ∧ W.length g = (W.map f hf).length h := by
  have hh := ((W.map f hf).mem_ball_iff_length_le h ((W.map f hf).length h)).mpr le_rfl
  rw [W.map_ball] at hh
  obtain ⟨g, hg, hfg⟩ := Finset.mem_image.mp hh
  refine ⟨g, hfg, le_antisymm ((W.mem_ball_iff_length_le _ _).mp hg) ?_⟩
  simpa only [hfg] using W.map_length_le f hf g

noncomputable def shortLift (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f) (h : H) : G :=
  (W.exists_lift_length_eq f hf h).choose

@[simp] theorem shortLift_map (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f) (h : H) :
    f (W.shortLift f hf h) = h := (W.exists_lift_length_eq f hf h).choose_spec.1

theorem shortLift_mem_ball (W : WordGeometry G) (f : G →* H) (hf : Function.Surjective f)
    {n : ℕ} {h : H} (hh : h ∈ (W.map f hf).ball n) : W.shortLift f hf h ∈ W.ball n := by
  apply (W.mem_ball_iff_length_le _ _).mpr
  dsimp only [shortLift]
  rw [(W.exists_lift_length_eq f hf h).choose_spec.2]
  exact ((W.map f hf).mem_ball_iff_length_le _ _).mp hh

/-- The ambient word ball cut down to the kernel, not an intrinsic kernel ball. -/
def kernelBall (W : WordGeometry G) (f : G →* H) (n : ℕ) : Finset G :=
  (W.ball n).filter (fun g => f g = 1)

def kernelVolume (W : WordGeometry G) (f : G →* H) (n : ℕ) : ℕ := (W.kernelBall f n).card

/-- Disjoint kernel translates over short quotient representatives give a
lower bound for the ambient ball. Surjectivity is the only algebraic hypothesis. -/
theorem map_volume_mul_kernelVolume_le (W : WordGeometry G) (f : G →* H)
    (hf : Function.Surjective f) (m n : ℕ) :
    (W.map f hf).volume m * W.kernelVolume f n ≤ W.volume (m + n) := by
  classical
  let A := (W.map f hf).ball m ×ˢ W.kernelBall f n
  let F : H × G → G := fun p => W.shortLift f hf p.1 * p.2
  have hF : Set.InjOn F A := by
    intro p hp q hq he
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    have hk₁ := (Finset.mem_filter.mp hp₂).2
    have hk₂ := (Finset.mem_filter.mp hq₂).2
    have he₁ : p.1 = q.1 := by
      have hh := congrArg f he
      simpa only [F, map_mul, W.shortLift_map, hk₁, hk₂, mul_one] using hh
    apply Prod.ext he₁
    dsimp [F] at he
    rw [he₁] at he
    exact mul_left_cancel he
  have hsub : A.image F ⊆ W.ball (m + n) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    exact W.mul_mem_ball (W.shortLift_mem_ball f hf hp₁) (Finset.mem_filter.mp hp₂).1
  calc
    (W.map f hf).volume m * W.kernelVolume f n = A.card := by simp [A, volume, kernelVolume]
    _ = (A.image F).card := (Finset.card_image_of_injOn hF).symm
    _ ≤ W.volume (m + n) := Finset.card_le_card hsub

/-- Each fiber inside a ball injects into the kernel cut out by the ball
of twice the radius. This gives the complementary upper bound. -/
theorem volume_le_map_volume_mul_kernelVolume (W : WordGeometry G) (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    W.volume n ≤ (W.map f hf).volume n * W.kernelVolume f (2 * n) := by
  classical
  let A := (W.map f hf).ball n ×ˢ W.kernelBall f (2 * n)
  let F : H × G → G := fun p => p.2 * W.shortLift f hf p.1
  have hsub : W.ball n ⊆ A.image F := by
    intro g hg
    have hfg : f g ∈ (W.map f hf).ball n := by
      rw [W.map_ball]
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    let t := W.shortLift f hf (f g)
    have ht : t ∈ W.ball n := W.shortLift_mem_ball f hf hfg
    have hk : g * t⁻¹ ∈ W.kernelBall f (2 * n) := by
      apply Finset.mem_filter.mpr
      constructor
      · simpa only [two_mul] using W.mul_mem_ball hg (W.inv_mem_ball ht)
      · simp [t]
    refine Finset.mem_image.mpr ⟨(f g, g * t⁻¹), Finset.mem_product.mpr ⟨hfg, hk⟩, ?_⟩
    simp [F, t, mul_assoc]
  calc
    W.volume n ≤ (A.image F).card := Finset.card_le_card hsub
    _ ≤ A.card := Finset.card_image_le
    _ = (W.map f hf).volume n * W.kernelVolume f (2 * n) := by simp [A, volume, kernelVolume]

end RecurrentSections.WordGeometry
