/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.ReturnConfigurations

namespace RecurrentSections

open Set MeasureTheory

variable {G X K : Type} [Group G] [DecidableEq G] [MulAction G X]

def recentered (H : ℕ → X → G) (A : ℕ → Set X) (n : ℕ) : Set X :=
  {x | H n x • x ∈ A n}

omit [DecidableEq G] in
theorem uncenter_injective (H : X → G) (hinv : ∀ (g : G) (x : X), H (g • x) = H x) :
    Function.Injective (fun x => H x • x) := by
  have hl : Function.LeftInverse (fun x => (H x)⁻¹ • x) (fun x => H x • x) := by
    intro x
    dsimp
    rw [hinv, inv_smul_smul]
  exact hl.injective

theorem recentered_multiplicity (W : WordGeometry G) (R M : ℕ) (hR : 0 < R)
    (hpack : GroupPacking W M) (H : X → G) (hinv : ∀ (g : G) (x : X), H (g • x) = H x)
    (hH : ∀ x, H x ∈ W.ball (3 * R)) (A : Set X) (hA : Separated W R A) :
    LocalMultiplicity W R M {x | H x • x ∈ A} := by
  classical
  intro y hy I _ f hf hmem hclose
  choose g hg hgf using hclose
  let k (i : I) : G := H (f i) * g i * (H y)⁻¹
  have hpos (i : I) : k i • (H y • y) = H (f i) • f i := by
    simp only [k, mul_smul, inv_smul_smul, hgf]
  apply hpack R hR I k
  · intro i
    have h₁ := (W.mem_ball_iff_length_le _ _).mp (hH (f i))
    have h₂ := (W.mem_ball_iff_length_le _ _).mp (hg i)
    have h₃ := (W.mem_ball_iff_length_le _ _).mp (hH y)
    have h₄ := W.length_mul_le (H (f i)) (g i)
    have h₅ := W.length_mul_le (H (f i) * g i) (H y)⁻¹
    rw [W.length_inv] at h₅
    dsimp [k]
    omega
  · intro i j hij
    by_contra! hlen
    have heq : H (f i) • f i = H (f j) • f j :=
      hA _ (hmem i) _ (hmem j) (k j * (k i)⁻¹)
        ((W.mem_ball_iff_length_le _ _).mpr hlen) (by
          rw [← hpos i, mul_smul, inv_smul_smul, hpos j])
    exact hij (hf (uncenter_injective H hinv heq))

variable [MeasurableSpace X] [MeasurableConstSMul G X]

theorem measurableSet_variable_translate (W : WordGeometry G) (H : X → G)
    (hH : ∀ g, MeasurableSet {x | H x = g}) (A : Set X) (hA : MeasurableSet A) :
    MeasurableSet {x | H x • x ∈ A} := by
  let := W.countable
  have heq : {x | H x • x ∈ A} =
      ⋃ g : G, {x | H x = g} ∩ (fun x => g • x) ⁻¹' A := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h; exact ⟨H x, rfl, h⟩
    · rintro ⟨g, h, hx⟩; simpa [h] using hx
  rw [heq]
  exact MeasurableSet.iUnion fun g => (hH g).inter (hA.preimage (measurable_const_smul g))

variable [MetricSpace K] [CompactSpace K]

omit [MeasurableSpace X] [MeasurableConstSMul G X] [CompactSpace K] in
/-- Nearest-point recentering turns membership in the selected cluster
into everywhere recurrence. Its displacements need not preserve distance. -/
theorem recentered_recurrent (W : WordGeometry G) (r : ℕ → ℕ)
    (hr : ∀ n, 0 < r n) (φ : ℕ → G → K) (hφ : ScaledModels W r φ)
    (A : ℕ → Set X) (f : X → K × K)
    (hf : ∀ x, f x ∈ returnCluster W r φ A x)
    (H : ℕ → X → G) (hinv : ∀ n (g : G) (x : X), H n (g • x) = H n x)
    (hH : ∀ n x, H n x ∈ W.ball (3 * r n))
    (hmin : ∀ n x g, g ∈ W.ball (3 * r n) →
      dist (φ n (H n x)) (f x).2 ≤ dist (φ n g) (f x).2) :
    Recurrent W r (recentered H A) := by
  intro ε hε x N
  obtain ⟨n, hn, p, hp, hd⟩ :=
    (mem_tailCluster_iff _ _).mp (hf x).1 (ε / 3) (by positivity) N
  obtain ⟨g, hg, hga, rfl⟩ := hp
  have hsnd : dist (φ n g) (f x).2 < ε / 3 := (max_lt_iff.mp hd).2
  have hmn := hmin n x g hg
  have htri := dist_triangle (φ n (H n x)) (f x).2 (φ n g)
  rw [dist_comm (f x).2 (φ n g)] at htri
  have hdist : dist (φ n (H n x)) (φ n g) < ε := by linarith
  have hrpos : (0 : ℝ) < r n := by exact_mod_cast hr n
  have hlen := mul_lt_mul_of_pos_right hdist hrpos
  rw [hφ n (H n x) g (hH n x) hg] at hlen
  let k : G := (H n x)⁻¹ * g
  refine ⟨n, hn, k⁻¹, k • x, ?_, inv_smul_smul k x, ?_⟩
  · change H n (k • x) • (k • x) ∈ A n
    rw [hinv]
    simpa only [k, mul_smul, smul_inv_smul] using hga
  · simpa only [W.length_inv, k] using hlen

end RecurrentSections
