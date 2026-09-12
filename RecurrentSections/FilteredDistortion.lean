/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedCollection

namespace RecurrentSections
open scoped Pointwise
open WeightedWords
variable {G : Type*} [Group G] [DecidableEq G] {c : ℕ}

/-- The last term of any finite central filtration has distortion bounded
by the length of the filtration. No torsion-freeness or minimality of the
filtration is assumed. Both word metrics are explicit. -/
theorem exists_last_level_distortion_bound (F : CentralFiltration G c) (hc : 0 < c)
    (W : WordGeometry G) (V : WordGeometry (F.level c)) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, ∀ g : F.level c,
      (g : G) ∈ W.ball n → V.length g ≤ C * (n + 1) ^ c := by
  classical
  let A := W.generators.image (fun g => (g, 1))
  have hA : F.Valid 1 A := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨le_rfl, hc, by rw [F.first]; exact Subgroup.mem_top _⟩
  obtain ⟨B, hB, hBC⟩ := exists_weighted_collection F 1 (c - 1) (by omega) (by omega) A hA
  have hec : 1 + (c - 1) = c := by omega
  rw [hec] at hB hBC
  obtain ⟨D, hD⟩ := hBC 1
  obtain ⟨M, hM⟩ := exists_last_level_length_bound F B hB V
  refine ⟨M * D + 1, by omega, fun n g hg => ?_⟩
  obtain ⟨v, hv⟩ := Finset.mem_pow.mp hg
  let l : List (G × ℕ) := List.ofFn (fun k => ((v k : G), 1))
  have hl : ∀ a ∈ l, a ∈ A := by
    intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact Finset.mem_image.mpr ⟨v k, (v k).property, rfl⟩
  have hvalue : value l = (g : G) := by
    simpa only [value, l, List.map_ofFn, Function.comp_def] using hv
  have hcost : cost c (n + 1) l ≤ 1 * (n + 1) ^ c := by
    have he : cost c (n + 1) l = n * (n + 1) ^ (c - 1) := by
      simp [cost, l, List.map_ofFn, Function.comp_def]
    rw [he, one_mul]
    calc
      n * (n + 1) ^ (c - 1) ≤ (n + 1) * (n + 1) ^ (c - 1) := Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = (n + 1) ^ c := by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hc]
  have hrep := hD (n + 1) (by omega) l hl hcost (by rw [hvalue]; exact g.property)
  rw [hvalue] at hrep
  have hb := hM (n + 1) (D * (n + 1) ^ c) g hrep
  calc
    V.length g ≤ M * (D * (n + 1) ^ c) := hb
    _ ≤ (M * D + 1) * (n + 1) ^ c := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- Sharp polynomial upper distortion for the last possibly nontrivial
lower-central term. Combined with `NilpotentPowers`, this gives the two
complementary inclusions needed for matching volume bounds. -/
theorem exists_last_lowerCentralSeries_distortion_bound (c : ℕ)
    (W : WordGeometry G) (hc : (⊤ : Subgroup G).lowerCentralSeries (c + 1) = ⊥)
    (V : WordGeometry ((⊤ : Subgroup G).lowerCentralSeries c)) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, ∀ g : (⊤ : Subgroup G).lowerCentralSeries c,
      (g : G) ∈ W.ball n → V.length g ≤ C * (n + 1) ^ (c + 1) := by
  let F := CentralFiltration.ofLowerCentralSeries (G := G) (c + 1) hc
  exact exists_last_level_distortion_bound F (by omega) W V

end RecurrentSections
