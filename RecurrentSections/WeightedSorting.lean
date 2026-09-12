/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedUniform
import RecurrentSections.WeightedPermutation

namespace RecurrentSections
open scoped Pointwise commutatorElement
open WeightedWords
variable {G : Type*} [Group G] [DecidableEq G] {c : ℕ}

/-- Reordering `O(R^i)` letters of weight `i` costs `O(R^c)` in a fixed
alphabet of higher-weight commutators. -/
theorem exists_weighted_permutation_bound (F : CentralFiltration G c)
    (i : ℕ) (hi : 0 < i) (S : Finset G) (hS : ∀ s ∈ S, s ∈ F.level i) :
    ∃ B : Finset (G × ℕ), F.Valid (i + 1) B ∧
      ∀ C : ℕ, ∃ D : ℕ, ∀ R : ℕ, 0 < R → ∀ l t : List G,
        l.Perm t → l.length ≤ C * R ^ i → (∀ a ∈ l, a ∈ S) →
        ∃ h, Rep B c R (D * R ^ c) h ∧ l.prod = h * t.prod := by
  classical
  by_cases hic : c < i + i
  · refine ⟨∅, by simp [CentralFiltration.Valid], fun C => ⟨0, ?_⟩⟩
    intro R hR l t hp hlen hl
    have hswap : ∀ a ∈ S, ∀ b ∈ S, ∀ m ≤ l.length, ∀ g ∈ S ^ m,
        Rep (∅ : Finset (G × ℕ)) c R 0 (g * ⁅a, b⁆ * g⁻¹) := by
      intro a ha b hb m hm g hg
      have he : ⁅a, b⁆ = 1 := F.eq_one_of_mem hic
        (F.commutator_le i i hi hi (Subgroup.commutator_mem_commutator (hS a ha) (hS b hb)))
      simpa [he] using (Rep.one (∅ : Finset (G × ℕ)) c R 0)
    obtain ⟨h, hh, he⟩ := factor_of_perm ∅ S c R l.length 0 hswap hp le_rfl hl
    exact ⟨h, by simpa using hh, he⟩
  have hicle : i + i ≤ c := by omega
  let E : Finset G := (S ×ˢ S).image (fun p => ⁅p.1, p.2⁆)
  have hE : ∀ a ∈ E, a ∈ F.level (i + i) := by
    intro a ha
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.mp ha
    exact F.commutator_le i i hi hi (Subgroup.commutator_mem_commutator
      (hS s (Finset.mem_product.mp hst).1) (hS t (Finset.mem_product.mp hst).2))
  obtain ⟨B, hB, h⟩ := exists_weighted_conjugation_bound F i (i + i) hi (by omega) S E hS hE
  refine ⟨B, hB.weaken (by omega), fun C => ?_⟩
  obtain ⟨D, hD⟩ := h C
  refine ⟨C ^ 2 * D, fun R hR l t hp hlen hl => ?_⟩
  have hswap : ∀ a ∈ S, ∀ b ∈ S, ∀ m ≤ l.length, ∀ g ∈ S ^ m,
      Rep B c R (D * R ^ (c - (i + i))) (g * ⁅a, b⁆ * g⁻¹) := by
    intro a ha b hb m hm g hg
    exact hD R hR m g hg (hm.trans hlen) ⁅a, b⁆
      (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
  obtain ⟨h, hh, he⟩ := factor_of_perm B S c R l.length (D * R ^ (c - (i + i)))
    hswap hp le_rfl hl
  refine ⟨h, hh.mono ?_, he⟩
  calc
    l.length ^ 2 * (D * R ^ (c - (i + i)))
        ≤ (C * R ^ i) ^ 2 * (D * R ^ (c - (i + i))) := by gcongr
    _ = (C ^ 2 * D) * R ^ c := by
      have hpow : R ^ (i + i) * R ^ (c - (i + i)) = R ^ c := by
        rw [← pow_add, Nat.add_sub_of_le hicle]
      calc
        _ = (C ^ 2 * D) * (R ^ (i + i) * R ^ (c - (i + i))) := by rw [pow_add]; ring
        _ = _ := by rw [hpow]

end RecurrentSections
