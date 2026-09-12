/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedWords

namespace RecurrentSections.WeightedWords
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [DecidableEq G]

/-- A weighted form of the elementary adjacent-swap estimate. It needs no
nilpotence hypothesis; all geometric information is in the swap bound. -/
theorem factor_of_swaps (B : Finset (G × ℕ)) (S : Finset G) (c R n D : ℕ)
    (hD : ∀ a ∈ S, ∀ b ∈ S, ∀ m ≤ n, ∀ g ∈ S ^ m,
      Rep B c R D (g * ⁅a, b⁆ * g⁻¹))
    {k : ℕ} {l r : List G} (hs : WordSwaps.Steps k l r)
    (hlen : l.length ≤ n) (hl : ∀ a ∈ l, a ∈ S) :
    ∃ h, Rep B c R (k * D) h ∧ l.prod = h * r.prod := by
  induction hs with
  | refl l => exact ⟨1, Rep.one B c R _, by simp⟩
  | swap p q a b =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have hplen : p.length ≤ n := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    have hp := prod_mem_finset_pow S p (fun x hx => hl x (by simp [hx]))
    refine ⟨p.prod * ⁅a, b⁆ * p.prod⁻¹, by simpa using hD a ha b hb _ hplen _ hp, ?_⟩
    simp only [List.prod_append, List.prod_cons]
    group
  | @trans m k l t r h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a, ha, hea⟩ := ih₁ hlen hl
    obtain ⟨b, hb, heb⟩ := ih₂ (by simpa only [← h₁.perm.length_eq] using hlen)
      (fun x hx => hl x (h₁.perm.mem_iff.mpr hx))
    refine ⟨a * b, ?_, ?_⟩
    · simpa only [Nat.add_mul] using ha.mul hb
    · rw [hea, heb, mul_assoc]

theorem factor_of_perm (B : Finset (G × ℕ)) (S : Finset G) (c R n D : ℕ)
    (hD : ∀ a ∈ S, ∀ b ∈ S, ∀ m ≤ n, ∀ g ∈ S ^ m,
      Rep B c R D (g * ⁅a, b⁆ * g⁻¹))
    {l r : List G} (hperm : l.Perm r) (hlen : l.length ≤ n) (hl : ∀ a ∈ l, a ∈ S) :
    ∃ h, Rep B c R (n ^ 2 * D) h ∧ l.prod = h * r.prod := by
  obtain ⟨k, hk, hs⟩ := WordSwaps.exists_steps_of_perm hperm
  obtain ⟨h, hh, he⟩ := factor_of_swaps B S c R n D hD hs hlen hl
  exact ⟨h, hh.mono (Nat.mul_le_mul_right D (hk.trans (Nat.pow_le_pow_left hlen 2))), he⟩

/-- Move all letters of one weight to the left. A bound on conjugates of
the other letters bounds the cost of the resulting right-hand factor. -/
theorem factor_lowWord (B D : Finset (G × ℕ)) (S : Finset G) (c R i M K : ℕ)
    (hS : ∀ a ∈ B, a.2 = i → a.1 ∈ S)
    (hD : ∀ a ∈ B, a.2 ≠ i → ∀ m ≤ M, ∀ g ∈ S ^ m,
      Rep D c R (K * R ^ (c - a.2)) (g⁻¹ * a.1 * g))
    (l : List (G × ℕ)) (hl : ∀ a ∈ l, a ∈ B) (hm : (lowWord i l).length ≤ M) :
    ∃ h, Rep D c R (K * cost c R l) h ∧ value l = (lowWord i l).prod * h := by
  induction l with
  | nil => exact ⟨1, Rep.one D c R _, by simp⟩
  | cons a l ih =>
    have ha : a ∈ B := hl a (by simp)
    have hl' : ∀ b ∈ l, b ∈ B := fun b hb => hl b (by simp [hb])
    have hm' : (lowWord i l).length ≤ M := by
      rw [lowWord_cons] at hm
      split_ifs at hm with hai
      · simp only [List.length_cons] at hm
        omega
      · exact hm
    obtain ⟨h, hh, he⟩ := ih hl' hm'
    by_cases hai : a.2 = i
    · refine ⟨h, hh.mono (Nat.mul_le_mul_left K (Nat.le_add_left _ _)), ?_⟩
      simp [hai, he, mul_assoc]
    · have hp := lowWord_mem_pow S i l (fun b hb => hS b (hl' b hb))
      have haD := hD a ha hai _ hm' _ hp
      refine ⟨((lowWord i l).prod⁻¹ * a.1 * (lowWord i l).prod) * h, ?_, ?_⟩
      · simpa only [cost_cons, Nat.mul_add] using haD.mul hh
      · simp only [value_cons, lowWord_cons, if_neg hai]
        rw [he]
        group

end RecurrentSections.WeightedWords
