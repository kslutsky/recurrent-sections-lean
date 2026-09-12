/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordSwaps
import RecurrentSections.WordGeometry
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators

namespace RecurrentSections
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [DecidableEq G]

theorem WordGeometry.prod_mem_ball (W : WordGeometry G) (l : List G)
    (hl : ∀ a ∈ l, a ∈ W.generators) : l.prod ∈ W.ball l.length := by
  induction l with
  | nil => exact W.one_mem_ball 0
  | cons a l ih =>
    have ha : a ∈ W.ball 1 := by simpa [WordGeometry.ball] using hl a (by simp)
    simpa [Nat.add_comm] using W.mul_mem_ball ha (ih (fun b hb => hl b (by simp [hb])))

/-- Control of each conjugated elementary swap controls the discrepancy
between products of permuted words. -/
theorem factor_of_word_swaps (W : WordGeometry G) (N : Subgroup G) (V : WordGeometry N)
    (n D : ℕ)
    (hD : ∀ a ∈ W.generators, ∀ b ∈ W.generators, ∀ g ∈ W.ball n,
      ∃ h ∈ V.ball D, (h : G) = g * ⁅a, b⁆ * g⁻¹)
    {k : ℕ} {l r : List G} (hs : WordSwaps.Steps k l r)
    (hlen : l.length ≤ n) (hl : ∀ a ∈ l, a ∈ W.generators) :
    ∃ h ∈ V.ball (k * D), l.prod = (h : G) * r.prod := by
  induction hs with
  | refl l => exact ⟨1, V.one_mem_ball (0 * D), by simp⟩
  | swap p q a b =>
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have hplen : p.length ≤ n := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    have hp : p.prod ∈ W.ball n := W.ball_mono hplen
      (W.prod_mem_ball p (fun x hx => hl x (by simp [hx])))
    obtain ⟨h, hh, he⟩ := hD a ha b hb p.prod hp
    refine ⟨h, by simpa using hh, ?_⟩
    rw [he]
    simp only [List.prod_append, List.prod_cons, commutatorElement_def]
    group
  | @trans m k l t r h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a, ha, hea⟩ := ih₁ hlen hl
    obtain ⟨b, hb, heb⟩ := ih₂ (by simpa only [← h₁.perm.length_eq] using hlen)
      (fun x hx => hl x (h₁.perm.mem_iff.mpr hx))
    refine ⟨a * b, ?_, ?_⟩
    · simpa only [Nat.add_mul] using V.mul_mem_ball ha hb
    · rw [hea, heb, Subgroup.coe_mul, mul_assoc]

theorem factor_of_word_perm (W : WordGeometry G) (N : Subgroup G) (V : WordGeometry N)
    (n D : ℕ)
    (hD : ∀ a ∈ W.generators, ∀ b ∈ W.generators, ∀ g ∈ W.ball n,
      ∃ h ∈ V.ball D, (h : G) = g * ⁅a, b⁆ * g⁻¹)
    {l r : List G} (hperm : l.Perm r) (hlen : l.length ≤ n)
    (hl : ∀ a ∈ l, a ∈ W.generators) :
    ∃ h ∈ V.ball (n ^ 2 * D), l.prod = (h : G) * r.prod := by
  obtain ⟨k, hk, hs⟩ := WordSwaps.exists_steps_of_perm hperm
  obtain ⟨h, hh, he⟩ := factor_of_word_swaps W N V n D hD hs hlen hl
  exact ⟨h, V.ball_mono (Nat.mul_le_mul_right D (hk.trans (Nat.pow_le_pow_left hlen 2))) hh, he⟩

theorem card_sym_le {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) :
    Fintype.card (Sym α n) ≤ (n + 1) ^ Fintype.card α := by
  let f : Sym α n → (α → Fin (n + 1)) := fun m a =>
    ⟨m.val.count a, by have h := Multiset.count_le_card a m.val; rw [m.property] at h; omega⟩
  have hf : Function.Injective f := by
    intro m t h
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro a
    exact congrArg Fin.val (congrFun h a)
  simpa using Fintype.card_le_of_injective f hf

/-- A ball is covered by short normal-subgroup errors times one representative
for each multiset of letters. This estimate does not assume nilpotence. -/
theorem volume_le_of_swap_bound (W : WordGeometry G) (N : Subgroup G) (V : WordGeometry N)
    (n D : ℕ)
    (hD : ∀ a ∈ W.generators, ∀ b ∈ W.generators, ∀ g ∈ W.ball n,
      ∃ h ∈ V.ball D, (h : G) = g * ⁅a, b⁆ * g⁻¹) :
    W.volume n ≤ V.volume (n ^ 2 * D) * (n + 1) ^ W.generators.card := by
  classical
  let rep : Sym W.generators n → G := fun m => (m.val.toList.map Subtype.val).prod
  let f : N × Sym W.generators n → G := fun p => (p.1 : G) * rep p.2
  have hcover : W.ball n ⊆ (V.ball (n ^ 2 * D) ×ˢ (Finset.univ : Finset (Sym W.generators n))).image f := by
    intro g hg
    obtain ⟨v, hv⟩ := Finset.mem_pow.mp hg
    let l : List W.generators := List.ofFn v
    let m : Sym W.generators n := ⟨(l : Multiset W.generators), by simp [l]⟩
    have hlperm : l.Perm m.val.toList := Quotient.exact (Multiset.coe_toList m.val).symm
    have hl : ∀ a ∈ l.map Subtype.val, a ∈ W.generators := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact b.property
    have hlen : (l.map Subtype.val).length ≤ n := by simp [l]
    obtain ⟨h, hh, he⟩ := factor_of_word_perm W N V n D hD (hlperm.map Subtype.val) hlen hl
    refine Finset.mem_image.mpr ⟨(h, m), Finset.mem_product.mpr ⟨hh, Finset.mem_univ _⟩, ?_⟩
    have hlprod : (l.map Subtype.val).prod = g := by simpa [l, Function.comp_def] using hv
    exact he.symm.trans hlprod
  calc
    W.volume n ≤ ((V.ball (n ^ 2 * D) ×ˢ (Finset.univ : Finset (Sym W.generators n))).image f).card :=
      Finset.card_le_card hcover
    _ ≤ (V.ball (n ^ 2 * D) ×ˢ (Finset.univ : Finset (Sym W.generators n))).card := Finset.card_image_le
    _ = V.volume (n ^ 2 * D) * Fintype.card (Sym W.generators n) := by simp [WordGeometry.volume]
    _ ≤ V.volume (n ^ 2 * D) * (n + 1) ^ W.generators.card := by
      exact Nat.mul_le_mul_left _ (by simpa using card_sym_le (α := W.generators) n)

end RecurrentSections
