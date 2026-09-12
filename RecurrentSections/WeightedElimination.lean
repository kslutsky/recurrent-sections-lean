/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedSorting
import RecurrentSections.FiltrationRelations

/-! # Weighted collection in a central filtration

The collection method follows the classical argument in Druţu--Kapovich,
*Geometric Group Theory*, 2017 author draft, Lemma 14.21, pp. 506--508:
https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
Here finite positive relation blocks, obtained from Dickson's lemma in
`PositiveRelations`, replace cyclic-basis and finite-order carry bookkeeping.
All commutator errors are counted with their weights; in particular, the
second-weight count includes every crossed first-weight letter.
-/

namespace RecurrentSections
open scoped Pointwise commutatorElement
open WeightedWords
variable {G : Type*} [Group G] [DecidableEq G] {c : ℕ}

theorem WeightedWords.inv_mem_finset_pow_inv (S : Finset G) (n : ℕ) {g : G}
    (hg : g ∈ S ^ n) : g⁻¹ ∈ (S⁻¹) ^ n := by
  induction n generalizing g with
  | zero =>
    have hg1 : g = 1 := by simpa using hg
    simp [hg1]
  | succ n ih =>
    rw [pow_succ] at hg
    obtain ⟨u, hu, s, hs, rfl⟩ := Finset.mem_mul.mp hg
    rw [mul_inv_rev, pow_succ']
    exact Finset.mul_mem_mul (Finset.inv_mem_inv hs) (ih hu)

omit [DecidableEq G] in
theorem WeightedWords.value_mem_level (F : CentralFiltration G c) {i : ℕ}
    {B : Finset (G × ℕ)} (hB : F.Valid i B) (l : List (G × ℕ))
    (hl : ∀ a ∈ l, a ∈ B) : value l ∈ F.level i := by
  induction l with
  | nil => exact (F.level i).one_mem
  | cons a l ih =>
    exact (F.level i).mul_mem (F.antitone (hB a (hl a (by simp))).1
      (hB a (hl a (by simp))).2.2) (ih (fun b hb => hl b (by simp [hb])))

omit [DecidableEq G] in
theorem WeightedWords.Rep.mem_level {F : CentralFiltration G c} {i R M : ℕ}
    {B : Finset (G × ℕ)} {g : G} (h : Rep B c R M g) (hB : F.Valid i B) :
    g ∈ F.level i := by
  obtain ⟨l, hl, rfl, hc⟩ := h
  exact value_mem_level F hB l hl

/-- Remove the least weight from a weighted word representing an element
of the next central-filtration level. The output alphabet is independent of
the radius and cost constant, and the polynomial cost degree is preserved. -/
theorem exists_weighted_elimination (F : CentralFiltration G c)
    (i : ℕ) (hi : 0 < i) (hic : i < c)
    (A : Finset (G × ℕ)) (hA : F.Valid i A) :
    ∃ B : Finset (G × ℕ), F.Valid (i + 1) B ∧
      ∀ C : ℕ, ∃ D : ℕ, ∀ R : ℕ, 0 < R → ∀ l : List (G × ℕ),
        (∀ a ∈ l, a ∈ A) → cost c R l ≤ C * R ^ c →
        value l ∈ F.level (i + 1) → Rep B c R (D * R ^ c) (value l) := by
  classical
  let S := (A.filter (fun a => a.2 = i)).image Prod.fst
  have hS : ∀ s ∈ S, s ∈ F.level i := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    have ha' := Finset.mem_filter.mp ha
    simpa only [ha'.2] using (hA a ha'.1).2.2
  have hAS : ∀ a ∈ A, a.2 = i → a.1 ∈ S :=
    fun a ha he => Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, he⟩, rfl⟩
  let H := A.filter (fun a => a.2 ≠ i)
  have hH : F.Valid (i + 1) H := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact ⟨by have := (hA a ha'.1).1; omega, (hA a ha'.1).2⟩
  have hSI : ∀ s ∈ S⁻¹, s ∈ F.level i := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_inv.mp hs
    exact (F.level i).inv_mem (hS t ht)
  obtain ⟨BH, hBH, hHC⟩ := exists_uniform_weighted_conjugation_bound F i (i + 1) hi
    (by omega) S⁻¹ hSI H hH
  obtain ⟨BP, hBP, hPC⟩ := exists_weighted_permutation_bound F i hi S hS
  obtain ⟨T, hT, hTC⟩ := F.exists_relation_blocks i hi S hS
  let BT : Finset (G × ℕ) := T.image (fun l => (l.prod, i + 1))
  have hBT : F.Valid (i + 1) BT := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨le_rfl, by omega, (hT l hl).2.2⟩
  let B := BP ∪ (BT ∪ BH)
  have hPB : BP ⊆ B := Finset.subset_union_left
  have hTB : BT ⊆ B := Finset.subset_union_left.trans Finset.subset_union_right
  have hHB : BH ⊆ B := Finset.subset_union_right.trans Finset.subset_union_right
  refine ⟨B, hBP.union (hBT.union hBH), fun C => ?_⟩
  obtain ⟨K, hK⟩ := hHC C
  obtain ⟨D, hD⟩ := hPC C
  refine ⟨D + C + K * C, fun R hR l hl hcost hmem => ?_⟩
  have hm : (lowWord i l).length ≤ C * R ^ i := lowWord_length_le hR (by omega) l hcost
  have hheavy : ∀ a ∈ A, a.2 ≠ i → ∀ m ≤ C * R ^ i, ∀ g ∈ S ^ m,
      Rep BH c R (K * R ^ (c - a.2)) (g⁻¹ * a.1 * g) := by
    intro a ha hai m hm g hg
    have hgi : g⁻¹ ∈ (S⁻¹) ^ m := inv_mem_finset_pow_inv S m hg
    have hh := hK R hR m g⁻¹ hgi hm a (Finset.mem_filter.mpr ⟨ha, hai⟩)
    simpa only [inv_inv] using hh
  obtain ⟨h, hh, he⟩ := factor_lowWord A BH S c R i (C * R ^ i) K hAS hheavy l hl hm
  have huS : ∀ a ∈ lowWord i l, a ∈ S := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hb' := List.mem_filter.mp hb
    exact hAS b (hl b hb'.1) (by simpa using hb'.2)
  have huN : (lowWord i l).prod ∈ F.level (i + 1) := by
    have hhN := hh.mem_level hBH
    have hz := (F.level (i + 1)).mul_mem hmem ((F.level (i + 1)).inv_mem hhN)
    simpa only [he, mul_inv_cancel_right] using hz
  obtain ⟨L, hL, hperm, hlen⟩ := hTC (lowWord i l) huS huN
  obtain ⟨p, hp, hpe⟩ := hD R hR (lowWord i l) L.flatten hperm hm huS
  have hr : Rep BT c R (C * R ^ c) L.flatten.prod := by
    refine ⟨L.map (fun t => (t.prod, i + 1)), ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_image.mpr ⟨t, hL t ht, rfl⟩
    · simp only [value, List.map_map, Function.comp_def, List.prod_flatten]
    · have hlen' : L.length ≤ C * R ^ (i + 1) := by
        calc
          L.length ≤ C * R ^ i := hlen.trans hm
          _ ≤ C * R ^ (i + 1) := by gcongr; omega
      have hpow : R ^ (i + 1) * R ^ (c - (i + 1)) = R ^ c := by
        rw [← pow_add, Nat.add_sub_of_le (by omega : i + 1 ≤ c)]
      calc
        cost c R (L.map (fun t => (t.prod, i + 1))) = L.length * R ^ (c - (i + 1)) := by
          simp [cost, List.map_map, Function.comp_def]
        _ ≤ (C * R ^ (i + 1)) * R ^ (c - (i + 1)) := Nat.mul_le_mul_right _ hlen'
        _ = C * R ^ c := by rw [mul_assoc, hpow]
  have hh' : Rep BH c R ((K * C) * R ^ c) h := hh.mono (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K hcost)
  have hz := ((hp.alphabet_mono hPB).mul (hr.alphabet_mono hTB)).mul (hh'.alphabet_mono hHB)
  rw [he, hpe]
  convert hz using 1
  ring

end RecurrentSections
