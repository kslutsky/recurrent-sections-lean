/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.PositiveRelations
import RecurrentSections.WeightedWords

namespace RecurrentSections
open scoped Pointwise commutatorElement
variable {G H : Type*} [Group G] [Group H] [DecidableEq G]

omit [Group G] in
/-- Finite-alphabet form of positive relation decomposition. -/
theorem exists_finite_relation_words_on_finset (S : Finset G) (f : G → H)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, Commute (f a) (f b)) :
    ∃ R : Finset (List G),
      (∀ l ∈ R, (∀ a ∈ l, a ∈ S) ∧ l ≠ [] ∧ (l.map f).prod = 1) ∧
      ∀ l : List G, (∀ a ∈ l, a ∈ S) → (l.map f).prod = 1 →
        ∃ L : List (List G), (∀ a ∈ L, a ∈ R) ∧ l.Perm L.flatten ∧ L.length ≤ l.length := by
  classical
  let fS : S → H := fun a => f a.val
  obtain ⟨R, hR, h⟩ := exists_finite_relation_words_of_commute fS
    (fun a b => hcomm a a.property b b.property)
  refine ⟨R.image (List.map Subtype.val), ?_, ?_⟩
  · intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact b.property
    · exact fun he => (hR u hu).1 (List.map_eq_nil_iff.mp he)
    · simpa only [List.map_map, Function.comp_def, fS] using (hR u hu).2
  · intro l hl hf
    let u : List S := l.attach.map (fun a => ⟨a.val, hl a.val a.property⟩)
    have hu : u.map Subtype.val = l := by simp [u, List.map_map, Function.comp_def]
    have huf : (u.map fS).prod = 1 := by
      have he : u.map fS = l.map f := by
        calc
          u.map fS = (u.map Subtype.val).map f := List.map_map.symm
          _ = l.map f := congrArg (List.map f) hu
      rwa [he]
    obtain ⟨L, hL, hp, hlen⟩ := h u huf
    refine ⟨L.map (List.map Subtype.val), ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_image.mpr ⟨b, hL b hb, rfl⟩
    · simpa only [hu, List.map_flatten] using hp.map Subtype.val
    · simpa only [List.length_map, ← hu] using hlen

namespace CentralFiltration
variable {c : ℕ} (F : CentralFiltration G c)

omit [DecidableEq G] in
/-- Normality follows from the central-filtration axioms. -/
theorem normal (i : ℕ) : (F.level i).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
  by_cases hi : i = 0
  · subst i
    have he : F.level 0 = ⊤ := top_unique (by
      rw [← F.first]
      exact F.antitone (by omega))
    rw [he]
    exact le_top
  · rw [← F.first]
    exact (F.commutator_le i 1 (by omega) (by omega)).trans (F.antitone (by omega))

/-- The usual lower central series, with the first term assigned weight one. -/
def ofLowerCentralSeries (c : ℕ) (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) :
    CentralFiltration G c where
  level i := (⊤ : Subgroup G).lowerCentralSeries (i - 1)
  antitone := fun i j hij => (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  first := by simp
  commutator_le := by
    intro i j hi hj
    convert commutator_top_lowerCentralSeries_le (G := G) (i - 1) (j - 1) using 1
    congr 1
    omega
  vanishes := by simpa using hc

/-- In each successive quotient, the images of a finite alphabet of the
preceding level admit a fixed finite set of positive relation blocks. -/
theorem exists_relation_blocks (i : ℕ) (hi : 0 < i) (S : Finset G)
    (hS : ∀ a ∈ S, a ∈ F.level i) :
    ∃ R : Finset (List G),
      (∀ l ∈ R, (∀ a ∈ l, a ∈ S) ∧ l ≠ [] ∧ l.prod ∈ F.level (i + 1)) ∧
      ∀ l : List G, (∀ a ∈ l, a ∈ S) → l.prod ∈ F.level (i + 1) →
        ∃ L : List (List G), (∀ a ∈ L, a ∈ R) ∧ l.Perm L.flatten ∧ L.length ≤ l.length := by
  classical
  let N := F.level (i + 1)
  let : N.Normal := F.normal (i + 1)
  let q := QuotientGroup.mk' N
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, Commute (q a) (q b) := by
    intro a ha b hb
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact F.antitone (by omega : i + 1 ≤ i + i)
      (F.commutator_le i i hi hi (Subgroup.commutator_mem_commutator (hS a ha) (hS b hb)))
  obtain ⟨R, hR, h⟩ := exists_finite_relation_words_on_finset S q hcomm
  have he (l : List G) : (l.map q).prod = 1 ↔ l.prod ∈ N := by
    rw [← map_list_prod]
    exact QuotientGroup.eq_one_iff _
  exact ⟨R, fun l hl => ⟨(hR l hl).1, (hR l hl).2.1, (he l).mp (hR l hl).2.2⟩,
    fun l hl hm => h l hl ((he l).mpr hm)⟩

end CentralFiltration
end RecurrentSections
