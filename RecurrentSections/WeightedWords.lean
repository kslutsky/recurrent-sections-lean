/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.LowerCentralCommutators
import RecurrentSections.WordSwaps

namespace RecurrentSections
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- A descending central filtration, indexed by positive weights. -/
structure CentralFiltration (G : Type*) [Group G] (c : ℕ) where
  level : ℕ → Subgroup G
  antitone : Antitone level
  first : level 1 = ⊤
  commutator_le : ∀ i j, 0 < i → 0 < j → ⁅level i, level j⁆ ≤ level (i + j)
  vanishes : level (c + 1) = ⊥

namespace CentralFiltration
variable {c : ℕ} (F : CentralFiltration G c)

theorem eq_one_of_mem {j : ℕ} (hj : c < j) {g : G} (hg : g ∈ F.level j) : g = 1 := by
  have := F.antitone (show c + 1 ≤ j by omega) hg
  simpa [F.vanishes] using this

def Valid (i : ℕ) (B : Finset (G × ℕ)) : Prop :=
  ∀ a ∈ B, i ≤ a.2 ∧ a.2 ≤ c ∧ a.1 ∈ F.level a.2

variable {F}

theorem Valid.mono {i : ℕ} {B D : Finset (G × ℕ)} (h : F.Valid i D) (hBD : B ⊆ D) :
    F.Valid i B := fun a ha => h a (hBD ha)

theorem Valid.union [DecidableEq G] {i : ℕ} {B D : Finset (G × ℕ)}
    (hB : F.Valid i B) (hD : F.Valid i D) : F.Valid i (B ∪ D) := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · exact hB a ha
  · exact hD a ha

theorem Valid.weaken {i j : ℕ} {B : Finset (G × ℕ)} (h : F.Valid j B) (hij : i ≤ j) :
    F.Valid i B := fun a ha => ⟨hij.trans (h a ha).1, (h a ha).2⟩

end CentralFiltration

namespace WeightedWords

def value (l : List (G × ℕ)) : G := (l.map Prod.fst).prod

def cost (c R : ℕ) (l : List (G × ℕ)) : ℕ := (l.map (fun a => R ^ (c - a.2))).sum

@[simp] theorem value_nil : value ([] : List (G × ℕ)) = 1 := rfl
@[simp] theorem value_cons (a : G × ℕ) (l : List (G × ℕ)) :
    value (a :: l) = a.1 * value l := rfl
@[simp] theorem value_append (l t : List (G × ℕ)) : value (l ++ t) = value l * value t := by
  simp [value]
omit [Group G] in
@[simp] theorem cost_nil (c R : ℕ) : cost c R ([] : List (G × ℕ)) = 0 := rfl
omit [Group G] in
@[simp] theorem cost_cons (c R : ℕ) (a : G × ℕ) (l : List (G × ℕ)) :
    cost c R (a :: l) = R ^ (c - a.2) + cost c R l := rfl
omit [Group G] in
@[simp] theorem cost_append (c R : ℕ) (l t : List (G × ℕ)) :
    cost c R (l ++ t) = cost c R l + cost c R t := by simp [cost]

/-- A weighted word with a specified finite alphabet and cost budget. -/
def Rep (B : Finset (G × ℕ)) (c R M : ℕ) (g : G) : Prop :=
  ∃ l : List (G × ℕ), (∀ a ∈ l, a ∈ B) ∧ value l = g ∧ cost c R l ≤ M

namespace Rep
variable {B D : Finset (G × ℕ)} {c R M N : ℕ} {g h : G}

theorem one (B : Finset (G × ℕ)) (c R M : ℕ) : Rep B c R M 1 := ⟨[], by simp⟩

theorem letter {a : G × ℕ} (ha : a ∈ B) : Rep B c R (R ^ (c - a.2)) a.1 := by
  exact ⟨[a], by simpa using ha, by simp, by simp⟩

theorem mono (h : Rep B c R M g) (hMN : M ≤ N) : Rep B c R N g := by
  obtain ⟨l, hl, he, hc⟩ := h
  exact ⟨l, hl, he, hc.trans hMN⟩

theorem alphabet_mono (h : Rep B c R M g) (hBD : B ⊆ D) : Rep D c R M g := by
  obtain ⟨l, hl, he, hc⟩ := h
  exact ⟨l, fun a ha => hBD (hl a ha), he, hc⟩

theorem mul (hg : Rep B c R M g) (hh : Rep B c R N h) : Rep B c R (M + N) (g * h) := by
  obtain ⟨l, hl, he, hc⟩ := hg
  obtain ⟨t, ht, hf, hd⟩ := hh
  refine ⟨l ++ t, ?_, by simp [he, hf], by simpa using Nat.add_le_add hc hd⟩
  intro a ha
  exact (List.mem_append.mp ha).elim (hl a) (ht a)

end Rep


/-- The subword of exactly one weight, with labels forgotten. -/
def lowWord (i : ℕ) (l : List (G × ℕ)) : List G :=
  (l.filter (fun a => a.2 = i)).map Prod.fst

omit [Group G] in
@[simp] theorem lowWord_nil (i : ℕ) : lowWord i ([] : List (G × ℕ)) = [] := rfl
omit [Group G] in
@[simp] theorem lowWord_cons (i : ℕ) (a : G × ℕ) (l : List (G × ℕ)) :
    lowWord i (a :: l) = if a.2 = i then a.1 :: lowWord i l else lowWord i l := by
  by_cases h : a.2 = i <;> simp [lowWord, h]

omit [Group G] in
theorem lowWord_length_mul_le_cost (c R i : ℕ) (l : List (G × ℕ)) :
    (lowWord i l).length * R ^ (c - i) ≤ cost c R l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [lowWord_cons, cost_cons]
    split_ifs with h
    · simp only [List.length_cons]
      rw [h]
      nlinarith
    · exact ih.trans (Nat.le_add_left _ _)

omit [Group G] in
theorem lowWord_length_le {c R i C : ℕ} (hR : 0 < R) (hi : i ≤ c)
    (l : List (G × ℕ)) (hl : cost c R l ≤ C * R ^ c) :
    (lowWord i l).length ≤ C * R ^ i := by
  have h := (lowWord_length_mul_le_cost c R i l).trans hl
  have he : C * R ^ c = (C * R ^ i) * R ^ (c - i) := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
  rw [he] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem prod_mem_finset_pow [DecidableEq G] (S : Finset G) (l : List G)
    (hl : ∀ a ∈ l, a ∈ S) : l.prod ∈ S ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ']
    exact Finset.mul_mem_mul (hl a (by simp)) (ih (fun b hb => hl b (by simp [hb])))

theorem lowWord_mem_pow [DecidableEq G] (S : Finset G) (i : ℕ) (l : List (G × ℕ))
    (hl : ∀ a ∈ l, a.2 = i → a.1 ∈ S) :
    (lowWord i l).prod ∈ S ^ (lowWord i l).length := by
  apply prod_mem_finset_pow
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  have hb' := List.mem_filter.mp hb
  exact hl b hb'.1 (by simpa using hb'.2)

end WeightedWords
end RecurrentSections
