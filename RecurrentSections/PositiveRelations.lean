/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Minimal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Fintype
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

namespace RecurrentSections

variable {ι A : Type*} [Fintype ι] [CommGroup A]

/-- Evaluation of a nonnegative multiplicity vector in an abelian group. -/
def relationEval (f : ι → A) (v : ι → ℕ) : A := ∏ i, f i ^ v i

@[simp] theorem relationEval_zero (f : ι → A) : relationEval f 0 = 1 := by
  simp [relationEval]

theorem relationEval_add (f : ι → A) (v w : ι → ℕ) :
    relationEval f (v + w) = relationEval f v * relationEval f w := by
  simp [relationEval, pow_add, Finset.prod_mul_distrib]

/-- Dickson's lemma gives finitely many positive relation vectors. Every
positive relation is a sum of these, with at most its total number of letters
summands. The abelian target need not be finitely generated or torsion-free. -/
theorem exists_finite_positive_relations (f : ι → A) :
    ∃ R : Finset (ι → ℕ),
      (∀ v ∈ R, v ≠ 0 ∧ relationEval f v = 1) ∧
      ∀ v, relationEval f v = 1 →
        ∃ l : List (ι → ℕ), (∀ a ∈ l, a ∈ R) ∧ l.sum = v ∧ l.length ≤ ∑ i, v i := by
  classical
  let P : (ι → ℕ) → Prop := fun v => v ≠ 0 ∧ relationEval f v = 1
  have hfin : {v | Minimal P v}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain P)
  let R := hfin.toFinset
  refine ⟨R, fun v hv => (hfin.mem_toFinset.mp hv).prop, ?_⟩
  have hmain : ∀ n, ∀ v : ι → ℕ, (∑ i, v i) = n → relationEval f v = 1 →
      ∃ l : List (ι → ℕ), (∀ a ∈ l, a ∈ R) ∧ l.sum = v ∧ l.length ≤ ∑ i, v i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv he
      by_cases hz : v = 0
      · subst v
        exact ⟨[], by simp⟩
      obtain ⟨a, hav, ha⟩ := exists_minimal_le_of_wellFoundedLT P v ⟨hz, he⟩
      have hRa : a ∈ R := hfin.mem_toFinset.mpr ha
      let w : ι → ℕ := v - a
      have haw : a + w = v := by
        funext i
        exact Nat.add_sub_of_le (hav i)
      have hw : relationEval f w = 1 := by
        have hh := relationEval_add f a w
        rw [haw, he, ha.prop.2, one_mul] at hh
        exact hh.symm
      have has : 0 < ∑ i, a i := by
        by_contra! h
        have heq : ∑ i, a i = 0 := Nat.eq_zero_of_le_zero h
        have hall := Finset.sum_eq_zero_iff.mp heq
        apply ha.prop.1
        funext i
        exact hall i (Finset.mem_univ i)
      have hsum : (∑ i, a i) + ∑ i, w i = ∑ i, v i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => congrFun haw i)
      obtain ⟨l, hl, hls, hlen⟩ := ih (∑ i, w i) (by omega) w rfl hw
      refine ⟨a :: l, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hRa
        · exact hl b hb
      · simpa [hls] using haw
      · simp only [List.length_cons]
        omega
  exact fun v hv => hmain (∑ i, v i) v rfl hv


noncomputable def multiplicityWord (v : ι → ℕ) : List ι :=
  (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm v)).toList

@[simp] theorem count_multiplicityWord [DecidableEq ι] (v : ι → ℕ) (i : ι) :
    (multiplicityWord v).count i = v i := by
  change (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm v)).toList.count i = v i
  rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
  rfl

theorem relationEval_counts [DecidableEq ι] (f : ι → A) (l : List ι) :
    relationEval f (fun i => l.count i) = (l.map f).prod := by
  induction l with
  | nil => simp [relationEval]
  | cons a l ih =>
    simp only [List.count_cons, List.map_cons, List.prod_cons]
    calc
      relationEval f (fun i => l.count i + if a == i then 1 else 0)
          = relationEval f (fun i => l.count i) * relationEval f (fun i => if a == i then 1 else 0) :=
        relationEval_add f _ _
      _ = f a * (l.map f).prod := by
        rw [ih]
        simp [relationEval, beq_iff_eq, mul_comm]

/-- Every word that evaluates to the identity in an abelian target can be
permuted into a concatenation of words from one fixed finite set of positive
relations. The number of relation words is at most the input length. -/
theorem exists_finite_relation_words (f : ι → A) :
    ∃ R : Finset (List ι),
      (∀ l ∈ R, l ≠ [] ∧ (l.map f).prod = 1) ∧
      ∀ l : List ι, (l.map f).prod = 1 →
        ∃ L : List (List ι), (∀ a ∈ L, a ∈ R) ∧ l.Perm L.flatten ∧ L.length ≤ l.length := by
  classical
  obtain ⟨R, hR, h⟩ := exists_finite_positive_relations f
  refine ⟨R.image multiplicityWord, ?_, ?_⟩
  · intro l hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
    constructor
    · intro he
      apply (hR v hv).1
      funext i
      have := count_multiplicityWord v i
      rw [he] at this
      exact this.symm
    · rw [← relationEval_counts]
      simpa using (hR v hv).2
  · intro l hl
    obtain ⟨L, hL, he, hlen⟩ := h (fun i => l.count i) (by rwa [relationEval_counts])
    refine ⟨L.map multiplicityWord, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_image.mpr ⟨v, hL v hv, rfl⟩
    · apply List.perm_iff_count.mpr
      intro i
      rw [List.count_flatten, List.map_map]
      simp only [Function.comp_def, count_multiplicityWord]
      have hsum : (L.map (fun v => v i)).sum = L.sum i := by
        clear hL he hlen
        induction L with
        | nil => simp
        | cons v L ih => simp [ih]
      rw [hsum, he]
    · rw [List.length_map]
      have hc : (∑ i, l.count i) = l.length := by
        simpa using (Multiset.sum_count_eq_card (s := Finset.univ) (m := (l : Multiset ι))
          (fun i _ => Finset.mem_univ i))
      exact hlen.trans hc.le


open scoped IsMulCommutative in
/-- The same relation decomposition applies when only the images of the
letters commute; the ambient target group can be nonabelian. -/
theorem exists_finite_relation_words_of_commute {H : Type*} [Group H]
    (f : ι → H) (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ R : Finset (List ι),
      (∀ l ∈ R, l ≠ [] ∧ (l.map f).prod = 1) ∧
      ∀ l : List ι, (l.map f).prod = 1 →
        ∃ L : List (List ι), (∀ a ∈ L, a ∈ R) ∧ l.Perm L.flatten ∧ L.length ≤ l.length := by
  classical
  let N := Subgroup.closure (Set.range f)
  let : IsMulCommutative N := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hcomm i j).eq)
  let : CommGroup N := inferInstance
  let fN : ι → N := fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hp (l : List ι) : (((l.map fN).prod : N) : H) = (l.map f).prod := by
    have := map_list_prod N.subtype (l.map fN)
    simpa only [List.map_map, Function.comp_def, fN, Subgroup.coe_subtype] using this
  obtain ⟨R, hR, h⟩ := exists_finite_relation_words fN
  refine ⟨R, fun l hl => ⟨(hR l hl).1, ?_⟩, fun l hl => ?_⟩
  · rw [← hp, (hR l hl).2]
    rfl
  · apply h
    apply Subtype.ext
    simpa only [hp, Subgroup.coe_one] using hl

end RecurrentSections
