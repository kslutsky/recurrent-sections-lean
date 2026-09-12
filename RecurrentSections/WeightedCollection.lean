/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedElimination
import RecurrentSections.WordGeometry

namespace RecurrentSections
open scoped Pointwise commutatorElement
open WeightedWords
variable {G : Type*} [Group G] [DecidableEq G] {c : ℕ}

/-- Iterating weighted elimination collects a word into any later level
that contains its value. The cost degree and radius uniformity are preserved. -/
theorem exists_weighted_collection (F : CentralFiltration G c)
    (i n : ℕ) (hi : 0 < i) (hic : i + n ≤ c)
    (A : Finset (G × ℕ)) (hA : F.Valid i A) :
    ∃ B : Finset (G × ℕ), F.Valid (i + n) B ∧
      ∀ C : ℕ, ∃ D : ℕ, ∀ R : ℕ, 0 < R → ∀ l : List (G × ℕ),
        (∀ a ∈ l, a ∈ A) → cost c R l ≤ C * R ^ c →
        value l ∈ F.level (i + n) → Rep B c R (D * R ^ c) (value l) := by
  induction n with
  | zero =>
    refine ⟨A, by simpa using hA, fun C => ⟨C, ?_⟩⟩
    intro R hR l hl hcost hmem
    exact ⟨l, hl, rfl, hcost⟩
  | succ n ih =>
    obtain ⟨B, hB, hBC⟩ := ih (by omega)
    obtain ⟨E, hE, hEC⟩ := exists_weighted_elimination F (i + n) (by omega) (by omega) B hB
    refine ⟨E, by simpa only [Nat.add_succ] using hE, fun C => ?_⟩
    obtain ⟨D, hD⟩ := hBC C
    obtain ⟨K, hK⟩ := hEC D
    refine ⟨K, fun R hR l hl hcost hmem => ?_⟩
    have hmem' : value l ∈ F.level (i + n) := F.antitone (by omega) hmem
    obtain ⟨t, ht, he, hc⟩ := hD R hR l hl hcost hmem'
    have htn : value t ∈ F.level (i + n + 1) := by simpa only [he, Nat.add_succ] using hmem
    simpa only [he] using hK R hR t ht hc htn

/-- Words supported in the last level have intrinsic length bounded by
a fixed multiple of their weighted cost. -/
theorem exists_last_level_length_bound (F : CentralFiltration G c)
    (B : Finset (G × ℕ)) (hB : F.Valid c B) (V : WordGeometry (F.level c)) :
    ∃ M : ℕ, ∀ R K : ℕ, ∀ g : F.level c,
      Rep B c R K (g : G) → V.length g ≤ M * K := by
  classical
  let lift : B → F.level c := fun a => ⟨a.val.1,
    F.antitone (hB a a.property).1 (hB a a.property).2.2⟩
  let M := Finset.univ.sup (fun a => V.length (lift a))
  have hmain : ∀ l : List (G × ℕ), (∀ a ∈ l, a ∈ B) →
      ∀ g : F.level c, (g : G) = value l → V.length g ≤ M * l.length := by
    intro l
    induction l with
    | nil =>
      intro hl g hg
      have hg1 : g = 1 := Subtype.ext hg
      simp [hg1, V.length_one]
    | cons a l ih =>
      intro hl g hg
      have ha := hl a (by simp)
      let b := lift ⟨a, ha⟩
      let t : F.level c := ⟨value l, value_mem_level F hB l (fun x hx => hl x (by simp [hx]))⟩
      have he : g = b * t := Subtype.ext hg
      have hb : V.length b ≤ M := Finset.le_sup (f := fun a : B => V.length (lift a)) (Finset.mem_univ (⟨a, ha⟩ : B))
      have ht := ih (fun x hx => hl x (by simp [hx])) t rfl
      rw [he]
      exact (V.length_mul_le b t).trans (by simp only [List.length_cons]; nlinarith)
  refine ⟨M, fun R K g hg => ?_⟩
  obtain ⟨l, hl, he, hc⟩ := hg
  have hcost : cost c R l = l.length := by
    have hw : ∀ a ∈ l, a.2 = c := fun a ha => le_antisymm (hB a (hl a ha)).2.1 (hB a (hl a ha)).1
    clear he hc hmain
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [cost_cons, hw a (by simp)]
      simp only [Nat.sub_self, pow_zero, List.length_cons]
      rw [ih (fun x hx => hl x (by simp [hx])) (fun x hx => hw x (by simp [hx]))]
      omega
  exact (hmain l hl g he.symm).trans (Nat.mul_le_mul_left M (by omega))

end RecurrentSections
