/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedConjugation

namespace RecurrentSections
open scoped Pointwise commutatorElement
open WeightedWords
variable {G : Type*} [Group G] [DecidableEq G] {c : ℕ}

/-- Simultaneous weighted conjugation bounds for a finite weighted alphabet.
One output alphabet and one constant work for all its letters. -/
theorem exists_uniform_weighted_conjugation_bound (F : CentralFiltration G c)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (S : Finset G)
    (hS : ∀ s ∈ S, s ∈ F.level i) (A : Finset (G × ℕ)) (hA : F.Valid j A) :
    ∃ B : Finset (G × ℕ), F.Valid j B ∧
      ∀ L : ℕ, ∃ D : ℕ, ∀ R : ℕ, 0 < R → ∀ m g, g ∈ S ^ m → m ≤ L * R ^ i →
        ∀ a ∈ A, Rep B c R (D * R ^ (c - a.2)) (g * a.1 * g⁻¹) := by
  classical
  have hex (a : A) := exists_weighted_conjugation_bound F i a.val.2 hi
    (hj.trans_le (hA a a.property).1) S {a.val.1} hS (by
      intro g hg
      have hg' : g = a.val.1 := Finset.mem_singleton.mp hg
      subst g
      exact (hA a a.property).2.2)
  choose B hB hC using hex
  let U := Finset.univ.biUnion B
  have hBU (a : A) : B a ⊆ U := Finset.subset_biUnion_of_mem B (Finset.mem_univ a)
  refine ⟨U, ?_, fun L => ?_⟩
  · intro b hb
    obtain ⟨a, ha, hb⟩ := Finset.mem_biUnion.mp hb
    exact ⟨(hA a a.property).1.trans (hB a b hb).1, (hB a b hb).2⟩
  · choose C hC' using (fun a => hC a L)
    let D := Finset.univ.sup C
    refine ⟨D, fun R hR m g hg hm a ha => ?_⟩
    have hh := hC' ⟨a, ha⟩ R hR m g hg hm a.1 (Finset.mem_singleton_self _)
    exact (hh.alphabet_mono (hBU ⟨a, ha⟩)).mono
      (Nat.mul_le_mul_right _ (show C ⟨a, ha⟩ ≤ D from Finset.le_sup (Finset.mem_univ (⟨a, ha⟩ : A))))

end RecurrentSections
