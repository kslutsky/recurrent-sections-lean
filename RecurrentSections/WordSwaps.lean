/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

namespace RecurrentSections.WordSwaps

inductive Steps {α : Type*} : ℕ → List α → List α → Prop
  | refl (l : List α) : Steps 0 l l
  | swap (p q : List α) (a b : α) : Steps 1 (p ++ a :: b :: q) (p ++ b :: a :: q)
  | trans {m n : ℕ} {l t r : List α} : Steps m l t → Steps n t r → Steps (m + n) l r

variable {α : Type*}

theorem Steps.perm {n : ℕ} {l r : List α} (h : Steps n l r) : l.Perm r := by
  induction h with
  | refl l => exact List.Perm.refl l
  | swap p q a b => exact List.Perm.append_left p (List.Perm.swap b a q)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem Steps.cons (a : α) {n : ℕ} {l r : List α} (h : Steps n l r) :
    Steps n (a :: l) (a :: r) := by
  induction h with
  | refl l => exact Steps.refl _
  | swap p q b c => exact Steps.swap (a :: p) q b c
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem move_head (a : α) (p q : List α) :
    Steps p.length (a :: (p ++ q)) (p ++ a :: q) := by
  induction p with
  | nil => exact Steps.refl _
  | cons b p ih =>
    have hs := (Steps.swap [] (p ++ q) a b).trans (ih.cons b)
    simpa [Nat.add_comm] using hs

/-- Two permutations of a length-`n` word are connected by at most `n^2`
adjacent transpositions. Intermediate words have the same multiset. -/
theorem exists_steps_of_perm {l r : List α} (h : l.Perm r) :
    ∃ k, k ≤ l.length ^ 2 ∧ Steps k l r := by
  induction l generalizing r with
  | nil =>
    have hr : r = [] := List.length_eq_zero_iff.mp (by simpa using h.length_eq.symm)
    subst r
    exact ⟨0, by simp, Steps.refl []⟩
  | cons a l ih =>
    have ha : a ∈ r := h.mem_iff.mp (by simp)
    obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp ha
    have hm : (a :: (p ++ q)).Perm (p ++ a :: q) := List.perm_middle.symm
    have ht : l.Perm (p ++ q) := (List.perm_cons a).mp (h.trans hm.symm)
    obtain ⟨k, hk, hs⟩ := ih ht
    refine ⟨k + p.length, ?_, (hs.cons a).trans (move_head a p q)⟩
    have hp : p.length ≤ l.length := by
      have htlen := ht.length_eq
      simp only [List.length_append] at htlen
      omega
    simp only [List.length_cons]
    nlinarith

end RecurrentSections.WordSwaps
