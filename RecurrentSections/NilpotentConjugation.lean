/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordGeometry
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace RecurrentSections
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [DecidableEq G]

/-- Conjugation of a finite set in the `c`th upper-central term grows
at most polynomially of degree `c`, for any subadditive length on a normal
subgroup containing that set. No properness or symmetry of that length is needed. -/
theorem exists_conjugation_bound_of_upperCentralSeries
    (S : Finset G) (N : Subgroup G) [N.Normal]
    (ell : N → ℕ) (hell_one : ell 1 = 0)
    (hell_mul : ∀ a b, ell (a * b) ≤ ell a + ell b)
    (c : ℕ) (A : Finset N)
    (hA : ∀ a ∈ A, (a : G) ∈ Subgroup.upperCentralSeries G c) :
    ∃ C : ℕ, ∀ n g, g ∈ S ^ n → ∀ a ∈ A,
      ell (MulAut.conjNormal g a) ≤ C * (n + 1) ^ c := by
  classical
  induction c generalizing A with
  | zero =>
    refine ⟨0, fun n g hg a ha => ?_⟩
    have ha1 : a = 1 := by
      apply Subtype.ext
      simpa using hA a ha
    simp [ha1, hell_one]
  | succ c ih =>
    let B : Finset N := (S ×ˢ A).image (fun p => MulAut.conjNormal p.1 p.2 * p.2⁻¹)
    have hB : ∀ b ∈ B, (b : G) ∈ Subgroup.upperCentralSeries G c := by
      intro b hb
      obtain ⟨⟨s, a⟩, hsa, rfl⟩ := Finset.mem_image.mp hb
      have ha := hA a (Finset.mem_product.mp hsa).2
      have hc := Subgroup.mem_upperCentralSeries_succ_iff.mp ha s
      have hinv := (Subgroup.upperCentralSeries G c).inv_mem hc
      change ⁅s, (a : G)⁆ ∈ Subgroup.upperCentralSeries G c
      simpa only [commutatorElement_inv] using hinv
    obtain ⟨D, hD⟩ := ih B hB
    let M := A.sup ell
    have hbound : ∀ n g, g ∈ S ^ n → ∀ a ∈ A,
        ell (MulAut.conjNormal g a) ≤ M + D * n * (n + 1) ^ c := by
      intro n
      induction n with
      | zero =>
        intro g hg a ha
        have hg1 : g = 1 := by simpa using hg
        subst g
        simpa using (Finset.le_sup ha : ell a ≤ M)
      | succ n hn =>
        intro g hg a ha
        rw [pow_succ] at hg
        obtain ⟨u, hu, s, hs, rfl⟩ := Finset.mem_mul.mp hg
        let b : N := MulAut.conjNormal s a * a⁻¹
        have hb : b ∈ B := Finset.mem_image.mpr ⟨(s, a), Finset.mem_product.mpr ⟨hs, ha⟩, rfl⟩
        have heq : MulAut.conjNormal (u * s) a =
            MulAut.conjNormal u b * MulAut.conjNormal u a := by
          simp [b, map_mul]
        calc
          ell (MulAut.conjNormal (u * s) a)
              = ell (MulAut.conjNormal u b * MulAut.conjNormal u a) := congrArg ell heq
          _ ≤ ell (MulAut.conjNormal u b) + ell (MulAut.conjNormal u a) := hell_mul _ _
          _ ≤ D * (n + 1) ^ c + (M + D * n * (n + 1) ^ c) :=
            Nat.add_le_add (hD n u hu b hb) (hn u hu a ha)
          _ = M + D * (n + 1) * (n + 1) ^ c := by ring
          _ ≤ M + D * (n + 1) * (n + 1 + 1) ^ c := by gcongr; omega
    refine ⟨M + D, fun n g hg a ha => (hbound n g hg a ha).trans ?_⟩
    calc
      M + D * n * (n + 1) ^ c ≤ M * (n + 1) ^ (c + 1) + D * (n + 1) * (n + 1) ^ c := by
        gcongr
        · exact Nat.le_mul_of_pos_right M (by positivity)
        · omega
      _ = (M + D) * (n + 1) ^ (c + 1) := by ring

/-- The preceding estimate applies to every finite set in a normal subgroup
of a nilpotent group. The normal subgroup need not be finitely generated
when an arbitrary subadditive length is supplied. -/
theorem exists_conjugation_bound_of_nilpotent
    [Group.IsNilpotent G] (S : Finset G) (N : Subgroup G) [N.Normal]
    (ell : N → ℕ) (hell_one : ell 1 = 0)
    (hell_mul : ∀ a b, ell (a * b) ≤ ell a + ell b) (A : Finset N) :
    ∃ C : ℕ, ∀ n g, g ∈ S ^ n → ∀ a ∈ A,
      ell (MulAut.conjNormal g a) ≤ C * (n + 1) ^ Group.nilpotencyClass G :=
  exists_conjugation_bound_of_upperCentralSeries S N ell hell_one hell_mul
    (Group.nilpotencyClass G) A (fun a _ => by
      rw [Subgroup.upperCentralSeries_nilpotencyClass]
      exact Subgroup.mem_top _)

end RecurrentSections
