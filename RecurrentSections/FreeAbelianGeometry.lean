/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordGeometry
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators

/-! # Cubical word balls in finitely generated free abelian groups

For the symmetric generating set `{-1, 0, 1}^d` in `ℤ^d`, the ball of
radius `n` is exactly `[-n, n]^d`. The volume formula includes rank zero
and radius zero. This elementary model is used to transfer volume bounds
through the structure theorem for finitely generated abelian groups.
-/

namespace RecurrentSections.FreeAbelianGeometry
open scoped Pointwise

noncomputable def cube (d n : ℕ) : Finset (Multiplicative (Fin d → ℤ)) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)).map
    Multiplicative.ofAdd.toEmbedding

@[simp] theorem mem_cube {d n : ℕ} {g : Multiplicative (Fin d → ℤ)} :
    g ∈ cube d n ↔ ∀ i, -(n : ℤ) ≤ g.toAdd i ∧ g.toAdd i ≤ n := by
  simp [cube, Fintype.mem_piFinset]

theorem card_cube (d n : ℕ) : (cube d n).card = (2 * n + 1) ^ d := by
  simp [cube, Fintype.card_piFinset, Int.card_Icc]
  congr 1
  omega

theorem cube_zero (d : ℕ) : cube d 0 = 1 := by
  ext g
  simp only [mem_cube, Nat.cast_zero, neg_zero, Finset.mem_one]
  constructor
  · intro h
    apply Multiplicative.ext
    funext i
    exact le_antisymm (h i).2 (h i).1
  · rintro rfl
    simp

theorem cube_succ (d n : ℕ) : cube d (n + 1) = cube d n * cube d 1 := by
  classical
  ext g
  constructor
  · intro hg
    have hbounds := mem_cube.mp hg
    let b : Fin d → ℤ := fun i => if 0 < g.toAdd i then 1 else if g.toAdd i < 0 then -1 else 0
    let a : Fin d → ℤ := g.toAdd - b
    refine Finset.mem_mul.mpr ⟨Multiplicative.ofAdd a, ?_, Multiplicative.ofAdd b, ?_, ?_⟩
    · apply mem_cube.mpr
      intro i
      have hi := hbounds i
      dsimp [a, b]
      split_ifs <;> omega
    · apply mem_cube.mpr
      intro i
      dsimp [b]
      split_ifs <;> norm_num
    · apply Multiplicative.ext
      change a + b = g.toAdd
      dsimp [a]
      abel
  · intro hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hg
    apply mem_cube.mpr
    intro i
    have hai := mem_cube.mp ha i
    have hbi := mem_cube.mp hb i
    change -(↑(n + 1) : ℤ) ≤ a.toAdd i + b.toAdd i ∧ a.toAdd i + b.toAdd i ≤ (n + 1 : ℕ)
    push_cast at *
    omega

theorem cube_one_pow (d n : ℕ) : (cube d 1) ^ n = cube d n := by
  induction n with
  | zero => exact (cube_zero d).symm
  | succ n ih => rw [pow_succ, ih, ← cube_succ d n]

noncomputable def wordGeometry (d : ℕ) : WordGeometry (Multiplicative (Fin d → ℤ)) where
  generators := cube d 1
  one_mem := mem_cube.mpr (fun _ => by norm_num)
  inv_mem g hg := by
    apply mem_cube.mpr
    intro i
    have hi := mem_cube.mp hg i
    change -(↑1 : ℤ) ≤ -g.toAdd i ∧ -g.toAdd i ≤ (1 : ℕ)
    omega
  generates g := by
    classical
    let n := ∑ i : Fin d, (g.toAdd i).natAbs
    refine ⟨n, ?_⟩
    rw [cube_one_pow]
    apply mem_cube.mpr
    intro i
    have hi : (g.toAdd i).natAbs ≤ n := by
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (g.toAdd j).natAbs) (Finset.mem_univ i)
    have hcast : ((g.toAdd i).natAbs : ℤ) ≤ n := by exact_mod_cast hi
    have habs : |g.toAdd i| ≤ n := by simpa using hcast
    exact abs_le.mp habs

theorem volume_wordGeometry (d n : ℕ) : (wordGeometry d).volume n = (2 * n + 1) ^ d := by
  change ((cube d 1) ^ n).card = _
  rw [cube_one_pow, card_cube]

end RecurrentSections.FreeAbelianGeometry

