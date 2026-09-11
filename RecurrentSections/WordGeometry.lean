/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic

namespace RecurrentSections

open scoped Pointwise

/-- A finite symmetric generating set containing the identity. The
generation condition is written as exhaustion by finite word balls. -/
structure WordGeometry (G : Type*) [Group G] [DecidableEq G] where
  generators : Finset G
  one_mem : 1 ∈ generators
  inv_mem : ∀ g ∈ generators, g⁻¹ ∈ generators
  generates : ∀ g : G, ∃ n : ℕ, g ∈ generators ^ n

variable {G : Type*} [Group G] [DecidableEq G]

namespace WordGeometry

def ball (W : WordGeometry G) (n : ℕ) : Finset G := W.generators ^ n

def volume (W : WordGeometry G) (n : ℕ) : ℕ := (W.ball n).card

noncomputable def length (W : WordGeometry G) (g : G) : ℕ :=
  Nat.find (W.generates g)

theorem ball_mono (W : WordGeometry G) {m n : ℕ} (h : m ≤ n) :
    W.ball m ⊆ W.ball n := Finset.pow_subset_pow_right W.one_mem h

theorem volume_mono (W : WordGeometry G) : Monotone W.volume :=
  fun _ _ h => Finset.card_le_card (W.ball_mono h)

theorem one_mem_ball (W : WordGeometry G) (n : ℕ) : 1 ∈ W.ball n :=
  Finset.one_mem_pow W.one_mem

theorem volume_pos (W : WordGeometry G) (n : ℕ) : 0 < W.volume n :=
  Finset.card_pos.mpr ⟨1, W.one_mem_ball n⟩

theorem mem_ball_iff_length_le (W : WordGeometry G) (g : G) (n : ℕ) :
    g ∈ W.ball n ↔ W.length g ≤ n := by
  constructor
  · exact Nat.find_min' (W.generates g)
  · intro h
    exact W.ball_mono h (Nat.find_spec (W.generates g))

theorem mul_mem_ball (W : WordGeometry G) {g h : G} {m n : ℕ}
    (hg : g ∈ W.ball m) (hh : h ∈ W.ball n) : g * h ∈ W.ball (m + n) := by
  simpa only [ball, pow_add] using Finset.mul_mem_mul hg hh

theorem inv_mem_ball (W : WordGeometry G) {g : G} {n : ℕ}
    (hg : g ∈ W.ball n) : g⁻¹ ∈ W.ball n := by
  induction n generalizing g with
  | zero => simpa [ball] using hg
  | succ n ih =>
    rw [ball, pow_succ] at hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hg
    have hi := Finset.mul_mem_mul (W.inv_mem b hb) (ih ha)
    simpa only [ball, pow_succ', mul_inv_rev] using hi

end WordGeometry

variable {X : Type*} [MulAction G X]

/-- The finite union of translates of `C` indexed by a word ball. -/
def neighborhood (W : WordGeometry G) (m : ℕ) (C : Set X) : Set X :=
  ⋃ g ∈ W.ball m, g • C

/-- Distinct points of `C` have orbit word distance strictly greater than `r`. -/
def Separated (W : WordGeometry G) (r : ℕ) (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ g ∈ W.ball r, g • x = y → x = y

/-- Every orbit meets the set. This requirement is not used in the
obstruction, but is included in the stated cross-section property. -/
def CompleteSection (C : Set X) : Prop :=
  ∀ x : X, ∃ g : G, ∃ c ∈ C, g • c = x

/-- Everywhere recurrence, expressed by explicit displacement witnesses.
For integer word metrics this is exactly `d(x,Cₙ) < ε rₙ` infinitely often. -/
def Recurrent (W : WordGeometry G) (r : ℕ → ℕ) (C : ℕ → Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ x : X, ∀ N : ℕ,
    ∃ n, N ≤ n ∧ ∃ g : G, ∃ c ∈ C n,
      g • c = x ∧ (W.length g : ℝ) < ε * (r n : ℝ)

end RecurrentSections
