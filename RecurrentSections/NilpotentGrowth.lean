/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.NilpotentConjugation
import RecurrentSections.WordCollection
import RecurrentSections.GrowthComparison
import Gromov.Unipotent.FG

/-! # Polynomial upper bounds for nilpotent groups

This is a discrete collection proof of the classical polynomial-growth
result. Polynomial conjugation bounds and quadratically many adjacent swaps
reduce word-ball counting to the commutator subgroup. Induction on the
lower-central length closes the argument. The exponent is intentionally
not claimed to be the sharp Bass--Guivarc'h exponent.

The finite generation of nilpotent subgroups is supplied by Aaron Hill's
proved `fg_of_subgroup_fg_nilpotent` in the pinned Gromov development;
see REFERENCES.md for attribution. The collection and counting arguments
in this module and its local dependencies were developed for this project.
The classical growth theorem is due to Wolf; Guivarc'h's 1973 paper,
Section III (Theorem III.3 and its preparatory lemmas), also gives bounds
using polynomially controlled conjugation.
-/

namespace RecurrentSections
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G] [DecidableEq G]

/-- Polynomial growth of a normal subgroup containing the elementary
commutators implies polynomial growth of the ambient nilpotent group.
Conjugates are measured in the subgroup word metric. -/
theorem polynomialGrowth_of_nilpotent_normal_subgroup [Group.IsNilpotent G]
    (W : WordGeometry G) (N : Subgroup G) [N.Normal] (V : WordGeometry N)
    (hcomm : ∀ a ∈ W.generators, ∀ b ∈ W.generators, ⁅a, b⁆ ∈ N)
    (hV : PolynomialGrowth V.volume) : PolynomialGrowth W.volume := by
  classical
  let A : Finset N := Finset.univ.image (fun p : W.generators × W.generators =>
    ⟨⁅(p.1 : G), (p.2 : G)⁆, hcomm _ p.1.property _ p.2.property⟩)
  obtain ⟨C, hC⟩ := exists_conjugation_bound_of_nilpotent W.generators N
    V.length V.length_one V.length_mul_le A
  let c := Group.nilpotencyClass G
  have hswap : ∀ n, ∀ a ∈ W.generators, ∀ b ∈ W.generators, ∀ g ∈ W.ball n,
      ∃ h ∈ V.ball (C * (n + 1) ^ c), (h : G) = g * ⁅a, b⁆ * g⁻¹ := by
    intro n a ha b hb g hg
    let q : N := ⟨⁅a, b⁆, hcomm a ha b hb⟩
    have hq : q ∈ A := Finset.mem_image.mpr ⟨(⟨a, ha⟩, ⟨b, hb⟩), Finset.mem_univ _, rfl⟩
    refine ⟨MulAut.conjNormal g q, ?_, ?_⟩
    · exact (V.mem_ball_iff_length_le _ _).mpr (hC n g hg q hq)
    · exact MulAut.conjNormal_apply g q
  obtain ⟨P, d, hPd⟩ := hV
  refine ⟨P * (C + 1) ^ d, (c + 2) * d + W.generators.card, fun n => ?_⟩
  have hr : n ^ 2 * (C * (n + 1) ^ c) + 1 ≤ (C + 1) * (n + 1) ^ (c + 2) := by
    calc
      n ^ 2 * (C * (n + 1) ^ c) + 1
          ≤ (n + 1) ^ 2 * (C * (n + 1) ^ c) + (n + 1) ^ (c + 2) := by
            gcongr
            · omega
            · have hp : 0 < (n + 1) ^ (c + 2) := by positivity
              omega
      _ = (C + 1) * (n + 1) ^ (c + 2) := by rw [pow_add]; ring
  calc
    W.volume n ≤ V.volume (n ^ 2 * (C * (n + 1) ^ c)) * (n + 1) ^ W.generators.card :=
      volume_le_of_swap_bound W N V n (C * (n + 1) ^ c) (hswap n)
    _ ≤ (P * (n ^ 2 * (C * (n + 1) ^ c) + 1) ^ d) * (n + 1) ^ W.generators.card :=
      Nat.mul_le_mul_right _ (hPd _)
    _ ≤ (P * ((C + 1) * (n + 1) ^ (c + 2)) ^ d) * (n + 1) ^ W.generators.card := by gcongr
    _ = (P * (C + 1) ^ d) * (n + 1) ^ ((c + 2) * d + W.generators.card) := by
      rw [mul_pow, ← pow_mul, pow_add]
      ring

omit [DecidableEq G] in
/-- The lower central series of the commutator subgroup starts one step
later than that of the ambient group; this coarse inclusion suffices for
induction on nilpotency length. -/
theorem commutator_lowerCentralSeries_le (n : ℕ) :
    (_root_.commutator G).lowerCentralSeries n ≤ (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-- Every finitely generated nilpotent group has a polynomial upper bound.
The exponent furnished by this collection argument is not asserted optimal. -/
theorem polynomialGrowth_of_lowerCentralSeries_eq_bot (c : ℕ)
    (W : WordGeometry G) (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) :
    PolynomialGrowth W.volume := by
  classical
  induction c generalizing G with
  | zero =>
    have hG : ∀ g : G, g = 1 := by
      intro g
      have hg : g ∈ (⊥ : Subgroup G) := hc ▸ Subgroup.mem_top g
      simpa using hg
    let : Subsingleton G := ⟨fun a b => by rw [hG a, hG b]⟩
    let := Fintype.ofFinite G
    refine ⟨Fintype.card G, 0, fun n => ?_⟩
    simpa [WordGeometry.volume] using Finset.card_le_univ (W.ball n)
  | succ c ih =>
    let : Group.IsNilpotent G := (Subgroup.nilpotent_iff_lowerCentralSeries).mpr ⟨c + 1, hc⟩
    let N := _root_.commutator G
    let : Group.FG N := (Group.fg_iff_subgroup_fg N).mpr (fg_of_subgroup_fg_nilpotent W.fg N)
    let V := WordGeometry.ofFG N
    have hN : (⊤ : Subgroup N).lowerCentralSeries c = ⊥ := by
      rw [← Subgroup.map_subtype_inj, Subgroup.map_bot, Subgroup.top_subtype_lowerCentralSeries]
      exact le_bot_iff.mp ((commutator_lowerCentralSeries_le (G := G) c).trans hc.le)
    exact polynomialGrowth_of_nilpotent_normal_subgroup W N V
      (fun a _ b _ => Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
      (ih V hN)

theorem polynomialGrowth_of_nilpotent [Group.IsNilpotent G] (W : WordGeometry G) :
    PolynomialGrowth W.volume :=
  polynomialGrowth_of_lowerCentralSeries_eq_bot (Group.nilpotencyClass G) W
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

/-- Finite extensions of finitely generated nilpotent groups have polynomial
word growth. No two-sided volume theorem is used. -/
theorem polynomialGrowth_of_virtuallyNilpotent (W : WordGeometry G)
    (h : Group.IsVirtuallyNilpotent G) : PolynomialGrowth W.volume := by
  obtain ⟨N, hN, hindex⟩ := h
  let : Group.IsNilpotent N := hN
  let : N.FiniteIndex := hindex
  let : Group.FG G := W.fg
  let : Group.FG N := Subgroup.fg_of_index_ne_zero N
  let V := WordGeometry.ofFG N
  exact (polynomialGrowth_iff_subgroup W N V).mpr (polynomialGrowth_of_nilpotent V)

end RecurrentSections
