/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.FilteredDistortion
import RecurrentSections.VolumeExtensions
import RecurrentSections.NilpotentPowers
import RecurrentSections.AbelianVolume
import Gromov.Unipotent.FG

/-! # Matching polynomial volume for nilpotent groups

This proves the existence-of-degree consequence of Bass--Guivarc'h.
The discrete proof follows the last-lower-central-subgroup distortion
route in Druţu--Kapovich, *Geometric Group Theory*, 2017 author draft,
Section 14.1.3 and Theorem 14.26, pp. 503--512:
https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf

Classical sources: H. Bass, Proc. London Math. Soc. (3) 25 (1972), 603--614,
https://doi.org/10.1112/plms/s3-25.4.603; Y. Guivarc'h, Bull. Soc. Math.
France 101 (1973), 333--379, https://doi.org/10.24033/bsmf.1764.

Finite generation of nilpotent subgroups uses Aaron Hill's proved
`fg_of_subgroup_fg_nilpotent` from the pinned external Gromov development.
The distortion, relation-block collection, volume counting, and induction
proofs are local. Neither an explicit rank formula nor positive volume
asymptotics are claimed.
-/

namespace RecurrentSections
variable {G : Type*} [Group G] [DecidableEq G]

/-- A finite lower central series gives matching integer-power word-volume
bounds. The exponent is existential; this does not assert its rank formula. -/
theorem twoSidedPolynomialGrowth_of_lowerCentralSeries_eq_bot (c : ℕ)
    (W : WordGeometry G) (hc : (⊤ : Subgroup G).lowerCentralSeries c = ⊥) :
    TwoSidedPolynomialGrowth W.volume := by
  classical
  induction c generalizing G with
  | zero =>
    have hG : ∀ g : G, g = 1 := by
      intro g
      have hg : g ∈ (⊥ : Subgroup G) := hc ▸ Subgroup.mem_top g
      simpa using hg
    let : Subsingleton G := ⟨fun a b => by rw [hG a, hG b]⟩
    exact twoSidedPolynomialGrowth_of_finite W
  | succ c ih =>
    let : Group.IsNilpotent G := (Subgroup.nilpotent_iff_lowerCentralSeries).mpr ⟨c + 1, hc⟩
    let N := (⊤ : Subgroup G).lowerCentralSeries c
    have hN : N ≤ Subgroup.center G :=
      (Subgroup.commutator_top_right_eq_bot_iff_le_center).mp hc
    let : CommGroup N := { (inferInstance : Group N) with
      mul_comm a b := Subtype.ext (Subgroup.mem_center_iff.mp (hN b.property) a) }
    let : Group.FG N := (Group.fg_iff_subgroup_fg N).mpr (fg_of_subgroup_fg_nilpotent W.fg N)
    let V := WordGeometry.ofFG N
    let q := QuotientGroup.mk' N
    let Q := W.map q QuotientGroup.mk_surjective
    have htop : (⊤ : Subgroup G).map q = ⊤ :=
      Subgroup.map_top_of_surjective q QuotientGroup.mk_surjective
    have hqc : (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries c = ⊥ := by
      rw [← htop, ← Subgroup.map_lowerCentralSeries, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hQ := ih Q hqc
    have hV := twoSidedPolynomialGrowth_of_commGroup V
    obtain ⟨A, hA, hupper⟩ := exists_last_lowerCentralSeries_distortion_bound c W hc V
    obtain ⟨B, hB, hcompression⟩ := exists_last_lowerCentralSeries_ball_inclusion c W hc V
    exact twoSidedPolynomialGrowth_of_normal_subgroup_distortion W N V (c + 1) A B
      hupper hcompression hV hQ

/-- The matching-bounds consequence of the Bass--Guivarc'h theorem,
proved for arbitrary finitely generated nilpotent groups, including torsion. -/
theorem twoSidedPolynomialGrowth_of_nilpotent [Group.IsNilpotent G] (W : WordGeometry G) :
    TwoSidedPolynomialGrowth W.volume :=
  twoSidedPolynomialGrowth_of_lowerCentralSeries_eq_bot (Group.nilpotencyClass G) W
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

end RecurrentSections
