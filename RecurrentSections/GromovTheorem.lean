/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WordComparison
import RecurrentSections.Growth
import Gromov.Gromov

/-! # Gromov's theorem for finite word geometry

The proof of polynomial growth implying virtual nilpotence is Aaron Hill's
formalization of the Kleiner--Tao proof, imported as a pinned dependency:
https://github.com/Aaron1011/gromov/tree/8db79f13cf211b570e3116301d91379fbc01cf3e

This module only supplies the bridge from our word geometry and `(n+1)^d`
normalization to Hill's `Generates` and `HasPolynomialGrowthD`, and handles
finite groups. The deep proof is upstream, not a new proof by this project.

Mathematical source: M. Gromov, *Groups of polynomial growth and expanding
maps*, Publ. Math. IHES 53 (1981), Main Theorem, p. 54,
https://doi.org/10.1007/BF02698687.
B. Kleiner, *A new proof of Gromov's theorem on groups of polynomial growth*,
J. Amer. Math. Soc. 23 (2010), 815--829, https://doi.org/10.1090/S0894-0347-09-00658-4.
T. Tao, *A proof of Gromov's theorem*, February 18, 2010,
https://terrytao.wordpress.com/2010/02/18/a-proof-of-gromovs-theorem/.
-/

namespace RecurrentSections

open scoped Pointwise

/-- Gromov's theorem with no unproved mathematical theorem as an argument. -/
theorem virtuallyNilpotent_of_polynomialGrowth {G : Type*} [Group G] [DecidableEq G]
    (W : WordGeometry G) (h : PolynomialGrowth W.volume) :
    Group.IsVirtuallyNilpotent G := by
  rcases finite_or_infinite G with hfinite | hinfinite
  · refine ⟨⊥, Group.isNilpotent_of_subsingleton, inferInstance⟩
  · obtain ⟨C, d, hC⟩ := h
    have hgrowth : HasPolynomialGrowthD W.generators d := by
      refine ⟨C * 2 ^ d, fun n hn => ?_⟩
      calc
        (W.generators ^ n).card ≤ C * (n + 1) ^ d := hC n
        _ ≤ C * (2 * n) ^ d := by gcongr; omega
        _ = (C * 2 ^ d) * n ^ d := by rw [mul_pow]; ring
    let inst : Generates :=
      { G := G
        g_group := inferInstance
        g_eq := inferInstance
        S := W.generators
        hS := ⟨⟨1, W.one_mem⟩⟩
        generates := by simp [W.closure_generators]
        one_mem := W.one_mem
        has_inv := W.inv_mem
        g_infinite := hinfinite
        g_growth := ⟨d, hgrowth⟩ }
    exact GeneratesNS.main_gromov_theorem (hGS := inst) d hgrowth

end RecurrentSections

