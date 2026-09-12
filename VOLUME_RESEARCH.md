# Partial polynomial-volume formalization

This branch, `research/polynomial-volume`, preserves the work separated
from `main` on September 11, 2026. The base commit contains all completed
geometry and Borel tools and treats `PolynomialVolumeTheorem W` as an
explicit black box. This branch does not discharge that general input.

## Proved here

[VolumeBounds.lean](RecurrentSections/VolumeBounds.lean) proves:

- `eventual_mul_bounds_of_tendsto_ratio`: a positive ratio limit, with
  eventually positive denominator, gives integer multiplicative bounds
  in both directions on a tail.
- `twoSidedPolynomialGrowth_of_eventually`: positivity of every value
  absorbs finitely many exceptional radii into a common constant.
- `twoSidedPolynomialGrowth_of_tendsto_ratio`: for a positive natural-valued
  sequence, `v(n)/n^d → c > 0` gives all-radius bounds with the same `d`,
  including radius zero and `d = 0`. No monotonicity is needed.
- `twoSidedPolynomialGrowth_of_finite` and
  `polynomialVolumeTheorem_of_finite`: word volumes of finite groups have
  matching bounds of degree zero.

[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean)
also proves `universalRecurrence_of_finite` with no external theorem input.
The volume module and this corollary are preserved verbatim from the
pre-separation working tree.

[WordComparison.lean](RecurrentSections/WordComparison.lean) also constructs
word geometry from finite generation, proves a uniform Lipschitz bound for
homomorphisms, and compares ambient and finite-index subgroup word volumes.
The subgroup need not be normal. `VolumeBounds.lean` transfers polynomial
and matching polynomial bounds across these comparisons, proving invariance
under passage to finite index and change of finite generating set.

These comparison results have passed the full build and the expanded audit:
36 modules, 41 Lean files, 68 principal checks, and 524 compiled declarations.
The allowed logical axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining gap

The group-theoretic existence of matching polynomial bounds for every
finitely generated group of polynomial growth remains unformalized.
Breuillard's Theorem 1.1 gives the stronger positive asymptotic ratio;
the normalization above only proves the numerical deductions from that
hypothesis. A route through the permitted Gromov equivalence would still
require Bass–Guivarc'h estimates for finitely generated nilpotent groups
and passage through finite index. No such general proof is claimed here.

After integration of the proved Bernoulli test action, both branches have
the same two remaining inputs for the
full virtual-nilpotence equivalence, listed in
[STANDARD_INPUTS.md](STANDARD_INPUTS.md). All downstream deductions from
matching bounds and all required Borel tools are proved on `main`.

## Verification and attribution

Run `python3 scripts/check.py --record` to build all modules, audit
principal signatures and all compiled declarations, and test rejection
of a custom axiom. Branch-specific evidence is in
[verification/](verification/README.md).

Breuillard and the other mathematical sources retain their attribution
in [REFERENCES.md](REFERENCES.md). Codex developed the partial Lean proofs
with substantive mathematical and programming assistance, as disclosed
in [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md). These additions have kernel
verification but no new separate-agent or outside human review.
