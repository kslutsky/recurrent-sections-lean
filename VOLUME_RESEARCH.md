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

## Remaining gap

The group-theoretic existence of matching polynomial bounds for every
finitely generated group of polynomial growth remains unformalized.
Breuillard's Theorem 1.1 gives the stronger positive asymptotic ratio;
the normalization above only proves the numerical deductions from that
hypothesis. A route through the permitted Gromov equivalence would still
require Bass–Guivarc'h estimates for finitely generated nilpotent groups
and passage through finite index. No such general proof is claimed here.

Both branches therefore have the same three remaining inputs for the
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
