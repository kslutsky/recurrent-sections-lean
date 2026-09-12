# Gromov and polynomial volume: formalization overview

The project proves both Gromov's equivalence and the required matching
polynomial-volume theorem. This work was developed on
`research/polynomial-volume`; the complete main characterizations use its
proved results.

## Exact conclusions

For every finitely generated group with an explicit finite word geometry:

```text
PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G
```

and

```text
PolynomialGrowth W.volume →
  ∃ C d : ℕ, 0 < C ∧ ∀ n,
    (n+1)^d ≤ C * W.volume n ∧ W.volume n ≤ C * (n+1)^d.
```

The second statement is `polynomialVolumeTheorem W` in
[NilpotentVolume.lean](RecurrentSections/NilpotentVolume.lean). It has no
unproved mathematical theorem argument. The common exponent is existential;
neither its explicit Bass–Guivarc'h rank formula nor positive asymptotic
volume ratios are asserted. Torsion, finite groups, arbitrary finite word
metrics, and nonnormal finite-index subgroups are covered.

## Proof and attribution

[GromovTheorem.lean](RecurrentSections/GromovTheorem.lean) imports Aaron
Hill's existing proof of the difficult implication at commit
`8db79f13cf211b570e3116301d91379fbc01cf3e`. The local adapter handles our
growth normalization and finite groups. The classical converse is proved
in [NilpotentGrowth.lean](RecurrentSections/NilpotentGrowth.lean), using
polynomial conjugation bounds, adjacent swaps, and multiset counting.
That earlier proof needs only a nonoptimal upper exponent.

The matching-volume proof follows the discrete last-lower-central-term
route in Druţu–Kapovich's 2017 author draft, Section 14.1.3 and Theorem
14.26, pp. 503–512:

1. [NilpotentPowers.lean](RecurrentSections/NilpotentPowers.lean) proves
   compression of powers and whole intrinsic balls in the last term of
   weight `k`: its intrinsic ball of radius `r^k` lies in an ambient ball
   of radius `C*(r+1)`.
2. [FilteredDistortion.lean](RecurrentSections/FilteredDistortion.lean)
   proves the complementary upper bound on intrinsic length,
   `length_H(g) ≤ C*(n+1)^k` for `g` in an ambient radius-`n` ball.
   The stronger formulation applies to the last term of any finite
   central filtration with additive commutator weights.
3. The collection proof uses finite positive relation blocks from
   [PositiveRelations.lean](RecurrentSections/PositiveRelations.lean).
   Dickson's lemma gives finitely many minimal nonzero positive relations
   in each abelian quotient. Every relation is their sum, with at most
   its letter count summands. This replaces explicit cyclic-basis and
   finite-order carry bookkeeping.
4. Weighted conjugation, permutation, and elimination preserve cost
   `O(R^c)`, where a weight-`j` letter costs `R^(c-j)`. The finite output
   alphabet is independent of the radius and of the input cost constant.
   [WeightedElimination.lean](RecurrentSections/WeightedElimination.lean)
   removes one weight, and `WeightedCollection.lean` iterates it. Every
   crossed lower-weight letter contributes its commutator error.
5. [QuotientGeometry.lean](RecurrentSections/QuotientGeometry.lean) proves
   exact quotient word metrics and upper and lower quotient/kernel ball
   counts. [VolumeExtensions.lean](RecurrentSections/VolumeExtensions.lean)
   combines matching quotient and intrinsic subgroup volume with both
   distortion bounds. This counting theorem requires normality, but
   neither centrality nor nilpotence.
6. [NilpotentMatchingVolume.lean](RecurrentSections/NilpotentMatchingVolume.lean)
   inducts on lower-central length. The last term is finitely generated
   abelian; its matching volume is proved using mathlib's abelian structure
   theorem and exact cubical balls. Hill's proved finite-generation theorem
   for nilpotent subgroups supplies its finite generation. Finite-index
   comparisons finish the virtually nilpotent case, and Gromov finishes
   the polynomial-growth case.

Numerical growth and volume definitions live in `VolumeGrowth.lean` and
`VolumeBounds.lean`, independently of Borel selection and Gromov's proof.
No undistorted central-extension estimate is used.

## Consequences and verification

The complete recurrence characterizations in
[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean)
now require only the group and word geometry. They cover arbitrary Borel
actions, and a separate equivalent formulation quantifies only over free
actions. The earlier conditional interfaces remain as modular lemmas;
their named propositions now have proved inhabitants.

Run `python3 scripts/check.py --record`. The complete branch verification passed: 63 modules, 68 Lean source files,
8836 build jobs, 100 principal theorem checks, and 830 compiled project
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur;
the injected custom axiom is correctly rejected. A separate consumer package
also passed, with 8835 build jobs. [verification/](verification/README.md)
records the logs, exact inputs, and source hashes.

Mathematical sources and software provenance are in [REFERENCES.md](REFERENCES.md).
The use of Codex for the local proofs, relation-block argument, integration,
and documentation is disclosed in [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md).
No first-formalization claim or new separate-agent or outside human review
is made.
