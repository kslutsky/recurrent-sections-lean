# Polynomial-volume formalization: research branch

This branch is `research/polynomial-volume`. Main remains at the earlier
black-box interface. The full request is not yet complete: the general
nonabelian nilpotent volume estimate remains an explicit mathematical input.

## Proved here

- [GromovTheorem.lean](RecurrentSections/GromovTheorem.lean) proves that
  polynomial growth of our word balls implies virtual nilpotence. The deep
  theorem is Aaron Hill's existing formalization, imported at commit
  `8db79f13cf211b570e3116301d91379fbc01cf3e`; our adapter handles finite
  groups and the normalization of growth. The fixed-action and universal
  recurrence implications no longer request Gromov as an argument. The
  full equivalence is now proved: `NilpotentGrowth.lean` supplies the
  converse by local discrete collection and finite-index comparison.
- [WordComparison.lean](RecurrentSections/WordComparison.lean) constructs
  word geometry from finite generation, proves homomorphism length bounds,
  and compares word volumes across finite-index subgroups, without normality.
- [VolumeBounds.lean](RecurrentSections/VolumeBounds.lean) transfers polynomial
  and matching bounds across these comparisons and across isomorphisms.
  It also normalizes positive asymptotic ratios and eventual bounds,
  including radius zero, and proves the finite-group case.
- [FreeAbelianGeometry.lean](RecurrentSections/FreeAbelianGeometry.lean)
  proves that cubical generators in `ℤ^d` give exact volume `(2*n+1)^d`.
  [AbelianVolume.lean](RecurrentSections/AbelianVolume.lean) uses mathlib's
  finitely generated abelian structure theorem and finite-index comparisons
  to prove matching bounds for every finitely generated abelian group,
  including torsion and arbitrary finite word metrics.
- [NilpotentVolume.lean](RecurrentSections/NilpotentVolume.lean) reduces
  the polynomial-volume theorem to one explicit
  nilpotent matching-volume estimate. Gromov's equivalence is already proved
  independently of that input. This reduction is proved; the
  remaining input is not.

The current full build and audit pass: 45 modules, 50 Lean files, 8818 build
jobs, 82 principal checks, and 606 compiled project declarations. Every
compiled project declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. The audit's injected custom-axiom negative control is rejected.

## Exact remaining gap

For every finitely generated nilpotent group `G` and every `WordGeometry G`,
prove that there are natural numbers `C > 0` and `d` such that, for all `n`,

```text
(n+1)^d ≤ C * volume(n)    and    volume(n) ≤ C * (n+1)^d.
```

This is the matching-bounds consequence of Bass–Guivarc'h. It neither fixes
the exponent of a pre-existing upper bound nor assumes torsion-freeness.
Breuillard's stronger positive asymptotic ratio would also supply this
input, but its group-theoretic existence is not proved merely by the
numerical normalization already formalized here.

The proved upper-bound chain is:

1. `NilpotentConjugation.lean`: conjugation of a finite set in an upper-central
   term is polynomially bounded for every subadditive normal-subgroup length.
2. `WordSwaps.lean`: permutations of a length-`n` word require at most `n^2`
   adjacent swaps.
3. `WordCollection.lean`: bound the errors from those swaps, and count one
   representative for each multiset of letters using at most `(n+1)^|S|`
   multiplicity vectors.
4. `NilpotentGrowth.lean`: induct on the lower-central length, using Hill's
   proved finite generation of nilpotent subgroups. The resulting polynomial
   upper exponent is not asserted optimal.

The matching-volume argument needs sharper distortion bounds for the last
nontrivial lower-central subgroup `H`, of weight `k`: its ambient word
length must be comparable to the `k`th root of intrinsic word length.
Quotient/kernel counting and induction then give matching exponents. The
relevant discrete reference is Druţu–Kapovich's *Geometric Group Theory*,
September 2017 author draft, Section 14.1.3 (Lemmas 14.15–14.21) and Theorem
14.26, pp. 503–512. This part is still in progress.

Ordinary subgroup word length need not be comparable to ambient word length.
An unqualified central-extension product estimate would be invalid.

## Verification and attribution

Run `python3 scripts/check.py --record`. Branch-specific evidence is in
[verification/](verification/README.md). The branch uses Lean 4.33.0-rc2
and exact pinned mathlib and Gromov dependencies. Upstream source has not
been edited or copied into our own Apache-licensed files.

Mathematical and formalization sources are credited in
[REFERENCES.md](REFERENCES.md). Codex located and audited Hill's development
and developed the local adapters and additional proofs, as disclosed in
[ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md). These additions have kernel
verification but no new separate-agent or outside human review.
