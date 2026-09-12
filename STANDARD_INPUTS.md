# Standard results and dependency inventory

This inventory describes **`research/polynomial-volume`**. The complete
main characterizations have **no unproved mathematical theorem inputs**.
Gromov's theorem, matching polynomial volume, the Bernoulli test action,
common compact embedding, and compact-section Borel projection all have
Lean proof terms. Main remains at its earlier black-box interface.

## Complete main statements

The theorems ending in `_of_standard_theorems` in
[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean)
require only `W : WordGeometry G` and the ordinary group instances. They
prove equivalence of polynomial growth, virtual nilpotence, and recurrent
sections for all prescribed increasing positive integer schedules in all
Borel actions. Arbitrary stabilizers are allowed. Restricting the universal
quantification to free actions gives an equivalent property.

| Mathematical ingredient | Formal proof |
|---|---|
| Polynomial growth ⇒ virtual nilpotence (Gromov) | Aaron Hill's pinned development, adapted in `GromovTheorem.lean` |
| Virtual nilpotence ⇒ polynomial growth (Wolf) | `NilpotentGrowth.lean`, using local collection and Hill's proved finite generation of nilpotent subgroups |
| Matching nilpotent polynomial-volume bounds (Bass–Guivarc'h consequence) | `NilpotentMatchingVolume.lean`, using both last-term distortion estimates, abelian volume, and quotient/kernel counting |
| Polynomial growth ⇒ matching polynomial volume | `polynomialVolumeTheorem` in `NilpotentVolume.lean`, using Gromov and finite-index comparison |
| Free pmp test action of every countable group | `FreePmpModel.lean` and `BorelToolkit.Bernoulli` |
| Packing and scaled compact models from matching volume | `PolynomialGeometry.lean` and `MetricGeometry.CommonEmbedding` |
| Borel extension, coloring, minimization, and selection | `BorelToolkit` and the action adapter `BorelTools.lean` |
| Fixed free pmp action, all prescribed schedules ⇒ polynomial growth | `Converse.lean` |
| Fixed free pmp action, one recurrent sequence ⇒ subexponential growth | `SingleSequence.lean` |

The imported results in mathlib and Hill's development have proof terms;
they are not axioms or assumed propositions. The recursive audit checks
the logical dependencies of the local declarations through those imports.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. There are
no project `axiom`, `sorry`, or proof-shortcut declarations.

## Scope of the volume result

`PolynomialVolumeTheorem W` is the implication

```text
PolynomialGrowth W.volume →
  ∃ C d : ℕ, 0 < C ∧ ∀ n,
    (n+1)^d ≤ C * W.volume n ∧ W.volume n ≤ C * (n+1)^d.
```

Its proved inhabitant is `polynomialVolumeTheorem W`.
`NilpotentPolynomialVolumeTheorem` is the corresponding statement for
every nilpotent group and every explicit word geometry. Its proved
inhabitant is `nilpotentPolynomialVolumeTheorem`.

Finite generation is included in `WordGeometry`. Torsion and finite groups
are allowed. The common exponent is existential and need not equal the
exponent supplied by the initial upper bound. The explicit Bass–Guivarc'h
rank formula and Breuillard's positive asymptotic volume limit are outside
the formal scope. They are neither proved nor assumed by the main results.
[REFERENCES.md](REFERENCES.md) gives the classical sources and the inspected
discrete proof in Druţu–Kapovich.

## Retained modular interfaces

Lower-level statements in `Sufficiency.lean` and `Maximality.lean` accept
`PolynomialGeometry W` and `StandardBorelTools W`. The constructors for
these interfaces are proved. Conditional assembly lemmas ending in
`_of_nilpotent_volume` remain available as well. Their explicit input is
now inhabited; the complete main statements do not request it.

The names `PolynomialVolumeTheorem`, `NilpotentPolynomialVolumeTheorem`,
`CommonCompactEmbeddingTheorem`, and `CompactSectionProjectionTheorem`
are propositions used as interfaces. Naming a proposition alone would not
prove it, and its appearance as an ordinary hypothesis would not be detected
by an axiom list. Here each interface also has an explicit proved inhabitant,
and the final theorem signatures omit them. Both facts are checked in
`Audit.lean`.

Ordinary assumptions about group structure, generating sets, actions,
measurability, freeness, invariant probability measures, or schedules remain
part of the mathematical setting. The one-sequence implication retains
its free pmp hypothesis; it is not an assertion about arbitrary actions.

## The Bernoulli test action is proved

[FreePmpModel.lean](RecurrentSections/FreePmpModel.lean) proves
`nonempty_freePmpModel G` for **every countable group**, including finite
and trivial groups. It requires no word geometry or external theorem input.
All group-level characterization and subexponential-growth theorems now
construct this model internally; their former `test` parameter is removed.

The reusable [Bernoulli.lean](BorelToolkit/Bernoulli.lean) proves the more
general construction with any atomless probability measure on a standard
Borel base. The action is `(g • x)(h) = x(g⁻¹*h)` on `Y^G`. Its free part
consists exactly of configurations with injective orbit maps. This set
is Borel by countably many measurable equality tests and is invariant by
the action law. Pairwise coordinate independence and the zero measure of
the diagonal show that almost every labeling is injective, hence belongs
to the free part. The restriction is therefore **everywhere free**, standard
Borel, and probability preserving.

`infinitePi_ae_ne` and `infinitePi_ae_injective` need only a measurable
diagonal, atomlessness and a probability measure; the latter needs a
countable index set. The separate
[MeasureRestriction.lean](BorelToolkit/MeasureRestriction.lean) proves that
a measure-preserving map restricts to a measurable conull forward-invariant
set, with no invertibility or probability assumption. These tools import
no recurrence application module. The model uses the unit interval with
Lebesgue probability measure from mathlib.

## Geometry: common compact embedding is proved

[CommonEmbedding.lean](MetricGeometry/CommonEmbedding.lean) proves
`commonCompactEmbeddingTheorem`, an inhabitant of the formerly external
proposition. Its stronger theorem `exists_common_compact_embedding` permits
an **arbitrary indexed family** of nonempty metric spaces with uniformly
bounded diameters and uniform finite covering numbers. Individual spaces
need not be complete or compact. Every member embeds isometrically into
one compact metric space; there is no restriction to a subsequence.

The proof coordinates finite nets by one finitely branching tree. Parent–child
distances have a common summable bound, and every level still covers each
space at its designated radius. Distances to the resulting dense coordinate
set give exact isometries into a space of bounded functions. Finite
truncations uniformly approximate all coordinates, yielding total boundedness
of the union of all images. Its closure is compact.

[PolynomialGeometry.lean](RecurrentSections/PolynomialGeometry.lean) proves
all deductions from volume doubling: disjoint-ball counting, packing,
finite nets, rescaled word-ball covering numbers, and common compact models.
For reference, matching volume bounds give doubling with `D = C*C*2^d`;
the packing constant used in the construction is `D^5`. Scaled models need
only positive radii, not monotonicity.

## Borel tools: compact projection is proved

The independent [BorelToolkit](TOOLS.md) imports no recurrence module.
The new proof chain is:

1. `AnalyticSeparation.lean`: Novikov's countable separation theorem.
   Countably many analytic sets with empty intersection have measurable
   supersets with empty intersection. Its target is any Hausdorff space
   whose opens are measurable.
2. `OpenSections.lean`: the Kunugui–Novikov decomposition of a Borel
   relation with open sections as a countable union of Borel–open rectangles.
3. `CompactProjectionProof.lean`: projection for closed sections in a
   compact Polish target, using finite subcovers; general compact sections
   follow by a Hilbert-cube embedding and Lusin–Souslin.
4. `CompactProjection.lean`: the exact `compactSectionProjectionTheorem`,
   weak measurability of compact-section Borel graphs, and fixed selection.

The projection theorem allows empty sections and arbitrary standard Borel
parameter spaces. It requires a complete separable metric target with its
Borel structure. No weak measurability or selector is assumed in proving
projection, so the subsequent selector application is not circular.

The earlier graph, finite-minimization, and Kuratowski–Ryll-Nardzewski
selection proofs remain in place. General graph lemmas explicitly assume
that neighborhoods of measurable sets are measurable; the finite-action
adapter proves this property directly. This does not formalize the general
Lusin–Novikov theorem or Kechris's lcsc orbit-cross-section existence theorem.

## Attribution and review status

[REFERENCES.md](REFERENCES.md) identifies the classical theorems, the
inspected proofs, and the mathlib constructions adapted here. The additions
were developed with Codex and checked by Lean and the dependency audits.
The earlier three AI reviews cover the initial snapshot only; no new
separate-agent review, outside human review, or first-formalization claim
is made. At the maintainer's request, `main` retains its earlier black-box
interface; the completed group-volume formalization is on the research branch.
