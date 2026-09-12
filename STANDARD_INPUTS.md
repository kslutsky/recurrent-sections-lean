# Standard inputs and what is proved

This inventory describes **`research/polynomial-volume`**. The forward Gromov
theorem is proved using Aaron Hill's pinned Lean development. The Bernoulli
test action, common compact embedding, Borel projection, and finite-index
volume comparison are also proved. **The general nilpotent polynomial-volume
estimate remains unproved.** The requested complete volume formalization is
therefore still in progress.

## Complete remaining input

The strongest assembled characterization in
[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean) is
`maximalRecurrence_iff_virtuallyNilpotent_of_nilpotent_volume`. It has one
unproved mathematical input:

```lean
nilpotentVolume : NilpotentPolynomialVolumeTheorem
```

[NilpotentVolume.lean](RecurrentSections/NilpotentVolume.lean) defines this as:
for every nilpotent group `G` and every `W : WordGeometry G`, there exist
natural `C,d`, with `0 < C`, such that for every natural `n`,

```text
(n+1)^d ≤ C * W.volume n    and    W.volume n ≤ C * (n+1)^d.
```

Finite generation is included in `WordGeometry`. No torsion-free hypothesis
or pre-existing polynomial upper bound is imposed. This is the existence
part of the Bass–Guivarc'h polynomial-volume estimate; the explicit formula
for `d` is not requested by this interface. Sources and normalization are
recorded in the Lean module and [REFERENCES.md](REFERENCES.md).

This is an explicit hypothesis, not a custom axiom declaration. Its absence
from `#print axioms` does **not** mean it has been proved. No inhabitant of
this general proposition has been constructed. The full proof is not complete.

## Deductions now proved

[GromovTheorem.lean](RecurrentSections/GromovTheorem.lean) proves
`virtuallyNilpotent_of_polynomialGrowth W h`, with no unproved theorem argument.
It imports Hill's `GeneratesNS.main_gromov_theorem`, handles finite groups,
and converts `(n+1)^d` to Hill's positive-radius convention. The deep proof
is Hill's formalization of the Kleiner–Tao argument, not an original proof
by this repository. Its compiled axiom dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`.

[WordComparison.lean](RecurrentSections/WordComparison.lean) and
[VolumeBounds.lean](RecurrentSections/VolumeBounds.lean) prove comparison of
finite-index subgroup and ambient word volumes, without normality. Matching
polynomial bounds are invariant under finite index and changing generators.
Consequently the single nilpotent input supplies both the reverse Gromov
implication and `PolynomialVolumeTheorem W`. This is a proved reduction,
not a proof of the missing nilpotent estimate.

| Conclusion / direction | Unproved mathematical input |
|---|---|
| Polynomial growth ⇒ virtual nilpotence | None; Hill's proof is imported |
| Universal recurrence ⇒ polynomial growth or virtual nilpotence | None |
| Fixed free pmp action, every schedule ⇒ virtual nilpotence | None |
| Fixed free pmp action, one recurrent sequence ⇒ subexponential growth | None |
| Universal action-dependent recurrence ⇒ subexponential growth | None |
| Either full recurrence characterization | `nilpotentVolume` |
| Virtual nilpotence ⇒ polynomial growth or matching volume bounds | `nilpotentVolume` |
| Positive recurrence from word-volume doubling or matching bounds | None beyond the stated volume hypothesis |
| Finite-group volume bounds and recurrence | None |

## Modular interfaces retained

The older theorem
`maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems` still accepts
`gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G` and
`volume : PolynomialVolumeTheorem W`. The new theorem constructs both from
the one nilpotent input. These older parameters are not two additional
unproved inputs to the new characterization.

`PolynomialVolumeTheorem W` asks for matching bounds from a polynomial
upper bound. The common exponent need not equal the supplied upper exponent.
Breuillard (2014), Theorem 1.1, p. 670 gives stronger positive asymptotic
ratios. Normalization of such ratios is proved here; the asymptotic theorem
itself is not imported as a proved Lean result.

The constructors `standardBorelTools W` and `nonempty_freePmpModel G` need
no unproved theorem parameters. `PolynomialGeometry W` is constructed from
volume doubling or matching polynomial bounds. The earlier geometric and
Borel interfaces remain available for reuse.

Ordinary hypotheses (group structure, word geometry, standard Borel actions,
and radius schedules) are mathematical setting, not black boxes. Pinned
mathlib and Gromov results have proof terms; there are no project `axiom`
or `sorry` declarations. Verification records distinguish completed runs
from work in progress.

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

## Separate volume-formalization branch

This checkout is that research branch. See [VOLUME_RESEARCH.md](VOLUME_RESEARCH.md)
and [VolumeBounds.lean](RecurrentSections/VolumeBounds.lean) for the partial proofs.

`research/polynomial-volume` preserves `VolumeBounds.lean`: normalization
of positive asymptotic ratios, absorption of finitely many exceptional
radii, the finite-group volume theorem, and the resulting finite-group
recurrence corollary. The general group-theoretic estimate is not proved
there either. None of that partial proof module is present in or imported
by `main`. Both branches use the same explicit `PolynomialVolumeTheorem`
interface for the general characterization. The research branch now includes the completed Bernoulli proof from main.

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
is made. At the maintainer's request, the general volume theorem remains a black box
on `main`, and further formalization is separated onto the research branch.

The research branch also proves matching volume bounds for all finitely
generated abelian groups in
[AbelianVolume.lean](RecurrentSections/AbelianVolume.lean), using mathlib's
abelian structure theorem, exact cubical balls, and finite-index comparison.
This discharges the abelian base case, including torsion; the general
nilpotent estimate remains unproved.
