# Standard inputs and what is proved

Two of the three inputs targeted in the latest formalization are now fully
proved: **common compact embedding** and **compact-section Borel projection**.
The general **two-sided polynomial volume theorem is retained as a black box**
on `main`. Partial normalization lemmas and the finite-group case are kept
on the separate local `research/polynomial-volume` branch.

The constructors now have these signatures:

```text
polynomialGeometry_of_standard_theorems W volume : PolynomialGeometry W
standardBorelTools W : StandardBorelTools W
```

In particular, `StandardBorelTools` is constructed without an external
mathematical theorem parameter. The application also has a fully proved
positive theorem directly from volume doubling:

```text
universalRecurrence_of_volumeDoubling W hD : UniversalRecurrence W
```

Here `hD` states `V(2*n + 1) ≤ D * V(n)` for every natural `n`.
The word geometry still specifies a finite symmetric generating set.

## Inputs still present in the characterization

[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean)
now takes just these three named inputs for the virtual-nilpotence equivalence:

| Parameter | Exact remaining mathematical input |
|---|---|
| `gromov` | Polynomial growth of the specified word balls is equivalent to virtual nilpotence. |
| `test` | A free probability-preserving standard Borel action exists. |
| `volume : PolynomialVolumeTheorem W` | A polynomial upper bound implies matching upper and lower bounds with one common integer exponent. |

The polynomial-growth characterization omits `gromov`. The fixed-action
polynomial and subexponential obstructions need none of these inputs.
The older theorems accepting bundled interfaces remain available.

All remaining inputs are explicit hypotheses, not custom axiom declarations.
Their absence from `#print axioms` does not mean they have been proved.
The audit prints their definitions and the final theorem types.

## Complete black-box inventory

For the final theorem
`maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems`, the following
are the **only unproved mathematical inputs**. Let `V(n) = |B_W(n)|`.

1. **Polynomial growth and virtual nilpotence (`gromov`).**
   The exact parameter is
   `PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G`.
   Here polynomial growth means that there exist natural `C,d` with
   `V(n) ≤ C*(n+1)^d` for every natural `n`. Virtual nilpotence means
   existence of a nilpotent subgroup of finite index, using mathlib's
   definition. The polynomial-growth-to-nilpotence implication is Gromov's
   theorem; the reverse direction is the classical nilpotent growth result
   and finite-index comparison. This parameter supplies both directions.
2. **Existence of a free probability-preserving test action (`test`).**
   The exact parameter is `Nonempty (FreePmpModel G)`. It supplies a
   standard Borel space, a group action with measurable translations,
   an invariant probability measure, and injectivity of every orbit map
   `g ↦ g • x`. Freeness is everywhere, not just almost everywhere.
   No ergodicity, recurrence, or additional geometric property is assumed.
   The standard construction is the Bernoulli shift on `[0,1]^G` restricted
   to its invariant conull Borel free part. For each nonidentity element,
   its fixed-point set forces two distinct atomless coordinates to agree
   and has measure zero. Countability of `G` follows from `WordGeometry`
   by the proved `WordGeometry.countable`. This construction itself is
   not formalized here.
3. **Matching polynomial word-volume bounds (`volume`).**
   The exact parameter `PolynomialVolumeTheorem W` unfolds to
   `PolynomialGrowth W.volume → TwoSidedPolynomialGrowth W.volume`.
   Its conclusion is that some positive natural `C` and natural `d` satisfy
   for every natural `n`:

   ```text
   (n+1)^d ≤ C*V(n)    and    V(n) ≤ C*(n+1)^d.
   ```

   The two bounds share an exponent; it need not equal the exponent in
   the supplied polynomial upper bound. Radius zero and finite groups
   are included. This is a weaker consequence of Breuillard's Theorem 1.1,
   whose positive polynomial asymptotic ratio implies these bounds.
   It is distinct from the growth/nilpotence equivalence in item 1.
   All deductions from these bounds to doubling, packing and compact
   models are proved on `main`; the theorem yielding the bounds remains
   an explicit hypothesis.

The classical sources and their roles are listed in
[REFERENCES.md](REFERENCES.md). The Bernoulli construction is also detailed
in the historical [input review](reviews/standard-inputs.md).

| Conclusion / direction | Unproved inputs actually needed |
|---|---|
| Universal recurrence ⇒ polynomial growth | `test` |
| Universal recurrence ⇒ virtual nilpotence | `test`, growth ⇒ nilpotence direction of `gromov` |
| Polynomial growth ⇒ universal maximal recurrence | `volume` |
| Virtual nilpotence ⇒ universal maximal recurrence | `volume`, nilpotence ⇒ growth direction of `gromov` |
| Full polynomial-growth equivalence | `test`, `volume` |
| Full virtual-nilpotence equivalence | `test`, `volume`, `gromov` |
| Fixed free pmp action, all schedules ⇒ polynomial growth | None |
| Fixed free pmp action, one recurrent sequence ⇒ subexponential growth | None |
| Positive recurrence from word-volume doubling | None beyond the stated doubling hypothesis |

These are explicit theorem parameters, not Lean `axiom` declarations.
`PolynomialGeometry`, `StandardBorelTools`, and `PositiveConstruction`
are intermediate interfaces with proved constructors, not additional
black boxes in the final theorem. Earlier modular theorems still expose
those interfaces for reuse.

Ordinary hypotheses specify the mathematical setting: a group, finite
symmetric generators containing the identity and exhausting the group,
standard Borel actions, and positive strictly increasing integer schedules.
They are not further published-theorem assumptions. Classical decidable
equality is used for finite word balls. The logical foundation uses only
`propext`, `Classical.choice`, and `Quot.sound`, as certified by the full
axiom audit. Results imported from pinned mathlib have checked proofs;
there are no custom mathematical axioms or admitted proofs.

## Separate volume-formalization branch

`research/polynomial-volume` preserves `VolumeBounds.lean`: normalization
of positive asymptotic ratios, absorption of finitely many exceptional
radii, the finite-group volume theorem, and the resulting finite-group
recurrence corollary. The general group-theoretic estimate is not proved
there either. None of that partial proof module is present in or imported
by `main`. Both branches use the same explicit `PolynomialVolumeTheorem`
interface for the general characterization.

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
