# Standard inputs to the formal characterization

This file records the standard mathematical results left as explicit
hypotheses in the formalization, and their correspondence with prior work. The structures are in
[StandardInputs.lean](RecurrentSections/StandardInputs.lean); the two
converse inputs are in
[Characterization.lean](RecurrentSections/Characterization.lean).

The final theorem has four explicit mathematical parameters:

| Parameter | Content | Used for |
|---|---|---|
| `gromov` | Polynomial growth of the specified word balls is equivalent to `Group.IsVirtuallyNilpotent G` | Passing between the two group properties |
| `test` | Existence of a free pmp standard Borel action | Universal recurrence implies polynomial growth |
| `geometry` | Uniform group packing and common compact models for rescaled word balls | Positive construction |
| `tools` | Borel extension, bounded-degree coloring, compact selection, finite nearest-point selection | Positive construction and maximality |

These are hypotheses, not custom Lean axiom declarations. Consequently
`#print axioms` does not list them. The [audit](verification/audit-output.txt) also
prints theorem types and the complete geometric and Borel input structures.
The arguments below explain why the interfaces are standard consequences
of the cited results; they are **not additional Lean proofs**.

The single-sequence implication does not use these
geometric or Borel-tool interfaces, or Gromov. Its growth and summability
arguments are proved using mathlib's existing
[Fekete lemma](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Analysis/Subadditive.lean)
and [first Borel–Cantelli lemma](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean).
These are kernel-checked library theorems, not new external assumptions.
The universal existential-radius corollary uses only `test`.

## Polynomial growth and the free test action

The parameter `gromov` identifies `PolynomialGrowth W.volume` with
mathlib's finite-index-nilpotent-subgroup definition. The forward
implication is Gromov's theorem; the reverse is the classical polynomial
growth of finitely generated virtually nilpotent groups. This is the
equivalence taken as an explicit standard input. See M. Gromov, *Groups of
polynomial growth and expanding maps*, Publ. Math. IHÉS **53** (1981),
53–78, [published scan](https://www.numdam.org/item/PMIHES_1981__53__53_0.pdf).

For `test`, take the Bernoulli shift on `[0,1]^G` and restrict to its
invariant conull free part. If `g ≠ 1` fixes a point, two distinct
coordinates agree, an event of probability zero for the atomless product
measure. Countability makes the free part conull and Borel. The product
measure is invariant. This elementary construction is assumed as a
bundled existence statement; no recurrence is assumed of the action.
Countability from the finite word geometry itself is proved in
`RecurrenceSelection.lean`.

## The geometric interface

`PolynomialGeometry` contains two conclusions under polynomial growth.

**Packing.** There is a positive integer `M` such that every finite family
in `B(7R)` with pairwise right-word distance greater than `R` has
cardinality at most `M`, uniformly for integer `R > 0`. Right-word
distance is `length (h * g⁻¹)`. Inversion identifies this metric
isometrically with the left-word metric and preserves balls about the
identity, so either convention gives the same bound.

Breuillard's volume asymptotics give constants `c,C > 0` and an integer
`d` with `c*(n+1)^d ≤ V(n) ≤ C*(n+1)^d` for every integer `n ≥ 0`,
after adjusting constants at finitely many radii. For `R ≥ 2`, disjoint
balls of radius `floor(R/2)` about the packed points fit in `B(8R)`.
The ratio `V(8R)/V(floor(R/2))` is uniformly bounded. Radius one is a
finite exception bounded by `V(7)`. This proves the precise packing
input. See E. Breuillard, *Geometry of locally compact groups of polynomial
growth and shape of large balls*, Groups Geom. Dyn. **8** (2014),
669–732, Theorem 1.1,
[published PDF](https://ems.press/content/serial-article-files/29707).

**Compact models.** For every increasing positive integer sequence `r`,
there is a compact metric space `K` and maps `φ n : G → K` satisfying

```text
dist (φ n g) (φ n h) * r n = length (g⁻¹ * h)
    whenever g,h ∈ B(3*r n).
```

The rescaled balls have diameter at most six. The same volume bounds
give uniform covering numbers at every positive rescaled radius. Thus
they form a uniformly totally bounded family. Gromov's common compact
embedding theorem puts all of them isometrically in one compact space;
see §6 of the [1981 paper](https://www.numdam.org/item/PMIHES_1981__53__53_0.pdf).
Extend each map arbitrarily outside its finite ball. No compatibility
between different `n`, origin convergence, or action is included
in this assumption.

These two standard geometric corollaries are left outside Lean together
with the published results from which they follow. In contrast, the
application of packing to recentered sets in a possibly nonfree action
is fully proved in `recentered_multiplicity`.

## Borel extension and coloring

For a Borel action of a countable group, join distinct `x,y` when
`y = g • x` for some `g ∈ B(R)`. This is a locally finite Borel graph.

`BorelExtension` asserts that any Borel independent set extends to a
Borel independent set meeting every closed graph neighborhood. Apply
the standard Borel maximal independent-set theorem to the induced graph
outside the original set and its neighbors, then adjoin the original
set. This is an ordinary maximal extension at one radius. It contains
no condition involving a sequence or recurrence.

`BorelColoring` asserts that a Borel set `D` whose intersections with
closed radius-`R` orbit balls centered at points of `D` have cardinality
at most `M` is a union of
`M` Borel separated sets. The corresponding graph on `D` has degree at
most `M-1`, since multiplicity counts the center. Apply the standard
bounded-degree Borel coloring theorem. See A. S. Kechris, S. Solecki, and
S. Todorcevic, *Borel chromatic numbers*, Adv. Math. **141** (1999),
1–44, [DOI](https://doi.org/10.1006/aima.1998.1771).

The related packing-and-coloring lemma for general locally compact
actions is explicitly recorded in F. Le Maître and K. Slutsky,
*L¹ full groups of flows*, Lemma E.2,
[arXiv v3](https://arxiv.org/pdf/2108.09009v3). That lemma is an antecedent
of the mechanism, not an assumed recurrence theorem.

## Compact and finite selection

`CompactChoice K` supplies one fixed function on subsets of a nonempty
compact metric space `K`, selecting a member of every nonempty compact
set. For any standard Borel parameter space `X` and Borel relation with
nonempty compact sections `T x`, the map `x ↦ select (T x)` is Borel.
Equal sets have equal selections; invariance of the particular return
clusters must still be proved.

A compact metric space is Polish, so the standard hyperspace and selection
theorems apply without an additional hypothesis on `K`.

Use a Borel selector on the hyperspace of nonempty compact subsets, as
supplied by Kuratowski–Ryll-Nardzewski. A Borel compact-section relation
defines a Borel hyperspace map: for an open set `U`, the set of parameters
whose section meets `U` is Borel by Arsenin–Kunugui, since a compact set
intersected with an open set is sigma-compact. Compose with the fixed
selector. The standard selection and uniformization results are covered
in A. S. Kechris, *Classical Descriptive Set Theory*, GTM **156**, Springer,
1995, Chapters 12 and 18,
[book](https://link.springer.com/book/10.1007/978-1-4612-4190-4).

`finiteNearest` asserts Borel nearest-point selection from a fixed
nonempty finite family in a metric space. Order the family, minimize
distance, and choose the first minimizer. Each equality fiber is given
by finitely many strict or weak comparisons of continuous distance
functions, hence is Borel. This elementary finite-minimization fact is
also left as an input; it assumes no orbit invariance.

The formal proof establishes Borelness and nonemptiness of return
clusters, their equality throughout each orbit, invariance of the
resulting displacements, recurrence after recentering, and invariant
choice among recurrent colors. None of those construction steps is
hidden in the selection interfaces.

## Source and verification status

Gromov §6, Breuillard Theorem 1.1, and Le Maître–Slutsky v3 Lemma E.2
were inspected during preparation. Bibliographic details appear in
[REFERENCES.md](REFERENCES.md). The KST theorem interfaces and named
classical selection results are taken as standard inputs. The separate
[input review](reviews/standard-inputs.md) corroborated the maximal-extension
and coloring formulations in the
[Kechris–Marks survey](https://math.berkeley.edu/~marks/papers/combinatorics20book.pdf),
Propositions 4.9 and 5.4, which attribute them to KST. Direct inspection
of the original KST article or the subscription-only Kechris book pages
is not claimed. The proof in Lean is conditional on the exact interfaces
above. Source correspondence, publication priority, and the intended
meaning of the definitions remain subjects for mathematical review.
