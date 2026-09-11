# Independent AI review of the external mathematical inputs

Source correspondence: the reviewed proof bodies are unchanged except for
six-line license headers in the standalone files. See
[source-correspondence.json](source-correspondence.json). Historical cache
filenames in this report identify inspected sources; the public URLs are
provided and the papers are not redistributed in this repository.

Date: September 10, 2026. Scope: the input interfaces in
`RecurrentSections/StandardInputs.lean` and
`RecurrentSections/Characterization.lean`, their mathematical interpretation,
and the source mapping in `STANDARD_INPUTS.md`. Paths and line numbers below
refer to the original `lean/` project reviewed before packaging.

This was a separate AI subagent review requested by the user. It is not a
human independent audit, a novelty certification, or a formal proof of the
external interfaces. I read the Lean declarations and surrounding definitions
directly and independently reconstructed why the inputs hold. I did not edit
proof files. Build verification is being performed separately by the main
agent.

## Finding

**No mathematical defect, hidden recurrence assumption, or circular input was
found.** Each external interface is true in its stated generality under the
finite word-geometry hypotheses, as explained below. The documentation correctly
says these interfaces remain hypotheses. In particular, a clean `#print axioms`
result does not establish those hypotheses, since they are theorem parameters.

There is no required proof correction. Two optional documentation improvements
are identified at the end.

## Interface-by-interface review

### `CompactChoice` — StandardInputs.lean:10–16, 72–73

The potentially delicate point is that `select` is one fixed function of the
compact set, rather than a fresh selector for each parameterized relation. The
stated interface is nevertheless valid.

A nonempty compact metric space is Polish. Its nonempty compact subsets form
a standard Borel hyperspace, and Kuratowski–Ryll-Nardzewski provides a Borel
selector on that hyperspace. Extend it arbitrarily to other subsets of the
space. Suppose a family `T x` has nonempty compact sections and a Borel graph.
For an open set `U`, the relation with sections `T x ∩ U` is Borel and has
sigma-compact sections: the intersection of a compact metric set with an open
set is a countable union of compact sets. Arsenin–Kunugui therefore makes its
projection Borel. These hitting tests show that `x ↦ T x` is Borel as a map to
the compact hyperspace. Composing with the fixed selector proves exactly the
`measurable` field, simultaneously for every standard Borel parameter space.

The structure itself does not assume nonemptiness of `K`; the field asserting
existence of `CompactChoice K` does. Thus no impossible selector on an empty
space is being assumed. Equality of selected values for equal compact sets is
ordinary extensionality of the fixed function. No orbit invariance or recurrence
conclusion is in this input.

Source correspondence: the named KRN and Arsenin–Kunugui theorems, as treated
in Kechris, *Classical Descriptive Set Theory*, Chapters 12 and 18, support this
standard composite statement. I did not access the subscription-only original
book text during this review; the proof above checks the standard theorem
hypotheses rather than claiming an original-page audit.

### `ScaledModels` / `PolynomialGeometry.models` — StandardInputs.lean:21–24, 39–42

The exact isometry requirement applies only to the finite ball `B(3 r_n)`.
Positive integer `r_n` ensures division by `r_n` is meaningful, and the
rescaled balls have diameter at most six. Two-sided polynomial volume estimates
give a uniform covering number at each positive rescaled radius. For small
integer radii the finitely many exceptions can be absorbed into the covering
bound. Thus the family is uniformly totally bounded with bounded diameter.

Gromov's 1981 paper, Section 6, explicitly proves a common compact embedding
statement for **every space in the family**, before extracting any convergent
subsequence. Consequently the use of one compact `K` and exact isometries for
the entire prescribed sequence is justified; passing to a subsequence is not
required. Each map can be extended off its finite ball by the image of the
identity. No continuity or compatibility across indices is imposed or needed.

Source checked directly: the cached published scan
`papers/gromov-polynomial-growth-1981.pdf`, Section 6, including the common
compact embedding construction. URL:
<https://www.numdam.org/item/PMIHES_1981__53__53_0.pdf>.

### `GroupPacking` / `PolynomialGeometry.packing` — StandardInputs.lean:28–31, 38

The separation condition itself forces injectivity of the indexed family;
the omission of a separate injectivity hypothesis is correct. Inversion
identifies the right word metric `length(h*g⁻¹)` with the left word metric
`length(g⁻¹*h)`, using symmetry of word length, and preserves identity balls.

For points in `B(7R)` separated by more than `R`, right-metric balls of radius
`floor(R/2)` are pairwise disjoint and contained in `B(8R)`. They all have the
same cardinality. The two-sided bounds `c(n+1)^d ≤ V(n) ≤ C(n+1)^d` give a
uniform bound on their number for `R ≥ 2`; radius one is a finite exception.
Increasing the resulting integer bound to at least one gives the exact field.
Finite groups are included, with exponent zero.

Source checked directly: Breuillard, *Geometry of locally compact groups of
polynomial growth and shape of large balls*, published 2014 PDF,
Theorem 1.1 on printed p. 670, gives the positive volume asymptotic constant
and integer growth degree. The bounds used here are its elementary discrete
counting-measure corollary. Cached source:
`papers/breuillard-polynomial-growth-2014-published.pdf`; URL:
<https://ems.press/content/serial-article-files/29707>.

### `BorelExtension` — StandardInputs.lean:54–57, 68–69

The graph joins distinct orbit points differing by an element of the finite
word ball. It is Borel, symmetric, and of bounded degree; stabilizers only
identify vertices or produce deleted loops. Each action map and its inverse
are measurable under `MeasurableConstSMul`, and standard Borelness makes their
graphs Borel. A prescribed Borel separated set is a Borel independent set.
The standard Borel maximal independent-set extension gives the stated Borel
superset. Maximality is equivalent to domination by the closed word ball,
including the identity. At radius zero, the whole space is a valid extension.
There is no freeness requirement, sequence, or recurrence conclusion.

Source correspondence checked through a primary-author exposition: the cached
Kechris–Marks survey (October 9, 2020), Proposition 4.9, explicitly attributes
extension of every Borel independent set to KST Proposition 4.2. Its Corollary
4.6 attributes countable Borel coloring for locally finite graphs to KST 4.5.
This supplies both hypotheses for the present graph. The original KST PDF
was not accessed; the Caltech record is metadata-only.

### `LocalMultiplicity` / `BorelColoring` — StandardInputs.lean:47–49, 60–63, 70–71

`LocalMultiplicity` quantifies over injective finite families and bounds the
number of points in `D ∩ B_R(y)` for each `y ∈ D`. Taking a finite family of
size `M+1` shows that this formulation gives exactly the required cardinality
bound. The center is counted, since the identity belongs to every word ball.
Thus the simple graph induced on `D` has degree at most `M−1`, not `M`.
The KST bounded-degree theorem gives `M` Borel colors. The equality between
`D` and their union also ensures each color class is a subset of `D`, even
though subset inclusion is not a separate field. Empty sets and `M=1` work;
the forbidden case `M=0` is excluded by the input.

Source correspondence checked in the same primary-author survey, Proposition
5.4, which expressly cites KST Proposition 4.6 and states the degree-`d` to
`d+1` Borel-coloring bound. I also read Le Maître–Slutsky, arXiv:2108.09009v3,
Lemma E.2, printed p. 122, which gives the related right-Haar packing and
coloring argument and directly cites KST 4.6. That lemma is antecedent
context, not an assumed recurrence theorem.

Sources:

- KST, *Borel chromatic numbers*, Adv. Math. 141 (1999), 1–44,
  <https://doi.org/10.1006/aima.1998.1771>.
- Kechris–Marks survey, cached manifest entry
  `priority-kechris-marks-survey`,
  <https://math.berkeley.edu/~marks/papers/combinatorics20book.pdf>.
- Le Maître–Slutsky v3,
  <https://arxiv.org/pdf/2108.09009v3>.
- Original-article access limitation checked at
  <https://authors.library.caltech.edu/records/mbe97-y1b24>.

### `finiteNearest` — StandardInputs.lean:74–77

A fixed nonempty finite family can be ordered. Choose the first point
minimizing distance to the argument. The fiber for each candidate is a finite
intersection of strict and non-strict comparisons of continuous distance
functions, so it is Borel. Fibers outside the finite family are empty. The
map `p : G → K` need not be measurable: only its finitely many fixed values
are used. The assumption of a map from the nonempty group also rules out an
empty target whenever the input is instantiated. No hidden invariance,
action, or recurrence is imposed. Second countability is more than this
elementary argument requires, not an invalid omission.

### `gromov` — Characterization.lean:69–73

The `WordGeometry` fields specify a finite symmetric generating set containing
the identity. Its powers are precisely closed integer word balls.
`PolynomialGrowth` is a natural-coefficient bound `V(n) ≤ C(n+1)^d`.
This is equivalent to the usual real-coefficient polynomial upper bound
after enlarging and rounding the coefficient and exponent. Radius zero
causes no issue. In mathlib's pinned `GroupTheory/Nilpotent.lean:201`,
`Group.IsVirtuallyNilpotent` means that a nilpotent subgroup has finite index,
exactly the intended definition.

The cached Gromov paper's introduction, printed p. 54, states the main
polynomial-growth implication and also explains the reverse implication via
polynomial growth of finitely generated nilpotent groups and finite extensions.
Thus the stated equivalence is correctly normalized. No recurrence input is
included in `gromov`.

### `FreePmpModel` / `test` — Characterization.lean:32–41, 44–45

The bundle describes a standard Borel action, an invariant probability
measure, and injectivity of every orbit map. This is everywhere freeness,
not merely essential freeness. The existence assumption is valid for every
countable group, and finite word geometry implies countability.

For the Bernoulli shift on `[0,1]^G`, the fixed-point condition for any
nonidentity group element forces equality of two distinct coordinates.
That event has atomless product measure zero. The complement of the countable
union of fixed-point sets is invariant, Borel, conull, and everywhere free.
Restrict the product measure and action to it. This works for finite groups
as well as infinite groups. For the trivial group, the whole product is free.
No ergodicity or non-atomicity of the resulting model is needed by the Lean
bundle, and no recurrence is assumed of it.

### Former `PositiveConstruction` input — Characterization.lean:75–88

The old assembly lemma still accepts `PositiveConstruction` as a parameter.
This is not a hidden input to the final theorem: `Sufficiency.lean:65–67`
proves it from `PolynomialGeometry` and `StandardBorelTools`, and the final
equivalence at `Sufficiency.lean:78–85` supplies that proof. The final theorem
therefore has the four documented external parameters, not a fifth recurrence
or positive-construction hypothesis.

## Documentation observations

1. **Optional, low severity:** the compact-selection explanation could add
   one sentence that compact metric spaces are Polish. This makes clear why
   no separate second-countability or completeness hypothesis occurs in
   `CompactChoice`.
2. **Optional, low severity:** the source-status paragraph can now record the
   separate AI review and the direct KST theorem-number corroboration in the
   Kechris–Marks survey, while still stating that the original KST text and
   Kechris book pages were not inspected in this review.

Neither observation requires changing a Lean statement. Source correspondence
is mathematical evidence for the explicit assumptions; it is not a replacement
for formalizing those assumptions. Publication priority and broader research
claims were outside this review.
