# Main results and formal scope

Use the definitions in [PROBLEM.md](PROBLEM.md). Throughout, $G$ is
finitely generated, $W$ specifies a finite symmetric generating set
containing the identity, and radius schedules are integer-valued.

## 1. Prescribed-radius characterization

The mathematical statement is:
$$
\begin{aligned}
G\text{ is virtually nilpotent}\quad\Longleftrightarrow\quad&
\text{every Borel action }G\curvearrowright X\\
&\text{has recurrent maximal }r_n\text{-separated Borel sections}\\
&\text{for every increasing positive integer }(r_n).
\end{aligned}
$$

The positive direction includes arbitrary stabilizers. The formal
equivalence is **conditional on explicitly supplied standard results**:

| Input | What remains unproved here |
|---|---|
| `gromov` | Polynomial word-volume growth is equivalent to `Group.IsVirtuallyNilpotent G`. |
| `test` | A free probability-preserving standard Borel action exists. |
| `volume : PolynomialVolumeTheorem W` | Polynomial growth gives matching upper and lower bounds with one common integer exponent. |

[STANDARD_INPUTS.md](STANDARD_INPUTS.md) gives the exact formulations.
None assumes recurrence, invariant return clusters, recentering, or
selection of a recurrent color. Those construction steps are proved.

The new theorem in
[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean)
has the following signature, with group instances suppressed:

```text
maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems
  (W : WordGeometry G)
  (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
  (test : Nonempty (FreePmpModel G))
  (volume : PolynomialVolumeTheorem W) :
  UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G
```

`PolynomialGeometry W` is constructed using only `volume`.
`StandardBorelTools W` is constructed without an external theorem parameter.
Common compact embedding and compact-section projection are fully proved;
the general group-volume theorem remains unproved.
The earlier theorem accepting the two interfaces remains available in
[Maximality.lean](RecurrentSections/Maximality.lean).

[Sufficiency.lean](RecurrentSections/Sufficiency.lean) also proves
`universalRecurrence_of_polynomialGrowth`,
`universalRecurrence_of_virtuallyNilpotent`,
`recurrence_iff_polynomialGrowth`, and
`recurrence_iff_virtuallyNilpotent`. The nonmaximal polynomial-growth
equivalence needs `test`, `geometry`, and `tools`, but no `gromov`.
The predicate `PositiveConstruction` is proved from the interfaces and
is not a further premise of the final equivalences.

`recurrence_iff_polynomialGrowth_of_standard_theorems` exposes the same
remaining inputs and omits `gromov`.

`universalRecurrence_of_volumeDoubling` proves the positive construction
from the explicit bound `V(2*n + 1) ≤ D*V(n)`, without an external theorem
parameter. The partial polynomial-volume proofs and their finite-group
corollary are maintained separately on `research/polynomial-volume`.
On this research branch, `universalRecurrence_of_finite` is proved without
any external theorem input; see [VOLUME_RESEARCH.md](VOLUME_RESEARCH.md).

## 2. All prescribed schedules in one free pmp action

**Theorem.** Suppose $G$ acts freely and preserves a probability measure,
with measurable group translations. If for every increasing positive
integer schedule $(r_n)$ there are measurable $r_n$-separated sets
$C_n$ satisfying everywhere recurrence, then $G$ has polynomial growth.

Completeness, maximality, and standard Borelness are unnecessary for this
fixed-action assertion. It has **no unformalized mathematical inputs**.

The theorem `polynomialGrowth_of_recurrent_with_lowerBounds` in
[Converse.lean](RecurrentSections/Converse.lean) permits any fixed
$q:\mathbb N\times\mathbb N\to\mathbb N$, restricting the recurrence
hypothesis to schedules with
$$
r_0\ge q(0,0),\qquad r_{n+1}\ge q(n+1,r_n).
$$
Thus arbitrarily rapid prescribed growth is covered.
The simpler `polynomialGrowth_of_recurrent` wrapper uses complete
sections for consistency with the universal definitions.

[Characterization.lean](RecurrentSections/Characterization.lean) passes
from universal recurrence to this statement using `test`, and then to
virtual nilpotence using `gromov`.

The proof chooses large volume ratios and bounds the total measure of
suitable section neighborhoods by $1/2$. Recurrence would make these
neighborhoods cover a probability space.

## 3. One recurrent sequence

**Theorem.** Suppose one free probability-preserving action, with measurable
group translations, has measurable
$r_n$-separated sets $C_n$, for one strictly increasing integer sequence,
satisfying
$$
\forall x\ \forall\varepsilon>0\ \forall N\
\exists n\ge N:\quad d(x,C_n)<\varepsilon r_n.
$$
Then
$$
\lim_{n\to\infty}\frac{\log V(n)}n=0.
$$

This is `subexponentialGrowth_of_one_recurrent_sequence` in
[SingleSequence.lean](RecurrentSections/SingleSequence.lean).
Completeness, maximality, standard Borelness, and positivity of the
initial radius are unnecessary. Freeness and an invariant probability
measure remain hypotheses.

There are **no unformalized mathematical inputs**. Growth calculations,
rounding, and measure estimates are proved locally; Fekete and the first
Borel–Cantelli lemma are already proved in mathlib.

The wrapper `subexponentialGrowth_of_some_recurrent_sections` uses
`HasSomeRecurrentSections`, with positive radii and complete sections.
The universal corollary
`subexponentialGrowth_of_universalFreeSomeRecurrence` allows a different
schedule for each free Borel action and uses only `test` as an external input.

For positive entropy $h$, a suitable positive tolerance gives
$$
\mu(B(\lfloor\varepsilon r_n\rfloor)C_n)
\le e^h e^{-hr_n/4}.
$$
Since $r_n\ge n$, this is summable, contradicting recurrence.

## 4. Reusable lemmas and verification

The new [BorelToolkit](TOOLS.md) proves measurable independent covers,
seeded maximal extension, finite coloring, finite minimization, and
Kuratowski--Ryll-Nardzewski closed-set selection, Novikov countable
separation, the Kunugui--Novikov rectangle decomposition, and compact-section
Borel projection. These theorems have
no unformalized mathematical inputs; their graph-neighborhood and
weak-measurability hypotheses are stated explicitly. They do not require
the recurrent-section application. Geometry now includes checked
disjoint-ball counting, doubling bounds, finite nets, and uniform scaled
covering numbers and the common compact embedding theorem for arbitrary
uniformly coverable bounded families. See [STANDARD_INPUTS.md](STANDARD_INPUTS.md) for the
remaining deep theorems and [TOOLS.md](TOOLS.md) for exact reusable APIs.

The measure and volume-ratio rows concern measurable separated sets in
a free probability-preserving action with measurable translations.

| Assertion | Lean declaration |
|---|---|
| A tail bound $v(5m)\le K v(m)$ for a monotone integer-valued function implies polynomial growth | `polynomialGrowth_of_dilation_bound` |
| $\mu(B(a)C)\le V(a)/V(b)$ when $C$ is $R$-separated and $2b\le R$ | `measure_neighborhood_le_of_separated` |
| Summable small-neighborhood volume ratios exclude recurrence | `not_recurrent_of_summable_ratios` |
| Word-volume logarithms have a nonnegative Fekete limit | `WordGeometry.tendsto_growthEntropy` |
| For the scaled word-ball models and increasing integer radii, return clusters are invariant on every orbit | `returnCluster_smul` |
| Uniform group packing bounds the local multiplicity after invariant, bounded recentering of separated sets, including with stabilizers | `recentered_multiplicity` |
| A recurrent finite union of Borel separated sequences can be assembled into one, using `StandardBorelTools` at a strictly increasing integer schedule | `finite_color_assembly` |

The general summability lemmas assume convergence of their displayed
series, without requiring increasing schedules.

`Audit.lean` prints principal signatures, definitions, and axiom
dependencies. `AllAxioms.lean` checks the compiled kernel dependencies
of every declaration in the three library namespaces, including private
declarations from their modules. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed.

Explicit mathematical hypotheses do **not** appear as custom axioms in
those lists. The standard-input table is therefore essential to the
meaning of the characterization. See [verification/](verification/README.md)
for evidence and [reviews/](reviews/README.md) for the separate AI reviews.
