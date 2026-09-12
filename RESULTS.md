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

The positive direction includes arbitrary stabilizers. **All mathematical
inputs are proved.** The complete signatures include:

```text
maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems
  (W : WordGeometry G) :
  UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G

recurrence_iff_polynomialGrowth_of_standard_theorems
  (W : WordGeometry G) :
  UniversalRecurrence W ↔ PolynomialGrowth W.volume

freeRecurrence_iff_virtuallyNilpotent_of_standard_theorems
  (W : WordGeometry G) :
  UniversalFreeRecurrence W ↔ Group.IsVirtuallyNilpotent G
```

These declarations are in
[DerivedCharacterization.lean](RecurrentSections/DerivedCharacterization.lean).
The nonmaximal virtual-nilpotence and free polynomial-growth equivalents
are also provided. There is no `volume`, `gromov`, `test`, `geometry`, or
`tools` argument in these complete signatures.

The Gromov forward proof is imported from Aaron Hill's pinned development.
The converse and the nilpotent matching-volume estimate are proved locally;
finite-index comparison gives the required polynomial-volume theorem.
The Bernoulli test action, common compact embedding, and compact-section
Borel projection are proved. [STANDARD_INPUTS.md](STANDARD_INPUTS.md)
identifies all dependencies and retained modular interfaces.

The lower-level theorems in `Sufficiency.lean` and `Maximality.lean` still
accept geometric and Borel interfaces for reuse. The conditional theorem
ending in `_of_nilpotent_volume` also remains available; its argument now
has the proved inhabitant `nilpotentPolynomialVolumeTheorem`.

`universalRecurrence_of_volumeDoubling` additionally constructs recurrence
from the explicit bound `V(2*n+1) ≤ D*V(n)`, without a group structure theorem.

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
from universal recurrence to this statement using the proved Bernoulli
test action. `virtuallyNilpotent_of_recurrent` and
`virtuallyNilpotent_of_universalRecurrence` then give virtual nilpotence
with **no unproved mathematical theorem argument**. The Gromov step is
proved by the imported formalization, with explicit attribution.

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
schedule for each free Borel action and has no unformalized mathematical input.
The needed free pmp test action is constructed internally.

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
Borel projection, conull invariant measure restriction, and free atomless
Bernoulli actions of countable groups. These theorems have
no unformalized mathematical inputs; their graph-neighborhood and
weak-measurability hypotheses are stated explicitly. They do not require
the recurrent-section application. Geometry now includes checked
disjoint-ball counting, doubling bounds, finite nets, and uniform scaled
covering numbers and the common compact embedding theorem for arbitrary
uniformly coverable bounded families. See [STANDARD_INPUTS.md](STANDARD_INPUTS.md) for the
classical theorem dependencies and [TOOLS.md](TOOLS.md) for exact reusable APIs.

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

## 5. The full Gromov equivalence is proved

```text
polynomialGrowth_iff_virtuallyNilpotent (W : WordGeometry G) :
  PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G
```

This has no unproved mathematical argument. For the reverse implication,
`polynomialGrowth_of_nilpotent` proves a polynomial upper bound by discrete
collection and finite generation of nilpotent subgroups; finite-index
comparison gives `polynomialGrowth_of_virtuallyNilpotent`. The exponent
from this upper-bound argument need not be optimal, and this proof is separate from the sharper matching-volume proof below.

## 6. Matching polynomial volume

```text
polynomialVolumeTheorem (W : WordGeometry G) :
  PolynomialGrowth W.volume → TwoSidedPolynomialGrowth W.volume
```

Here `TwoSidedPolynomialGrowth` means that there are natural `C,d`, with
`C > 0`, such that for every natural `n`,

```text
(n+1)^d ≤ C * W.volume n    and    W.volume n ≤ C * (n+1)^d.
```

This theorem has no unproved mathematical argument. The common exponent
need not equal the exponent of the initial upper bound. The nilpotent
case is `twoSidedPolynomialGrowth_of_nilpotent`; it permits torsion and
arbitrary finite word metrics. The exact Bass–Guivarc'h rank formula and
Breuillard's positive asymptotic volume limit are not formalized.

The proof uses both sharp distortion bounds for the last lower-central
term, its abelian matching volume, quotient/kernel counting, and induction.
[VOLUME_RESEARCH.md](VOLUME_RESEARCH.md) gives the module-level argument.
