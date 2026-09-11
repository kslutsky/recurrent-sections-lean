# Independent AI review: local proof mechanisms

Source correspondence: this report refers to the reviewed proof bodies before
extraction. The standalone files add a six-line licensing header, so source
line numbers below are six less than in the packaged files. Proof bodies are
identical, as recorded in [source-correspondence.json](source-correspondence.json).

Date: September 10, 2026.
Reviewer: a separate OpenAI Codex subagent, assigned to read the proof code independently of the repository-packaging agent. This is an independent AI-assisted pass, not outside human peer review or a novelty certificate.

## Scope and outcome

I read all fifteen `RecurrentSections/*.lean` files, the root import, `Audit.lean`, the existing audit output, `README.md`, and `STANDARD_INPUTS.md`. I also inspected the pinned mathlib definitions of `Group.IsVirtuallyNilpotent`, `StandardBorelSpace`, and the precise Fekete limit. I did not modify proof sources.

**No confirmed mathematical or statement-level error was found in the inspected code.** The main characterization is a conditional Lean theorem with the documented geometric and descriptive-set-theoretic inputs. The fixed-free-pmp-action growth obstructions have no analogous external mathematical theorem parameters. This review does not turn those external inputs into Lean proofs.

## Definitions and scope

`WordGeometry` really supplies a finite symmetric generating set containing the identity. Its finite powers are closed word balls, including radius zero. `length` is the least membership radius. `Separated` means distinct section points have distance **strictly greater** than the specified integer radius, including when stabilizers are present. `Recurrent` quantifies over every real positive tolerance, every point, and every tail of the sequence. Thus it asserts everywhere infinite recurrence, not almost-everywhere recurrence or a weaker varying-tolerance property.

`HasRecurrentSections` quantifies over every strictly increasing positive integer schedule. `HasSomeRecurrentSections` quantifies existentially over a schedule that can depend on the action. The distinction is present in both code and documentation. The maximal version quantifies over all separated supersets, not merely Borel supersets. `UniversalRecurrence` includes nonfree actions. For a countable group, measurable translations and their inverses give the expected Borel action.

Mathlib defines virtual nilpotence as existence of a nilpotent subgroup of finite index. There is no additional torsion-free, normal-subgroup, or infinite-group restriction hidden in that definition.

## Prescribed recurrence implies polynomial growth

The proof in `Growth.lean` establishes the dilation lemma for arbitrary monotone natural-valued functions. Its contrapositive genuinely gives unbounded dilation ratios on every tail. The recursive adverse schedule is strictly increasing, positive, and meets the stated stage/previous-radius lower bounds.

In `Packing.lean`, freeness is used precisely to make distinct translates of a separated set disjoint. The inverse and multiplication order is correct: intersecting translates yield a displacement of length at most twice the packing radius. Probability preservation is used to bound the sum of their equal measures by one.

In `Converse.lean`, the sequence of neighborhood measures has total at most one half. Recurrence at the single tolerance `1/10` forces those neighborhoods to cover the whole space, which contradicts countable subadditivity. Completeness is unused. This is a cover contradiction and does not smuggle in Borel–Cantelli or exceptional-set uniformity. The stronger lower-bound theorem passes the radius normalization `r = 10*m` through the prescribed function `q` correctly.

The resulting fixed-action theorem explicitly assumes an invariant probability measure and a free action. The group-level corollary additionally takes existence of a free pmp standard Borel model and the stated Gromov equivalence. It does not prove such a model exists in Lean.

## Positive construction, including stabilizers

I checked the potentially delicate steps separately:

- **Compactness and nonemptiness.** `returnCluster` is the compact tail cluster of pairs `(phi_n(1), phi_n(g))`, intersected with the closed cutoff of pair-distance at most two. Dominating nets supply witnesses of normalized length at most one. Keeping both coordinates avoids an unproved common-origin convergence assumption.
- **Full-group invariance.** `returnCluster_smul` replaces a return witness `g` at `x` by `g*h^-1` at `h*x`. The normalized model displacement is exactly `length(h)/r_n`. The cutoff at two and available ball radius three provide the required margin. Strict increase of integer radii absorbs every fixed `h`. Both inclusions are proved. No freeness or action-equivariance of the embeddings is assumed.
- **Borelness.** The cluster graph is expressed through countable closure tests and countably many group witnesses with Borel eligibility sets. It is proved Borel before compact selection is invoked.
- **Recentering.** The selected displacement is constant on each orbit. Consequently `x -> H(x) * x` is injective, with the explicit inverse obtained using `H(x)^-1`. This works with stabilizers. The proof never asserts that this map preserves orbit distance.
- **Uniform local multiplicity.** Nearby recentered points lift to separated original points. Their transporter representatives have length at most `7R`; right-word separation follows from original separation and injectivity. Thus group packing applies without a free action or injective raw orbit map.
- **Recurrence.** Nearest-point selection and cluster membership give a displacement `H^-1*g` of normalized length tending to zero along suitable arbitrarily late stages. Orbit invariance of `H` puts the recentered witness in the required set.
- **Finite colors.** The finite-union recurrence lemma proves one color recurs with every tolerance and every tail at a given point, using common maxima of finitely many failed tolerances/tails. Recurrence loci are separately proved invariant and Borel. The final selection is therefore constant along an orbit and preserves separation of the assembled sets.
- **Completeness and maximality.** Ordinary Borel maximal extension preserves recurrence by inclusion. Domination implies completeness and maximality among all separated supersets; these deductions are explicit Lean proofs.

## External interfaces

No inspected field of `PolynomialGeometry` or `StandardBorelTools` contains recurrence, invariant return clusters, or a recentering conclusion. I found no stronger-than-described action-theoretic assumption concealed there.

`GroupPacking` uses right-word distances; inversion changes these isometrically to left-word distances and fixes identity-centered balls. Therefore this does not require a bi-invariant metric. Uniform doubling gives exactly the finite-family bound stated.

`ScaledModels` assumes exact isometric embeddings of the finite rescaled balls in one compact metric space, without compatibility between stages. Uniform total boundedness and bounded diameter give this standard common-compact-space conclusion. This is stronger than merely extracting a Gromov–Hausdorff-convergent subsequence, so it is correct that the documentation explicitly cites the common-embedding form rather than calling arbitrary Gromov–Hausdorff convergence sufficient.

`CompactChoice` is a fixed extensional selector, uniformly usable for every Borel compact-section relation. This is stronger than selecting separately from one given relation, but it follows from a fixed Borel selector on the compact hyperspace: the compact-valued map is Borel because its open-hit sets are Borel by the sigma-compact-section projection theorem. Intersections of compact sets with open sets in a metric space are sigma-compact. Thus the exact stated interface has the standard justification given in the documentation. Its orbit-invariance consequence still requires the separately proved equality of clusters.

`BorelExtension` is the usual seeded maximal independent-set extension for a locally finite Borel graph. `BorelColoring` correctly counts the center in the local multiplicity, so a bound of `M` leads to graph degree at most `M-1` and `M` colors. `finiteNearest` is elementary finite minimization with a fixed tie-breaking order; it requires no regularity of the fixed finite family beyond its points.

These correspondence checks are mathematical review of the interfaces, not a new page-by-page source verification or a formal construction of the interfaces.

## One recurrent sequence implies subexponential growth

The code proves submultiplicativity of word-ball cardinalities and logarithmic subadditivity. Mathlib's Fekete limit is the infimum over **positive** indices; radius zero cannot spuriously force the entropy to zero. The nonnegative limit entropy gives the lower bound `exp(h*n) <= V(n)`, while the elementary generator bound gives `V(n) <= exp(b*n)`.

`exponential_ratio_bound` includes the actual integer floors, proves the denominator estimate at `floor(R/2)`, and yields the stated bound `exp(h)*exp(-h*R/4)` for tolerance `h/(4b)`. Strict increase of integer radii gives `r_n >= n`, hence summability when `h>0`. The mathlib first Borel–Cantelli lemma then rules out everywhere recurrence. No independence assumption is present.

The fixed-action theorem does not assume completeness, maximality, standard Borelness, or positive initial radius. It does explicitly assume freeness and an invariant probability measure. An informal statement that one sequence in an arbitrary action forces subexponential group growth would therefore be a material overstatement. The current README states the necessary action hypotheses correctly.

## Trust and limitations

I independently ran `lake env lean Audit.lean` from the original `lean/` directory; it exited successfully (status 0). Its printed dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`. The coordinating agent is responsible for the separate full build of the standalone repository.

The inspected source has no `sorry` tactic, `admit` tactic, custom axiom, opaque assertion, unsafe declaration, native-evaluation shortcut, or disabled-kernel device. The only text match for `admit` is ordinary English in a comment. The audit signatures expose the external parameters rather than relying solely on `#print axioms`.

The characterization remains conditional on the explicit standard inputs; absence of custom axioms does not make these hypotheses proved. The formal scope is finitely generated discrete groups with integer radii, not locally compact groups or arbitrary proper length functions. No converse from subexponential growth, intermediate-growth classification, hyperfiniteness theorem, lamplighter theorem, publication status, or novelty determination is certified by this review.
