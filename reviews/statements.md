# Independent AI review of the formal statements

Source correspondence: this report refers to the reviewed proof bodies before
extraction. The standalone files add a six-line licensing header, so source
line numbers below are six less than in the packaged files. Proof bodies are
identical, as recorded in [source-correspondence.json](source-correspondence.json).

Date: September 10, 2026.

Reviewer: a separately dispatched OpenAI Codex subagent, assigned to read the
Lean sources independently of the packaging agent. This is AI-assisted
semantic review, not outside human peer review or a novelty determination.
No proof files were edited.

## Result

No correctness defect was found in the statements reviewed. The main
signatures express the intended discrete, finitely generated results,
with the qualifications below. There is no identified vacuous premise,
wrong metric orientation, unintended freeness assumption in sufficiency,
or omitted invariant-probability hypothesis in the single-action obstructions.

I read all fifteen files in `RecurrentSections/`, their assembly import,
the exact external-input structures, the principal theorem signatures,
and the relevant mathlib definitions. I also ran `lake env lean Audit.lean`
independently: it exited with status 0 and reported dependencies for 26
principal results, without `sorryAx`. The listed logical axioms are
`propext`, `Classical.choice`, and `Quot.sound`. A source scan found no
placeholder tactic, custom axiom, unsafe declaration, native evaluation,
or elaborator override. The only occurrence of the word `admit` was
ordinary prose in a comment.

The aggregate SHA-256 of the fifteen reviewed proof sources was
`54e83b3ee1372cc9572b83f85637c8ae7208842979d56e23cb6df2c217b73549`.
It was computed by sorting paths relative to the Lean project and hashing,
for each file, its UTF-8 path, a NUL byte, file bytes, and a NUL byte.

## Detailed checks

1. **Word geometry and metric conventions — no defect found.**
   `WordGeometry.lean:10–27` requires a finite symmetric generating set
   containing the identity and exhausting the group through its powers.
   Its balls therefore are the usual closed integer word balls, and the
   least-radius length is standard. `Separated` at lines 69–70 means
   distinct section points have orbit displacement distance strictly
   greater than the given radius, even with stabilizers. The orbit metric
   uses the minimum length of an element carrying one point to another;
   this is compatible with the symmetry of the generating set.

   `StandardInputs.lean:21–24` instead uses the left word metric on return
   parameters. This is intentional: replacing a return parameter `g` by
   `g*h⁻¹` moves it a distance `length h`. In `Recentering.lean:90–96`,
   the short parameter is `k = H⁻¹*g`, the section point is `k • x`, and
   the recurrence witness is `k⁻¹`. The packing argument at lines 21–47
   uses the right word metric appropriate for actual orbit displacements.
   Inversion identifies the two group metrics and preserves identity balls.
   No orbit-map isometry is used for an action with stabilizers.

2. **Recurrence quantifiers — no defect found.**
   `WordGeometry.lean:79–82` quantifies every positive real tolerance,
   every point, and every tail bound; the witnessing index may depend on
   all three. This is everywhere infinitely-often recurrence, with a strict
   distance inequality, not merely an almost-everywhere condition or one
   return per point. `RecurrenceSelection.lean:45–72` proves equivalence
   with the countable integer-tolerance formulation.

3. **Prescribed and existential schedules — scope qualification.**
   `Converse.lean:49–53` quantifies every strictly increasing sequence of
   positive natural-number radii. `SingleSequence.lean:167–171` instead
   existentially quantifies a schedule, and
   `UniversalFreeSomeRecurrence` at lines 190–193 permits the schedule to
   depend on the action. These orders of quantification are correct and
   different. The formalized schedules are integer-valued. No theorem
   here claims all real-valued schedules or mere unboundedness without
   the stated increase/summability assumptions.

4. **Universal action and free test model — no defect found.**
   `Characterization.lean:19–28` quantifies all standard Borel spaces and
   their Borel actions, with freeness only in the separately named free
   variant. `FreePmpModel` at lines 32–41 bundles an everywhere free
   standard Borel action with an invariant probability measure; probability
   excludes an empty model. The definition of `FreeAction` in
   `Packing.lean:14` is injectivity of every orbit map, equivalent to
   trivial stabilizers. Mathlib's `SMulInvariantMeasure` expresses the
   usual preservation of measurable-set measures under inverse images.
   Since `WordGeometry` implies countability, measurable translations
   express the Borel-action condition for the countable discrete group.

5. **Positive direction and maximality — no defect found.**
   `Sufficiency.lean:14–16` has no freeness assumption.
   `recurrence_iff_virtuallyNilpotent` at lines 78–84 has only the four
   documented mathematical inputs: `gromov`, `test`, `geometry`, and
   `tools`. `PositiveConstruction` is discharged, not retained as an
   additional hypothesis. Mathlib's `Group.IsVirtuallyNilpotent` is
   explicitly existence of a finite-index nilpotent subgroup.
   `Maximality.lean:10–11` means maximality among *all* separated
   supersets, not just Borel supersets. The final maximal equivalence
   at lines 65–75 has the expected group-level signature, without an
   unintended fixed action or space parameter.

6. **One-sequence obstruction — no defect found; hypotheses essential.**
   `SingleSequence.lean:148–164` assumes one free action with an invariant
   probability measure, one strictly increasing integer schedule, and
   measurable separated sets satisfying recurrence. It does not require
   completeness, maximality, standard Borelness, or an external growth
   theorem. Its conclusion is exactly
   `log(volume n) / n → 0`, as defined in `ExponentialGrowth.lean:12–13`.
   Word-ball volumes are positive, so this normalization has the usual
   subexponential-growth meaning; the value at radius zero causes no
   issue for a limit at infinity. Submultiplicativity, Fekete's lemma,
   the exponential estimates, integer rounding, summability from
   `r n ≥ n`, and the first Borel–Cantelli application have the intended
   mathematical content.

   Public prose must retain the free invariant-probability assumption for
   this single-action result. The unrestricted assertion for *an arbitrary
   single action* would be false: the one-point trivial action has recurrent singleton
   sections regardless of the group's growth. The existing formal theorem
   and README correctly retain the needed hypothesis.

## Explicit-input boundary and limitations

`PolynomialGeometry` and `StandardBorelTools` are unproved proposition-valued
interfaces. Their fields do not contain the recurrence conclusion or an
invariant-recentering claim. At the statement level, their geometry,
maximal-independent-set extension, bounded-degree coloring, fixed compact
selector, and finite-nearest-point requirements have the expected standard
hypotheses. In particular, compact selection is requested only for nonempty
compact metric spaces, and local multiplicity includes the center, matching
an `M`-color bound.

The main equivalence is nevertheless a theorem **conditional on these
interfaces**, Gromov's equivalence, and existence of the free pmp model.
Absence of custom axioms does not discharge those explicit premises.
The fixed-action polynomial and single-sequence subexponential obstructions
are fully derived from their stated action hypotheses using mathlib.

This review checks the mathematical meaning of the displayed Lean
statements and reads their proofs; it does not prove the external interfaces,
establish a fresh-install build, verify the Lean kernel or dependencies,
certify all source-attribution details, or establish publication priority.
The packaging agent is separately responsible for rebuilding the standalone
repository. No claim about locally compact groups, arbitrary proper lengths,
or lamplighter hyperfiniteness is formalized here.
