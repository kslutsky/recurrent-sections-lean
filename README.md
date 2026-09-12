# Recurrent cross sections and growth of groups

Lean 4 proofs relating recurrent Borel cross sections to the growth of
finitely generated groups.

**Main result.** A finitely generated group $G$ has polynomial growth
(equivalently, is virtually nilpotent) if and only if every Borel action
$G\curvearrowright X$ on a standard Borel space admits recurrent Borel
cross sections at every prescribed strictly increasing sequence of positive
integer radii $(r_n)$. The sections $C_n$ can be chosen maximal
$r_n$-separated, and recurrence means that for every $x\in X$ and every
$\varepsilon>0$, the inequality $d(x,C_n)<\varepsilon r_n$ holds for
infinitely many $n$, where $d$ is the orbit distance induced by a fixed word
metric on $G$. The same characterization holds when only free actions are
considered.

In [Problem A.3 of *Borel circle squaring*](https://annals.math.princeton.edu/wp-content/uploads/annals-v186-n2-p04-p.pdf#page=22)
(Annals of Mathematics **186** (2017), p. 602), Marks and Unger ask whether
this property holds for every free Borel action of every finitely generated
amenable group. The characterization gives a negative answer in general
and identifies polynomial growth as the exact condition for it to hold in
all free Borel actions.

Both Gromov's equivalence and the matching polynomial-volume theorem are
proved. The complete recurrent-section characterization has **no unproved
mathematical theorem inputs**. [VOLUME_RESEARCH.md](VOLUME_RESEARCH.md)
explains the proof and its scope.

- Virtual nilpotence is equivalent to prescribed-radius recurrence for
  every Borel action, including actions with stabilizers.
- Restricting this quantification to free Borel actions gives the same class.
- Every prescribed increasing positive radius schedule in one free
  probability-preserving action forces virtual nilpotence.
- One recurrent sequence in such an action forces subexponential growth.

The Gromov forward implication uses **[Aaron Hill's existing formalization](https://github.com/Aaron1011/gromov)**.
His proved finite-generation theorem for nilpotent subgroups is also used.
The nilpotent growth and matching-volume arguments are developed locally
from the classical constructions, with explicit attribution to Wolf,
Bass, Guivarc'h, and Druţu–Kapovich. The matching exponent is existential;
the rank formula and positive volume asymptotics are outside the formal scope.
The Bernoulli action and all geometric and Borel construction tools are
proved. [STANDARD_INPUTS.md](STANDARD_INPUTS.md) records the dependency inventory.

## Read the mathematics

- [PROBLEM.md](PROBLEM.md): definitions, background, and quantifiers.
- [RESULTS.md](RESULTS.md): precise main statements and Lean names.
- [STANDARD_INPUTS.md](STANDARD_INPUTS.md): dependency inventory and the
  correspondence with classical results.
- [REFERENCES.md](REFERENCES.md): mathematical and software attribution.
- [TOOLS.md](TOOLS.md): reusable Borel graph and measurable-selection library.
- [PALOMAR.md](PALOMAR.md): independent statements, structured metadata, and submission checks.

The starting recurrent-section construction is due to Boykin and Jackson;
the prescribed-radius formulation used here appears in Marks and Unger's
appendix. This is a research formalization. Publication priority and
outside human review are not certified by this repository.

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan).
The toolchain file selects **Lean 4.33.0-rc2**. From the repository root:

```sh
lake exe cache get
python3 scripts/check.py
```

The first command obtains mathlib's dependency cache. The second builds
every proof module with warnings treated as errors, checks the main
theorem signatures and axioms, audits every project declaration's axiom
dependencies, and tests rejection of an injected custom axiom.
It needs Python 3.10 or newer and only Python's standard library.
The separate `Challenge.lean` contains five deliberate statement holes;
its proofs are supplied and audited in `Solution.lean`. No proof-library
holes or unproved Solution declarations are allowed.

The individual Lean commands are:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true AllAxioms.lean
```

Mathlib is pinned at `a6180e1994004a7c705114bcbebaf5fff4b8384d`, and Hill's
[Gromov development](https://github.com/Aaron1011/gromov) at
`8db79f13cf211b570e3116301d91379fbc01cf3e`. All transitive revisions are in
`lake-manifest.json`. Project warnings are errors via `lakefile.toml`;
the unmodified upstream Gromov development reports legacy warnings.
Its proof dependencies are checked by the same recursive axiom audit.
No parent repository or private research file is needed.

[GitHub Actions](.github/workflows/lean.yml) runs the same script on
pushes and pull requests. The [verification guide](verification/README.md)
describes the checks and their last completed local run. The optional
`--record` flag writes ignored local artifacts; CI preserves its logs as
workflow artifacts rather than committing generated output.

## Palomar preparation

[Challenge.lean](Challenge.lean) states the five advertised results independently
using only Mathlib imports. [Solution.lean](Solution.lean) supplies the proofs;
[comparator.json](comparator.json) fixes the comparisons, and
[formalization.yaml](formalization.yaml) records provenance and review status.
See [PALOMAR.md](PALOMAR.md) for local metadata validation, Comparator/NanoDa
checks, and the distinction between macOS diagnostics and Linux isolation.
These files and workflows do not submit or register the project.

## Review and attribution

Three separately tasked AI agents reviewed the initial snapshot's formal
statements, unproved interfaces, and proof mechanisms. Their reports are in
[reviews/](reviews/README.md). This is separate AI review, not outside
human peer review; kernel checking addresses a different question. The
subsequent geometry, toolkit, Gromov integration, and volume proofs have
local Lean verification but no new separate-agent or outside human review.

Research direction and maintenance: **Konstantin Slutsky**.
OpenAI's **Codex** contributed substantially to the mathematics, proofs,
documentation, and review. See [AUTHORS.md](AUTHORS.md) and the explicit
[AI-use acknowledgement](ACKNOWLEDGEMENTS.md).

Licensed under [Apache-2.0](LICENSE). Citation metadata is in
[CITATION.cff](CITATION.cff); cite the commit used and the underlying sources.
