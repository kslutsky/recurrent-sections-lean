# Recurrent cross sections and growth of groups

Lean 4 proofs relating recurrent Borel cross sections to the growth of
finitely generated groups.

This is the **`research/polynomial-volume` branch**. Both Gromov's
equivalence and the matching polynomial-volume theorem are proved.
The complete recurrent-section characterization now has **no unproved
mathematical theorem inputs**. [VOLUME_RESEARCH.md](VOLUME_RESEARCH.md)
explains the proof and its scope. Main remains unchanged.

- Virtual nilpotence is equivalent to prescribed-radius recurrence for
  every Borel action, including actions with stabilizers.
- Restricting this quantification to free Borel actions gives the same class.
- Every prescribed increasing positive radius schedule in one free
  probability-preserving action forces virtual nilpotence.
- One recurrent sequence in such an action forces subexponential growth.

The Gromov forward implication uses **Aaron Hill's existing formalization**.
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
every project module with warnings treated as errors, checks the main
theorem signatures and axioms, audits every project declaration's axiom
dependencies, and tests rejection of an injected custom axiom.
It needs Python 3.10 or newer and only Python's standard library.

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
pushes and pull requests. [Verification evidence](verification/README.md)
records the local run, exact output, and source hashes. Refresh it with
`python3 scripts/check.py --record` after changes. A local run does not
mean GitHub-hosted CI has already executed.

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
