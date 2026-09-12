# Recurrent cross sections and growth of groups

Lean 4 proofs relating recurrent Borel cross sections to the growth of
finitely generated groups.

This is the **`research/polynomial-volume` branch**. The full Gromov
equivalence is proved. The difficult implication uses Aaron Hill's existing
formalization; the converse uses a local discrete collection proof. The **nilpotent polynomial-volume estimate
remains unproved**; completing the volume theorem is work in progress.
[VOLUME_RESEARCH.md](VOLUME_RESEARCH.md) records the scope.

- Every prescribed increasing positive radius schedule in one free
  probability-preserving action forces **virtual nilpotence**, with no
  unproved mathematical input.
- One recurrent sequence in such an action forces **subexponential growth**.
- The full characterization by recurrence for all Borel actions, including
  actions with stabilizers, now reduces to **one explicit nilpotent volume
  input**, the matching-bounds part of the Bass–Guivarc'h theorem.

The Bernoulli test action and all geometric and Borel construction tools
are proved. Finite-index word-volume comparison is proved without assuming
normality. Polynomial upper bounds for all finitely generated nilpotent
groups and the full Gromov equivalence require no unproved theorem argument. The general matching-volume theorem is not yet discharged.
[STANDARD_INPUTS.md](STANDARD_INPUTS.md) gives the exact statements and
explains the older modular interfaces that remain available.

## Read the mathematics

- [PROBLEM.md](PROBLEM.md): definitions, background, and quantifiers.
- [RESULTS.md](RESULTS.md): precise main statements and Lean names.
- [STANDARD_INPUTS.md](STANDARD_INPUTS.md): all unproved inputs and their
  correspondence with standard results.
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
subsequent geometry and toolkit proofs have local Lean verification but
have not received a new separate-agent or human review.

Research direction and maintenance: **Konstantin Slutsky**.
OpenAI's **Codex** contributed substantially to the mathematics, proofs,
documentation, and review. See [AUTHORS.md](AUTHORS.md) and the explicit
[AI-use acknowledgement](ACKNOWLEDGEMENTS.md).

Licensed under [Apache-2.0](LICENSE). Citation metadata is in
[CITATION.cff](CITATION.cff); cite the commit used and the underlying sources.

The research branch also proves matching volume bounds for all finitely
generated abelian groups in
[AbelianVolume.lean](RecurrentSections/AbelianVolume.lean), using mathlib's
abelian structure theorem, exact cubical balls, and finite-index comparison.
This discharges the abelian base case, including torsion; the general
nilpotent estimate remains unproved.
