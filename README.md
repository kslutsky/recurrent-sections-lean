# Recurrent cross sections and growth of groups

Lean 4 proofs relating recurrent Borel cross sections to the growth of
finitely generated groups.

- **Prescribed radii characterize virtual nilpotence.** Every Borel action,
  including actions with stabilizers, has recurrent maximal separated
  cross sections at every prescribed increasing positive integer schedule
  exactly when the group is virtually nilpotent. The formal equivalence
  takes explicitly stated standard geometric and Borel-theoretic inputs.
- **All prescribed schedules in one free probability-preserving action**
  already force polynomial growth.
- **One recurrent sequence at increasing integer radii in one free
  probability-preserving action**
  forces subexponential growth: `log |B(n)| / n → 0`.

The two fixed-action growth obstructions have no unformalized mathematical
inputs. The full characterization takes Gromov's growth equivalence,
existence of a free pmp Borel action, and the interfaces specified in
[STANDARD_INPUTS.md](STANDARD_INPUTS.md). The positive recurrence
construction itself is proved, not assumed.

## Read the mathematics

- [PROBLEM.md](PROBLEM.md): definitions, background, and quantifiers.
- [RESULTS.md](RESULTS.md): precise main statements and Lean names.
- [STANDARD_INPUTS.md](STANDARD_INPUTS.md): all unproved inputs and their
  correspondence with standard results.
- [REFERENCES.md](REFERENCES.md): mathematical and software attribution.

The starting recurrent-section construction is due to Boykin and Jackson;
the prescribed-radius formulation used here appears in Marks and Unger's
appendix. This is a research formalization. Publication priority and
outside human review are not certified by this repository.

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan).
The toolchain file selects **Lean 4.29.1**. From the repository root:

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
lake build --wfail
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true AllAxioms.lean
```

Mathlib **v4.29.1** is pinned at
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, with all transitive revisions
in `lake-manifest.json`. No parent repository or private research file
is needed. Dependencies and generated files stay in the ignored `.lake/`.

[GitHub Actions](.github/workflows/lean.yml) runs the same script on
pushes and pull requests. [Verification evidence](verification/README.md)
records the local run, exact output, and source hashes. Refresh it with
`python3 scripts/check.py --record` after changes. A local run does not
mean GitHub-hosted CI has already executed.

## Review and attribution

Three separately tasked AI agents reviewed the formal statements,
unproved interfaces, and proof mechanisms. Their reports are in
[reviews/](reviews/README.md). This is separate AI review, not outside
human peer review; kernel checking addresses a different question.

Research direction and maintenance: **Konstantin Slutsky**.
OpenAI's **Codex** contributed substantially to the mathematics, proofs,
documentation, and review. See [AUTHORS.md](AUTHORS.md) and the explicit
[AI-use acknowledgement](ACKNOWLEDGEMENTS.md).

Licensed under [Apache-2.0](LICENSE). Citation metadata is in
[CITATION.cff](CITATION.cff); cite the commit used and the underlying sources.
