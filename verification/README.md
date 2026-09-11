# Verification record

The standalone sources were checked on September 10, 2026 with Lean
4.29.1 and the exact dependency revisions in `lake-manifest.json`.
[verification.json](verification.json) records the platform, time,
dependency revisions, and SHA-256 hashes of the checked source/configuration
files and verification script.

The fifteen proof modules were built from scratch in this standalone
directory. A local copy of the pinned dependency cache was reused;
mathlib itself was not rebuilt from scratch. No project build artifacts
were copied from the parent research development.

The final command was:

```sh
python3 scripts/check.py --record
```

It passed all of these checks:

| Check | Evidence |
|---|---|
| Every proof module is reachable from the root import; source contains no forbidden proof shortcut | Verification script's source/import guard |
| All nine dependency revisions match the manifest, with no tracked source modifications | Verification script's dependency check |
| Build with warnings treated as errors: 3305 build jobs | [build-output.txt](build-output.txt) |
| Signatures and logical dependencies of 26 principal results | [audit-output.txt](audit-output.txt) |
| All 242 project declarations use only the allowed logical axioms | [all-axioms-output.txt](all-axioms-output.txt) |
| A deliberately injected custom axiom is rejected | [negative-control-output.txt](negative-control-output.txt) |

The error in the negative-control log is intentional and is required for
that test to pass. Its temporary Lean source is generated inside the
ignored `.lake/` tree; it is not part of the mathematical library.

The allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The whole-project diagnostic traverses compiled kernel
declarations using Lean's `collectAxioms` API. It does not replace an
independent implementation of the Lean kernel. Explicit mathematical
hypotheses remain visible in the signatures and are documented in
[STANDARD_INPUTS.md](../STANDARD_INPUTS.md).

[The GitHub workflow](../.github/workflows/lean.yml) invokes the same script.
GitHub-hosted execution has not occurred merely because this local check
passed. Refresh the evidence with `--record` after changing a checked file.
