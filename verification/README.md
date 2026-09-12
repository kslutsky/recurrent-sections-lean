# Verification guide

Generated verification logs and hash reports are deliberately excluded from
Git. The proof sources, audit programs, pinned tool setup, and ordinary Lean
workflow are committed, so each result can be reproduced without retaining
machine-specific output in source history. Palomar performs and publishes its
own verification for a submitted commit.

## Lean build and axiom audit

From the repository root, run:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 python3 scripts/check.py
```

The script checks that all 63 modules in the three proof libraries are imported,
enforces the library import boundaries, verifies every dependency revision and
tracked dependency tree, builds the project with project warnings treated as
errors, prints the signatures and axioms of 105 principal results, recursively
audits all 835 project declarations, and confirms that an injected custom axiom
is rejected. The only permitted logical axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

`Challenge.lean` contains exactly five deliberate theorem holes and fully
specified definitions. It is compiled separately and is never imported into the
proved Solution or the three proof libraries. `Solution.lean` and the proof
libraries contain no holes or custom axioms.

The last clean Linux run, on September 12, 2026, built 8840 jobs and passed all
of these checks. Aaron Hill's pinned Gromov dependency was built from source.
The optional command

```sh
LEAN_NUM_THREADS=2 python3 scripts/check.py --record
```

writes detailed logs and an input-hash report under this directory. Those files
are ignored by Git and may be retained locally when needed.

## Comparator and independent kernels

[PALOMAR.md](../PALOMAR.md) describes the five independent statements, exact
tool pins, Linux isolation, controls, and reproduction commands. The completed
fresh Linux/aarch64 run used Ubuntu 24.04, a non-root user, real Landrun, and a
tested AF_UNIX socket restriction. All five statements and their definitions
matched, and both NanoDa and Lean accepted the complete proof. A valid control
passed; changed statements, changed definitions, a custom axiom, and an unproved
Solution were each rejected for the expected reason. The same comparisons and
kernel replays also passed in the explicitly non-isolated native macOS diagnostic.

Run the full isolated Linux check with:

```sh
.lake/palomar-venv/bin/python scripts/palomar.py all --record
```

The recorded reports are written to an ignored `verification/palomar-linux/`
directory and the primary logs remain below `.lake/palomar-results/linux/`.
The repository has no hosted Palomar workflow; these checks are run locally.

## Separate consumer check

[consumer-source.md](consumer-source.md) preserves the source and configuration
of a separate Lake consumer package. Its `ToolkitConsumer` imports only the
Borel and metric tools; its `VolumeConsumer` checks the growth and recurrence
interfaces. A separate build of this package passed against the completed proof
libraries. Generated consumer manifests, build logs, and hash reports are not
kept in Git.

These are reproducible build and kernel checks. They do not constitute outside
human review, certification of novelty, or a Palomar registration.
