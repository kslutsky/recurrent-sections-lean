# Palomar submission package

This repository contains a prepared Challenge/Solution package for
[Palomar](https://palomar-registry.org/how-to-submit). Preparing or running
these checks does not submit or register anything. The scripts contain no
registry intake calls, authentication flow, tag challenge, or registration step.

## What a reader should audit

[Challenge.lean](Challenge.lean) gives every project-specific definition used
in the five advertised theorems. It imports only Mathlib. The definitions are
fully specified; the only intentional holes are the five theorem proofs.
[Solution.lean](Solution.lean) supplies those proofs from the completed
library. Comparator compares the types and the definitions they use, checks
the transitive axioms, and replays the proof through Lean and NanoDa.
The Challenge must never be imported into the Solution or proof libraries.

| Comparator declaration, in namespace `PalomarRecurrence` | Mathematical claim |
|---|---|
| `recurrence_iff_polynomialGrowth` | All standard Borel actions have prescribed-radius recurrence exactly for groups of polynomial growth. |
| `recurrence_iff_virtuallyNilpotent` | The same property characterizes virtual nilpotence. |
| `freeRecurrence_iff_polynomialGrowth` | Quantifying over free actions alone gives the polynomial-growth characterization. |
| `freeRecurrence_iff_virtuallyNilpotent` | The free-action property is equivalent to virtual nilpotence. |
| `one_sequence_implies_subexponentialGrowth` | One recurrent sequence in a free probability-preserving action forces subexponential growth. |

The first four quantify over every prescribed strictly increasing positive
integer schedule. Actions with stabilizers are included in the first two.
The last theorem permits any measurable action with an invariant probability
measure; its sections need not be complete and the space need not be standard
Borel. It assumes strictly increasing integer radii and everywhere recurrence.
These distinctions are part of the statements, not extra theorem inputs.

[formalization.yaml](formalization.yaml) describes the substantive development,
source relationships, classifications, scope, and production and review history.
Aaron Hill's two imported formal proofs are recorded under
`related_formalizations`, with their exact upstream commit. The classical
sources retain their attribution. The local recurrence results carry no
definitive priority claim, and AI review is distinguished from human review.

## Local preparation checks

The ordinary library checks remain dependency-light:

```sh
lake exe cache get
python3 scripts/check.py
```

For Palomar validation, install the optional Python packages in an environment:

```sh
python3 -m venv .lake/palomar-venv
.lake/palomar-venv/bin/python -m pip install -r scripts/requirements-palomar.txt
python3 scripts/palomar_tools.py
.lake/palomar-venv/bin/python scripts/palomar.py validate
```

Tool setup downloads pinned public Git repositories and builds their tools.
It requires Git, elan/Lake, Rust/Cargo, and, on Linux, Go, a C compiler, and
the libseccomp development headers. It installs no registry service and makes
no submission. The project stays on Lean
4.33.0-rc2. Palomar's current Comparator builds with its own Lean 4.34.0-rc1
and its own pinned parser; the exporter uses the project's exact toolchain.
Allow disk space for both toolchains and the Mathlib cache.

The validator runs the upstream v0.4 schema and Palomar's metadata and
Comparator-configuration validators, then checks the local statement,
licence, manifest, and source layout. These checks do not reproduce the
registry's complete checkout, protected-import, archival, or rendering pipeline.

On Linux, run the isolated comparison and controls:

```sh
.lake/palomar-venv/bin/python scripts/palomar.py all --record
```

Real Landrun is mandatory in this mode. The Linux launcher additionally
blocks creation of AF_UNIX sockets using libseccomp, applying Comparator's
documented socket restriction without requiring systemd. Tool setup tests
ordinary IPv4 sockets, Unix sockets and socket pairs, and an upper-bit bypass
attempt against the actual loaded filter. Both local Linux checks and CI use
this launcher; failure to build or load either restriction stops the check.

On macOS, the explicit native diagnostic is available:

```sh
.lake/palomar-venv/bin/python scripts/palomar.py all --native --record
```

This uses Comparator's unmodified upstream development launcher. It checks
statement/definition matching and both kernels, but provides no Landrun
isolation. Its reports are labelled `native` and cannot establish that the
Linux sandbox or Palomar's protected-import pipeline passed. There is no
automatic fallback from Linux isolation to the native diagnostic.

The controls include a valid small theorem and four deliberately invalid
submissions: a different theorem statement, a changed definition, a custom
axiom, and an unproved Solution. Each invalid case must fail for the expected
reason. They are created below ignored `.lake/`, outside the proof library.

### Optional Linux container

[scripts/palomar.Dockerfile](scripts/palomar.Dockerfile) supplies an Ubuntu
environment with the required build tools and a non-root user. From the
repository root:

```sh
docker build -f scripts/palomar.Dockerfile -t recurrent-palomar-local scripts
docker run --rm -it \
  --mount type=bind,src="$PWD",dst=/source,readonly \
  --mount type=volume,src=recurrent-palomar-work,dst=/workspace \
  -e LEAN_NUM_THREADS=2 -e CARGO_BUILD_JOBS=2 \
  recurrent-palomar-local bash
```

Inside the container, copy the source into the build volume and run the same
checks. The copy includes Git metadata for the source-layout audit, excludes
host build caches, and leaves the host repository read-only:

```sh
tar -C /source --exclude=./.lake --exclude=__pycache__ --exclude=.DS_Store -cf - . \
  | tar -C /workspace --no-same-owner -xf -
mkdir -p .lake
python3 -m venv .lake/palomar-venv
.lake/palomar-venv/bin/python -m pip install -r scripts/requirements-palomar.txt
python3 scripts/palomar_tools.py
lake exe cache get
python3 scripts/check.py --record
.lake/palomar-venv/bin/python scripts/palomar.py all --record
```

The named volume retains build caches and verification reports after the
container exits. Use a fresh volume when checking a fresh source snapshot;
overlaying a changed tree can leave obsolete files. Docker's Linux kernel
must support Landrun. No privileged container is needed.

## Evidence and remaining external steps

The complete local Linux run passed, including both kernels and all controls;
the native macOS diagnostic also passed. The
[verification guide](verification/README.md) records the scope and outcome.

Checks write logs below `.lake/palomar-results/`. With `--record`, their reports
and logs are copied to the ignored `verification/palomar-native/` or
`verification/palomar-linux/` directories, including source hashes, tool pins,
mode, platform, and the exact control sources. A passing native record is not a
Palomar mechanical-verification record.

The repository has no hosted Palomar workflow or registry submission job. The
checks above are run locally when needed. A future registry submission must
select a pushed full commit SHA, use this root project with `comparator.json` and
`formalization.yaml`, and undergo the registry's own verification and editorial
review. No registration is requested by this package.

## Tool provenance

[scripts/palomar-pins.json](scripts/palomar-pins.json) records the exact tool
and validator sources. Comparator, NanoDa, and Landrun follow
[PalomarSubmission at `ef2fa1e`](https://github.com/PalomarRegistry/PalomarSubmission/tree/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763);
lean4export is the exact `v4.33.0-rc2` release tag. The schema is pinned to
[formalization.yaml at `99c678e`](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e).
The [Palomar starter](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8)
informed the layout, workflow, and metadata. The local Python orchestration
was developed with Codex. Downloaded tools remain external dependencies and
retain their own copyrights and licences.
