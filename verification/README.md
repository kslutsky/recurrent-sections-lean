# Verification record

The completed `research/polynomial-volume` sources were checked on
September 12, 2026 UTC (September 11 local time), with Lean 4.33.0-rc2.
[verification.json](verification.json) records the exact timestamp,
platform, all ten pinned dependency revisions, and SHA-256 hashes of the
68 checked Lean source files, configuration files, and verification script.

Both Gromov's equivalence and the matching polynomial-volume theorem are
proved. The final recurrence characterizations have no unproved mathematical
theorem arguments. Main remains at its earlier interface.

The command was:

```sh
LEAN_NUM_THREADS=2 python3 scripts/check.py --record
```

All checks passed:

| Check | Evidence |
|---|---|
| All 63 modules in three libraries are reachable from the root; no forbidden proof shortcut | Source/import guard |
| Reusable Borel and metric libraries do not import the recurrence application | Import-boundary guard |
| All ten dependencies match their pins, with no tracked source modifications | Dependency check |
| Full build, project warnings treated as errors: 8836 jobs | [build-output.txt](build-output.txt) |
| Signatures and axiom dependencies of 100 principal results | [audit-output.txt](audit-output.txt) |
| All 830 project declarations, including private declarations, use only the allowed logical axioms | [all-axioms-output.txt](all-axioms-output.txt) |
| An injected axiom in `BorelToolkit` is rejected | [negative-control-output.txt](negative-control-output.txt) |

The allowed logical axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The audit recursively traverses compiled declarations using Lean's
`collectAxioms` API, including dependencies in mathlib and Hill's Gromov
formalization. The negative-control error is intentional and required for
the test to pass. Its temporary source is in the ignored `.lake/` tree.
The audit also rejects a missing library, preventing an empty import set
from passing vacuously.

Ordinary theorem hypotheses are not custom axioms. Accordingly, the
principal audit also prints the main signatures and interface definitions.
In particular, `polynomialVolumeTheorem W` inhabits the precise volume
interface, and the `_of_standard_theorems` characterizations request only
the group and word geometry. [STANDARD_INPUTS.md](../STANDARD_INPUTS.md)
gives the full inventory and explains the retained modular statements.

The pinned mathlib cache was reused. Hill's complete Gromov dependency was
built locally from its pinned source before integration; its unchanged
upstream deprecation and style warnings are preserved in the build log.
This project's warnings remain errors. The integration initially found
one unused-binder warning in the volume interface; it was corrected before
this completed run. No proof assumption was added to resolve it.

## Separate consumer-package check

A separate Lake package with its own configuration and manifest was built
using a local path dependency on this project and the same pinned dependency
cache. `LEAN_NUM_THREADS=2 lake build` passed with 8835 jobs.

- `ToolkitConsumer` imports only the Borel and metric tools and checks
  measurable selection, graph covers, compact projection, common compact
  embedding, and the free Bernoulli measure.
- `VolumeConsumer` checks Gromov, the exact matching-volume conclusion,
  maximal recurrence versus virtual nilpotence, and free recurrence versus
  polynomial growth, without unproved theorem-input arguments.

[consumer-source.md](consumer-source.md) contains both complete consumer
modules and their Lake configuration.
[consumer-build-output.txt](consumer-build-output.txt) records the build.
[consumer-verification.json](consumer-verification.json) records their
hashes and the hash of the corresponding project verification record.
This supersedes the earlier consumer check on Lean 4.29.1.

These are local builds and kernel audits, not evidence that GitHub-hosted
CI has run, independent human review, or certification of novelty.
