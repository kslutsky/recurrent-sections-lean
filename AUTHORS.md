# Authorship and provenance

**Konstantin Slutsky** — research direction, problem formulation, and
human maintainer. [Personal webpage](https://kslutsky.com).

This formalization was developed in his research project in September
2026. OpenAI's Codex supplied substantial assistance with mathematical
proof development, Lean definitions and proofs, debugging, documentation,
and repository preparation. Three separately tasked AI agents reviewed
the statements, external inputs, and proof mechanisms for the initial snapshot.
Their reports are retained in [reviews/](reviews/README.md).
The subsequent geometry deductions and reusable Borel toolkit were also
developed with Codex and locally checked with Lean; the earlier reviews
do not extend to those additions. The September 11 work includes the
common compact embedding and compact-section projection proofs and the
partial formalization of polynomial volume bounds, now isolated on
`research/polynomial-volume`. Classical sources and
adapted mathlib proofs retain their separate attribution.

Codex also formalized the Bernoulli free-part construction and the
reusable conull measure-restriction lemmas, removed the test-action input
from the group-level results, and checked the primary-source references
for the remaining two growth assumptions. This work has local Lean and
axiom-audit verification; no new separate-agent or outside human review
is claimed.

The Gromov forward proof is **Aaron Hill's** existing formalization of the
Kleiner–Tao argument, imported as a pinned external dependency. Codex located
and inspected that development, built it, checked its logical dependencies,
and wrote the adapter to this project's definitions. Codex also developed
the finite-index volume comparisons and the reduction of the remaining
volume problem to nilpotent groups. These contributions do not establish
the general nilpotent volume estimate or constitute a new proof of Gromov's
theorem. No new separate-agent or outside human review is claimed.

AI tools are acknowledged as tools, not listed as authors.
[ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md) specifies their uses and the
limits of the automated review. The citation metadata identifies the
human responsible for this repository; it does not imply that every
definition or proof was independently written or reviewed by that person.

The recurrent-section construction for free integer-lattice actions
is due to Boykin and Jackson, with the formulation used here appearing
in Marks and Unger's appendix. The geometric and Borel tools, as well
as Lean and mathlib, are separately credited in
[REFERENCES.md](REFERENCES.md). This repository's generalized construction
and growth obstructions are research results under review; no definitive
priority claim is made.

The source was extracted from the research project's Lean development.
No private research logs, unpublished manuscript files, cached papers,
or dependency source trees form part of the Git repository.

Codex also developed the local discrete collection proof of polynomial
upper growth for nilpotent groups, including the conjugation, word-swap,
and counting lemmas. This formalizes a classical conclusion of Wolf and
uses Hill's proved finite-generation result for nilpotent subgroups. The
stronger general matching-volume theorem remains unproved; the upper-bound
proof is not presented as a formalization of the sharp Bass–Guivarc'h estimate.
