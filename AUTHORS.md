# Authorship and provenance

**Konstantin Slutsky** — research direction, problem formulation, and
human maintainer. [Personal webpage](https://kslutsky.com).

We gratefully acknowledge **Aaron Hill's Lean formalization of Gromov's
theorem**, following the Kleiner–Tao argument. We import his
[`Gromov` development at commit `8db79f13cf211b570e3116301d91379fbc01cf3e`](https://github.com/Aaron1011/gromov/tree/8db79f13cf211b570e3116301d91379fbc01cf3e)
as an external dependency. Specifically, we use
`GeneratesNS.main_gromov_theorem` for polynomial growth implying virtual
nilpotence and `fg_of_subgroup_fg_nilpotent` for finite generation of
subgroups of finitely generated nilpotent groups. These formal proofs are
Hill's work. This project's contributions include the adapter to our word
geometry and growth conventions and the downstream formalizations.
[REFERENCES.md](REFERENCES.md) records the mathematical sources and
software provenance.

This formalization was developed in Slutsky's research project in September
2026. OpenAI's Codex supplied substantial assistance with mathematical
proof development, Lean definitions and proofs, debugging, documentation,
and repository preparation. Three separately tasked AI agents reviewed
the statements, external inputs, and proof mechanisms for the initial snapshot.
Their reports are retained in [reviews/](reviews/README.md).
The subsequent geometry deductions and reusable Borel toolkit were also
developed with Codex and locally checked with Lean; the earlier reviews
do not extend to those additions. The September 11 work includes the
common compact embedding and compact-section projection proofs and the
formalization of polynomial volume bounds, initially developed on
`research/polynomial-volume` and now complete. Classical sources and
adapted mathlib proofs retain their separate attribution.

Codex also formalized the Bernoulli free-part construction and the
reusable conull measure-restriction lemmas, removed the test-action input
from the group-level results, and checked the primary-source references
for the then-remaining two growth assumptions. This work has local Lean and
axiom-audit verification; no new separate-agent or outside human review
is claimed.

Codex located and inspected Hill's development, built it, checked its
logical dependencies, and wrote the adapter to this project's definitions.
Codex also developed the finite-index volume comparisons and the reduction
of the volume problem to nilpotent groups. Hill's imported formal proofs
retain his authorship. No new separate-agent or outside human review is
claimed.

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
uses Hill's proved finite-generation result for nilpotent subgroups.
The later matching-volume formalization uses a separate sharper argument:
Codex developed lower-central power compression, weighted conjugation and
collection using finite positive relation blocks, sharp upper distortion,
and quotient/kernel volume counting. This formalizes the matching-bounds
consequence of Bass–Guivarc'h through the discrete method presented by
Druţu–Kapovich. Their mathematical attribution is retained; neither the
explicit degree formula nor positive volume asymptotics are claimed.
These additions have Lean checks and no new separate-agent or outside
human review.
