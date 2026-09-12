# Acknowledgements and use of AI

This work builds on Boykin and Jackson's recurrent cross-section
construction and its formulation by Marks and Unger. We acknowledge
the geometric results of Gromov and Breuillard, the Borel graph and
selection theory of Kechris, Solecki, Todorcevic and others, and the
work of the Lean developers and the mathlib community.
[REFERENCES.md](REFERENCES.md) and
[STANDARD_INPUTS.md](STANDARD_INPUTS.md) identify the sources and their roles.

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

OpenAI's **Codex** was used substantially throughout the project:
to develop and examine mathematical arguments, search and inspect
literature, design the formal definitions, write and revise Lean proofs,
inspect mathlib APIs, respond to compiler diagnostics, draft Markdown
documentation, and prepare the repository and its verification scripts.
The assistance extended to the mathematics and formal proofs, beyond
language editing or code completion.

For the initial repository snapshot, three separately tasked Codex AI agents reviewed
the formal statements, the standard-result interfaces, and the proof
mechanisms. These were separate AI review passes using the same source
snapshot. They are not independent human peer review, and agreement
between agents is not a guarantee of correctness. The reports in
[reviews/](reviews/README.md) record their scope and findings.

Codex subsequently developed the geometry deductions and the reusable
`BorelToolkit` library, including its graph and measurable-selection
proofs, and ran the expanded local Lean checks. These additions have not
received a new separate-agent review or outside human peer review. The
classical KST and Kuratowski--Ryll-Nardzewski constructions retain their
original mathematical attribution.

For the September 11 additions, Codex developed the common compact
embedding proof, Novikov countable separation, the Kunugui–Novikov rectangle
decomposition, and compact-section Borel projection. It also developed
volume-normalization lemmas, initially developed on the
`research/polynomial-volume` branch. Lang's and Srivastava's presentations
and the adapted mathlib proof patterns are explicitly credited in
[REFERENCES.md](REFERENCES.md). These additions likewise have local kernel
checks but no new separate-agent or outside human review. The completed
matching-bounds formalization now supplies a proof of the polynomial-volume
interface used by the main results.

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

Lean compilation and the axiom audits provide a different kind of
evidence: they check the formal proof terms and expose their logical
dependencies. They do not prove that an informal theorem was translated
as intended, that every unproved interface matches its cited source, or
that a result is new. The dependency inventory and ordinary hypotheses remain explicit in
[STANDARD_INPUTS.md](STANDARD_INPUTS.md).

The human maintainer remains responsible for the content, attribution,
and decisions to publish or use this work. This disclosure does not
represent a certification that outside human review has been completed.
AI systems are not assigned authorship. This approach follows the
[London Mathematical Society's AI guidance](https://www.lms.ac.uk/publications/policies/AI)
on identifying tools and their uses and retaining human responsibility
(consulted September 10, 2026).

The original files in this repository are made available under the
[Apache License 2.0](LICENSE). Lean, mathlib, and other dependencies
retain their own copyright notices and licenses.

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


Codex also prepared the Palomar Challenge/Solution adapters, structured
metadata, and local verification tooling. The Palomar template informed the
package layout; Comparator, lean4export, NanoDa, Landrun, and the upstream
metadata validators retain their software attribution and licences. Exact
pins and the scope of local checks are recorded in PALOMAR.md. These checks
do not constitute a Palomar submission, editorial review, or registration.
