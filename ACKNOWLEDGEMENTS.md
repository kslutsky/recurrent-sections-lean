# Acknowledgements and use of AI

This work builds on Boykin and Jackson's recurrent cross-section
construction and its formulation by Marks and Unger. We acknowledge
the geometric results of Gromov and Breuillard, the Borel graph and
selection theory of Kechris, Solecki, Todorcevic and others, and the
work of the Lean developers and the mathlib community.
[REFERENCES.md](REFERENCES.md) and
[STANDARD_INPUTS.md](STANDARD_INPUTS.md) identify the sources and their roles.

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
volume-normalization lemmas, now isolated on `research/polynomial-volume`. Lang's and Srivastava's presentations and the adapted mathlib proof
patterns are explicitly credited in [REFERENCES.md](REFERENCES.md).
These additions likewise have local kernel checks but no new separate-agent
or outside human review. The general polynomial-volume theorem is retained as an explicit black box
on `main`; the completed matching-bounds formalization is on the research branch.

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
volume problem to nilpotent groups. The difficult Gromov proof retains Hill's authorship; the local adapter
and downstream results do not constitute a new proof of that theorem. No new separate-agent or outside human review is claimed.

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
uses Hill's proved finite-generation result for nilpotent subgroups. The later matching-volume formalization uses a separate sharper argument:
Codex developed lower-central power compression, weighted conjugation and
collection using finite positive relation blocks, sharp upper distortion,
and quotient/kernel volume counting. This formalizes the matching-bounds
consequence of Bass–Guivarc'h through the discrete method presented by
Druţu–Kapovich. Their mathematical attribution is retained; neither the
explicit degree formula nor positive volume asymptotics are claimed.
These additions have Lean checks and no new separate-agent or outside
human review.
