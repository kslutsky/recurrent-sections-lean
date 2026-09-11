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

For this repository, three separately tasked Codex AI agents reviewed
the formal statements, the standard-result interfaces, and the proof
mechanisms. These were separate AI review passes using the same source
snapshot. They are not independent human peer review, and agreement
between agents is not a guarantee of correctness. The reports in
[reviews/](reviews/README.md) record their scope and findings.

Lean compilation and the axiom audits provide a different kind of
evidence: they check the formal proof terms and expose their logical
dependencies. They do not prove that an informal theorem was translated
as intended, that every unproved interface matches its cited source, or
that a result is new. The external mathematical hypotheses remain explicit
in [STANDARD_INPUTS.md](STANDARD_INPUTS.md).

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
