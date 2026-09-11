# Separate AI reviews

Three separately tasked OpenAI Codex agents examined the sources
independently of the coordinating repository-preparation agent on
September 10, 2026.

**Snapshot scope:** these reports concern initial commit `a2f61ad`.
The later geometry deductions and reusable Borel toolkit have not received
a new separate-agent or human review. Their local verification is recorded
in [verification/](../verification/README.md).

| Review | Scope | Result |
|---|---|---|
| [Formal statements](statements.md) | Definitions, quantifiers, theorem signatures, metrics, stabilizers, growth normalizations | No semantic correctness defect found |
| [Standard inputs](standard-inputs.md) | Every unproved interface and its standard mathematical justification | No incorrect or circular input found; source-access limits recorded |
| [Proof mechanisms](proof-mechanisms.md) | Growth obstructions, compact limits, recentering, Borelness, coloring, maximality | No confirmed proof or statement defect found |
| [Documentation follow-up](documentation.md) | Problem/results prose against the actual Lean statements | Omitted hypotheses in abbreviated summaries corrected |

The statement and proof reviewers each independently ran the principal
`Audit.lean` check successfully. The coordinator separately rebuilt the
standalone sources and ran the broader diagnostics recorded in
[verification/](../verification/README.md).

At the initial commit, the fifteen reviewed mathematical source bodies
matched the extracted standalone bodies after removing six-line license
headers. [source-correspondence.json](source-correspondence.json) records
that historical correspondence, not hashes of the evolving current tree.
The toolkit update moved four elementary word-geometry lemmas between
modules and added new proofs. Line references in the detailed reports
refer to the original pre-header sources.

These are separate **AI review passes**, not outside human peer review.
The agents used the same source snapshot and general model/tool
environment; their agreement is not independent evidence in the sense
of human refereeing. Kernel checking, semantic review, source attribution,
and novelty assessment remain different matters.

The reports do not discharge the explicit standard inputs, verify Lean's
kernel implementation, or certify publication priority. The precise
conditionality of the full characterization is retained in
[RESULTS.md](../RESULTS.md) and
[STANDARD_INPUTS.md](../STANDARD_INPUTS.md).
