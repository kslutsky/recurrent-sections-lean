# References and attribution

## Recurrent-section antecedents

**C. M. Boykin and Steve Jackson.** *Borel boundedness and the lattice
rounding property.* In *Advances in Logic*, Contemporary Mathematics
**425**, American Mathematical Society, 2007, 113–126.
[DOI](https://doi.org/10.1090/conm/425/08121).
The lattice recurrence construction is attributed to this work by
Marks and Unger. The precise statement used here was inspected in the
latter's appendix; direct inspection of Boykin–Jackson's publisher PDF
is not claimed.

**Andrew S. Marks and Spencer T. Unger.** *Borel circle squaring.*
Annals of Mathematics (2) **186** (2017), no. 2, 581–605.
[DOI](https://doi.org/10.4007/annals.2017.186.2.4);
[published PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v186-n2-p04-p.pdf).
Appendix A, Lemma A.2 gives prescribed-radius recurrence for free lattice
actions. Its discussion and Problem A.3 motivate the growth questions.
The compact-selection and recentering proof develops this antecedent.

**François Le Maître and Konstantin Slutsky.** *L¹ full groups of flows.*
[arXiv:2108.09009v3](https://arxiv.org/abs/2108.09009v3).
Lemma E.2 records related finite coloring by packing for locally compact
actions. It is credited as an antecedent, not assumed as a recurrence theorem.

## Standard geometric and Borel inputs

**Mikhail Gromov.** *Groups of polynomial growth and expanding maps*,
with an appendix by Jacques Tits. Publications Mathématiques de l'IHÉS
**53** (1981), 53–78.
[DOI](https://doi.org/10.1007/BF02698687);
[published scan](https://www.numdam.org/item/PMIHES_1981__53__53_0.pdf).
The polynomial-growth equivalence remains an explicit input. Section 6's
common compact embedding theorem is now proved in `MetricGeometry.CommonEmbedding`,
including arbitrary indexed families and noncomplete spaces.

**Emmanuel Breuillard.** *Geometry of locally compact groups of polynomial
growth and shape of large balls.* Groups, Geometry, and Dynamics
**8** (2014), 669–732.
[DOI](https://doi.org/10.4171/GGD/244);
[published PDF](https://ems.press/content/serial-article-files/29707).
Theorem 1.1's volume asymptotics give the uniform volume and packing bounds.
The resulting matching-bounds theorem is an explicit black box on `main`.
Partial normalization and finite-group proofs are isolated on the local
`research/polynomial-volume` branch; the general theorem remains unformalized.

**Joseph A. Wolf.** *Growth of finitely generated solvable groups and
curvature of Riemannian manifolds.* Journal of Differential Geometry
**2** (1968), no. 4, 421–446.
[DOI](https://doi.org/10.4310/jdg/1214428658);
[author-hosted scan](https://math.berkeley.edu/~jawolf/publications.pdf/paper_033.pdf).
An antecedent for the classical polynomial-growth direction for finitely
generated virtually nilpotent groups, distinct from Gromov's converse.

**Alexander S. Kechris, Sławomir Solecki, and Stevo Todorcevic.**
*Borel chromatic numbers.* Advances in Mathematics **141** (1999),
no. 1, 1–44.
[DOI](https://doi.org/10.1006/aima.1998.1771).
Source for the Borel maximal-independent-set and bounded-degree coloring
constructions now proved in `BorelToolkit.Graph`. The reusable version
states measurable neighborhoods explicitly; the finite-action adapter
verifies that hypothesis directly.

**Alexander S. Kechris and Andrew S. Marks.** *Descriptive Graph
Combinatorics.* Preliminary version, October 9, 2020.
[Author-hosted survey](https://math.berkeley.edu/~marks/papers/combinatorics20book.pdf).
Propositions 4.9 and 5.4 corroborate the seeded maximal-extension and
bounded-degree coloring formulations and identify their KST sources.

**Kazimierz Kuratowski and Czesław Ryll-Nardzewski.** *A general theorem
on selectors.* Bulletin de l'Académie Polonaise des Sciences, Série des
Sciences Mathématiques, Astronomiques et Physiques **13** (1965), 397–403.
The successive-approximation selection theorem is formalized in
`BorelToolkit.ClosedSelection`, for arbitrary measurable parameter spaces
and nonempty closed values in a complete separable metric target.
Kuratowski's primary-author conference statement,
[*On discontinuous selectors*](https://dml.cz/bitstream/handle/10338.dmlcz/700857/Toposym_02-1966-1_55.pdf),
states the weak-measurability formulation and identifies the joint paper.
That statement was inspected; direct inspection of the 1965 full paper
is not claimed.

**Alexander S. Kechris.** *Classical Descriptive Set Theory.*
Graduate Texts in Mathematics **156**, Springer, 1995.
[Book DOI](https://doi.org/10.1007/978-1-4612-4190-4).
Chapters 12 and 18 cover standard selection and uniformization, including
Kuratowski–Ryll-Nardzewski and Arsenin–Kunugui. The former selector is now
proved here, as is the compact-section projection consequence of the latter.
The proof of projection follows the more explicit source listed next.

**Urs Lang.** *Notes on Rectifiability.* Course notes, version of
December 15, 2023.
[Author-hosted PDF](https://people.math.ethz.ch/~lang/rect_notes.pdf).
Theorem 1.3 presents the coordinated-net distance-embedding proof, following
Gromov's original argument. This is the construction formalized here;
it yields simultaneous exact embeddings, not just a convergent subsequence.

**S. M. Srivastava.** *A Course on Borel Sets.* Graduate Texts in Mathematics
**180**, Springer, 1998.
[University-hosted PDF](https://eclass.uoa.gr/modules/document/file.php/MATH305/%CE%92%CE%BF%CE%B7%CE%B8%CE%B7%CF%84%CE%B9%CE%BA%CF%8C%20%CF%85%CE%BB%CE%B9%CE%BA%CF%8C/SynolaBorel.pdf).
Theorem 4.6.1 is Novikov's countable separation theorem; the proof is
credited there to Mokobodzki. Theorem 4.7.1 is attributed to Saint Raymond,
and Theorem 4.7.2 is the Kunugui–Novikov open-section rectangle decomposition.
Theorem 4.7.11 and its alternative proof give compact-section projection,
using a Hilbert-cube embedding and finite subcovers. These exact proofs
were inspected for the new Borel toolkit modules. This does not claim a
formalization of the full sigma-compact-section Arsenin–Kunugui theorem.

## Lean and mathlib

**The mathlib Community.** *The Lean Mathematical Library.*
Proceedings of the 9th ACM SIGPLAN International Conference on Certified
Programs and Proofs (CPP 2020), ACM, 2020.
[DOI](https://doi.org/10.1145/3372885.3373824).
This is mathlib's requested scholarly citation.

The project uses
[mathlib v4.29.1](https://github.com/leanprover-community/mathlib4/tree/5e932f97dd25535344f80f9dd8da3aab83df0fe6)
and [Lean 4.29.1](https://github.com/leanprover/lean4/tree/v4.29.1).
Their developers retain authorship of the library results, including:

- Fekete's lemma in
  [Analysis/Subadditive.lean](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/Analysis/Subadditive.lean)
  (file author: Sébastien Gouëzel).
- The first Borel–Cantelli lemma in
  [OuterMeasure/BorelCantelli.lean](https://github.com/leanprover-community/mathlib4/blob/5e932f97dd25535344f80f9dd8da3aab83df0fe6/Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean).
- Compactness, measure subadditivity, finite-set cardinality estimates,
  logarithmic/exponential inequalities, and `Group.IsVirtuallyNilpotent`.
- Measurable injections of countably separated spaces into Cantor space
  in `MeasureTheory/MeasurableSpace/CountablyGenerated.lean`, measurable
  least witnesses, geometric Cauchy estimates, complete-space limits,
  and measurability of metric-valued pointwise limits. These library
  theorems underlie the new toolkit proofs.
- Lusin separation, analytic images, Lusin–Souslin and compatible Polish
  topologies in `MeasureTheory/Constructions/Polish/Basic.lean`
  (file authors Sébastien Gouëzel and Felix Weilacher). The new countable
  separation proof adapts its cylinder-refinement construction.
- Hilbert-cube embeddings in `Topology/MetricSpace/PiNat.lean`.
- The distance-coordinate proof in `Topology/MetricSpace/Kuratowski.lean`
  (Sébastien Gouëzel) and finite-discretization proof in
  `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
  (Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth).
  The common-embedding formalization adapts these proof patterns and uses
  mathlib's bounded-function metric and completeness results. Adapted
  portions retain copyright attribution in the relevant Lean headers.

The whole-project diagnostic uses Lean's `collectAxioms` implementation,
attributed in Lean to Leonardo de Moura / Microsoft Corporation. Its use
is also illustrated by mathlib's `assert_no_sorry` command (file author:
David Renshaw). The diagnostic adds no mathematical assumption.

## This repository

Research direction and maintenance: **Konstantin Slutsky**.
See [AUTHORS.md](AUTHORS.md) for contributions and
[ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md) for substantial AI assistance.
Cite this repository at the exact commit used, using
[CITATION.cff](CITATION.cff). This does not replace citation of the
mathematical antecedents and software dependencies. Citations imply
no endorsement or certification of novelty.
