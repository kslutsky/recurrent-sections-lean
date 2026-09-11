# Reusing the Borel toolkit

`BorelToolkit` is a separate Lean library in this Lake package. Its modules
import only mathlib and other toolkit modules. No group-growth or
recurrent-cross-section theorem is needed to use it. The definitions and
most theorems are universe-polymorphic.

For a sibling local checkout, add this dependency to your project's
`lakefile.toml`:

```toml
[[require]]
name = "recurrent_sections"
path = "../recurrent-sections-lean"
```

Use the package's pinned Lean/mathlib versions. For a Git dependency,
pin a commit containing these modules; the original `ae361f7` snapshot
predates them. Access to the private GitHub repository requires your
usual GitHub credentials.

## Import only what you need

```lean
import BorelToolkit.Graph
import BorelToolkit.ActionGraph
import BorelToolkit.FiniteSelection
import BorelToolkit.ClosedSelection
import BorelToolkit.CompactProjection
```

Each import works separately. `import BorelToolkit` includes the complete
toolkit, including the proved compact-section projection theorem.
The verification script rejects imports from `RecurrentSections` inside
the reusable libraries.

| Module | Main API | Hypotheses |
|---|---|---|
| `CountableSelection` | `firstWitness`, `measurable_firstWitness` | Measurable natural-number witness predicates; zero is returned on empty fibers |
| `FiniteSelection` | `exists_measurable_argmin`, `exists_finite_minimizer`, `exists_finite_nearest` | Finite nonempty candidate family; measurable pairwise cost comparisons, or continuous distance costs |
| `Graph` | `exists_countable_independent_cover` | Locally finite `SimpleGraph`, countably separated measurable space, measurable graph-neighborhood operation |
| `Graph` | `exists_maximal_extension_of_cover`, `exists_maximal_extension` | Measurable domain and independent seed inside it; a countable independent cover, or the preceding graph hypotheses |
| `Graph` | `exists_finite_independent_cover` | The preceding graph hypotheses; closed neighborhoods within the domain have at most `M` vertices |
| `ActionGraph` | `finiteActionGraph`, `finiteActionGraph_measurable` | Finite inverse-closed action family; measurable maps on a countably separated space; stabilizers allowed |
| `ClosedSelection` | `closedSelector_mem`, `measurable_closedSelector`, `exists_measurable_selection` | Nonempty complete separable metric target; nonempty weakly measurable values, closed for the membership conclusion |
| `AnalyticSeparation` | `analytic_countable_separation` | Countable analytic family with empty intersection; Hausdorff target with measurable opens |
| `OpenSections` | `exists_borel_open_rectangles` | Borel relation between Polish spaces with open vertical sections |
| `CompactProjectionProof` | `measurableSet_proj_of_compact_sections` | Standard Borel parameters; complete separable metric target; Borel relation with compact sections, possibly empty |
| `CompactProjection` | `weaklyMeasurable_of_compact_graph`, `measurable_closedSelector_of_compact_graph` | Compact-section Borel graph; nonempty values for selection |

All these results have **no unformalized mathematical inputs**. A Borel
graph and a weakly measurable family are different hypotheses; the proved
compact-section projection theorem now provides the required bridge.

## Graph API

The toolkit uses mathlib's `SimpleGraph X` and `g.IsIndepSet S`.

```text
neighbors g S = {x | there exists y in S with g.Adj x y}
MeasurableNeighborhoods g =
  for every measurable S, neighbors g S is measurable

closedNeighbors g D x = D ∩ insert x (g.neighborSet x)
```

Local finiteness is stated as `∀ x, (g.neighborSet x).Finite`.
Measurable maximal extension returns an independent set `A`, containing
the seed and contained in the domain `D`, such that each point of `D`
either belongs to `A` or has a neighbor in `A`. Hence it is maximal within
`D`, including among nonmeasurable independent supersets.

The coloring theorem returns a family `C : Fin M → Set X` of measurable
independent sets with `D = ⋃ i, C i`. The cardinality bound counts the
center; a degree bound of `d` therefore gives `d + 1` colors. Cardinalities
use `Set.ncard`, and finiteness is checked before its monotonicity is used.

For a finite family of group translations, `ActionGraph` proves the
measurable-neighborhood condition by a finite union of preimages, excluding
fixed points. It requires neither freeness nor countability of the group.

## Selection API

`exists_finite_minimizer` does not require any measurable structure on the
candidate type. It returns a function with measurable equality fibers,
values in the fixed finite candidate set, and the minimizing inequality.
`exists_measurable_argmin` instead uses a finite index type and returns
`Measurable f` directly. Both allow any linearly ordered cost type when
pairwise comparison sets are measurable.

`closedSelector : Set K → K` is one fixed function. Consequently, equality
of sets implies equality of selections without any equivariance assumption.
`WeaklyMeasurable T` means that the parameter set where `T(x)` meets any
given open set is measurable. For nonempty closed values in a complete
separable metric space, the two key conclusions are:

```text
closedSelector_mem : closedSelector T ∈ T
measurable_closedSelector : Measurable (fun x => closedSelector (T x))
```

The parameter space can be an arbitrary measurable space. Compactness of
the values is unnecessary here. Measurability of the limiting map actually
holds for nonempty values without closedness; closedness is used to prove
that the limit lies in the original set. The selector sends a singleton
to its unique point, as checked by `closedSelector_singleton`.

## Geometry modules and the application

`import MetricGeometry.FiniteNets` gives finite separated nets in any
pseudometric space, including radius zero. `import MetricGeometry.CommonEmbedding`
gives `exists_common_compact_embedding`: any indexed family of nonempty
metric spaces with uniformly bounded diameters and uniform finite covering
numbers embeds isometrically into one compact metric space. The individual
spaces need not be compact or complete. `CommonCompactEmbeddingTheorem`
is the older countable-family proposition, now inhabited by the proved
`commonCompactEmbeddingTheorem`.

The application adapters are in
[PolynomialGeometry.lean](RecurrentSections/PolynomialGeometry.lean) and
[BorelTools.lean](RecurrentSections/BorelTools.lean). They construct the
original interfaces: the geometry constructor still takes the general
polynomial-volume theorem, while `standardBorelTools W` takes no external
theorem. See [STANDARD_INPUTS.md](STANDARD_INPUTS.md). Neither is a dependency of
the reusable toolkit.

These are classical constructions, credited in
[REFERENCES.md](REFERENCES.md), with substantive AI-assisted formalization
disclosed in [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md). No first-formalization
or mathlib-upstream status is claimed.
