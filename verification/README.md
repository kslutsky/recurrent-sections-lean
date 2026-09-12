# Verification record

The current sources were checked on September 11, 2026
with Lean 4.33.0-rc2 and the exact dependency revisions in `lake-manifest.json`.
[verification.json](verification.json) records the platform, time, all ten
dependency revisions, and SHA-256 hashes of the 45 checked Lean source files,
configuration files, and verification script.

This is the `research/polynomial-volume` branch. It includes the partial
volume proofs, the completed Bernoulli work merged from main, the proved Gromov forward implication, and matching volume bounds for abelian groups. The current project has 40 modules in three libraries, three root imports,
and two audit drivers. The initial fifteen proof modules were built from
scratch when the standalone directory was created. The present run builds
all targets and checks the new modules and their dependents. The pinned
mathlib dependency cache is reused; mathlib is not rebuilt from scratch.
Aaron Hill's Gromov dependency was built locally from its pinned source
before integration. Its unchanged upstream deprecation and style warnings
are recorded in the build log; this project's warnings remain errors.

The command was:

```sh
python3 scripts/check.py --record
```

It passed all of these checks:

| Check | Evidence |
|---|---|
| Every module in all three libraries is reachable from the root import; no forbidden proof shortcut | Source/import guard |
| Reusable libraries do not import `RecurrentSections` | Import-boundary guard |
| All ten dependencies match their pinned revisions, with no tracked modifications | Dependency check |
| Build with project warnings treated as errors: 8813 build jobs | [build-output.txt](build-output.txt) |
| Signatures and logical dependencies of 77 principal results | [audit-output.txt](audit-output.txt) |
| All 563 library declarations use only allowed logical axioms, including private declarations | [all-axioms-output.txt](all-axioms-output.txt) |
| An axiom injected into the new `BorelToolkit` namespace is rejected | [negative-control-output.txt](negative-control-output.txt) |

The error in the negative-control log is intentional and required for the
test to pass. Its temporary Lean source is generated inside the ignored
`.lake/` tree; it is not part of the mathematical library. The audit also
rejects a missing library, so omitting all its imports cannot pass vacuously.

The allowed logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. The diagnostic traverses compiled declarations using Lean's
`collectAxioms` API. Explicit mathematical hypotheses remain visible in
the signatures and are documented in
[STANDARD_INPUTS.md](../STANDARD_INPUTS.md). Common compact embedding and
compact-section projection now have proved inhabitants with no external
theorem parameters. The Gromov forward implication is now proved using Hill's development.
The full virtual-nilpotence characterization still requires the explicit
nilpotent matching-volume estimate; no inhabitant of that general input
is claimed. The finite and abelian cases and finite-index comparisons
are proved. The Bernoulli test action is now proved and is no
longer a theorem parameter, including in the subexponential corollary.

## Earlier separate consumer-package check (Lean 4.29.1)

Before the toolchain migration, a separate Lake package was created under the ignored verification tree,
using a local path dependency on this package. It shared the pinned
mathlib cache, but had its own manifest and consumer module. Running
`lake build --wfail` completed successfully with 3414 jobs. Its complete
consumer module was:

```lean
import BorelToolkit.Bernoulli
import BorelToolkit.Graph
import BorelToolkit.FiniteSelection
import BorelToolkit.ClosedSelection
import MetricGeometry.FiniteNets
import MetricGeometry.CommonEmbedding
import BorelToolkit.CompactProjection

example (x : ℝ) : BorelToolkit.closedSelector ({x} : Set ℝ) = x := by simp

example {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
    (g : SimpleGraph X) (hm : BorelToolkit.MeasurableNeighborhoods g)
    (hf : ∀ x, (g.neighborSet x).Finite) :
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, g.IsIndepSet (C n)) ∧ (⋃ n, C n) = Set.univ :=
  BorelToolkit.exists_countable_independent_cover g hm hf

example {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (R : Set (X × ℝ)) (hR : MeasurableSet R)
    (hc : ∀ x, IsCompact {y | (x, y) ∈ R}) :
    MeasurableSet {x | ∃ y, (x, y) ∈ R} :=
  BorelToolkit.measurableSet_proj_of_compact_sections R hR hc

example {ι : Type*} (A : ι → Type*) [∀ i, MetricSpace (A i)]
    (hne : ∀ i, Nonempty (A i))
    (hb : ∃ C : ℝ, ∀ i (x y : A i), dist x y ≤ C)
    (hc : MetricGeometry.UniformlyCoverable A) :
    ∃ (K : Type) (m : MetricSpace K), letI := m
      CompactSpace K ∧ ∃ f : ∀ i, A i → K, ∀ i, Isometry (f i) :=
  MetricGeometry.exists_common_compact_embedding A hne hb hc

example {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure ν]
    [MeasureTheory.NoAtoms ν] :
    StandardBorelSpace (BorelToolkit.Bernoulli.FreeSpace G Y) ∧
      MeasureTheory.IsProbabilityMeasure (BorelToolkit.Bernoulli.freeMeasure (G := G) ν) ∧
      MeasureTheory.SMulInvariantMeasure G (BorelToolkit.Bernoulli.FreeSpace G Y)
        (BorelToolkit.Bernoulli.freeMeasure ν) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

example {G Y : Type*} [Group G] (x : BorelToolkit.Bernoulli.FreeSpace G Y) :
    Function.Injective (fun g : G => g • x) := BorelToolkit.Bernoulli.free x
```

That historical check verified use through a dependency without importing the recurrence
application, including a countably separated graph parameter space without
a standard Borel assumption, compact-section projection without a supplied
projection theorem, and arbitrary-index common embeddings without compactness
of the individual spaces. It also verified the free Bernoulli action
for an arbitrary countable group and atomless standard Borel probability
base, using the probability and invariance instances without importing
the recurrence application. [TOOLS.md](../TOOLS.md) gives the dependency
configuration. Source hashes and the then-nine dependency revisions were
rechecked after that consumer build and matched. The example uses the old
name `NoAtoms`; Lean 4.33 uses `NullSingletonClass`. This consumer check has
not yet been repeated for the new toolchain.

## Hosted and human review status

[The GitHub workflow](../.github/workflows/lean.yml) invokes the same script.
The logs above record local verification. Hosted runs for pushed commits
are listed in [GitHub Actions](https://github.com/kslutsky/recurrent-sections-lean/actions);
consult the run for the exact commit being used. The
[run for `dbd0f02`](https://github.com/kslutsky/recurrent-sections-lean/actions/runs/34608517395)
passed; it includes the geometric and Borel tools but predates the Bernoulli
addition recorded here. Refresh the local evidence with `--record`
after changing checked sources. The previous three AI reviews cover the initial snapshot, not
these additions. No new separate-agent or outside human review is claimed.
