# Separate consumer-package check

The example package was located at `.lake/verification/consumer-4.33`; its [manifest](consumer-manifest.json) is recorded.

This package was built with Lean 4.33.0-rc2 on September 11, 2026 (local time). It has its own Lake configuration and manifest, a local path dependency on this project, and a shared cache of the same pinned dependencies. The toolkit module imports no recurrent-section application module. The volume module exercises the complete statements without theorem-input arguments.

Command: `LEAN_NUM_THREADS=2 lake build`. The build passed with 8835 jobs; see [consumer-build-output.txt](consumer-build-output.txt).

## lakefile.toml

```toml
name = "complete_volume_consumer"
defaultTargets = ["ToolkitConsumer", "VolumeConsumer"]

[leanOptions]
warningAsError = true

[[require]]
name = "recurrent_sections"
path = "../../.."

[[lean_lib]]
name = "ToolkitConsumer"

[[lean_lib]]
name = "VolumeConsumer"
```

## lean-toolchain

```text
leanprover/lean4:v4.33.0-rc2
```

## ToolkitConsumer.lean

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
    [MeasureTheory.NullSingletonClass ν] :
    StandardBorelSpace (BorelToolkit.Bernoulli.FreeSpace G Y) ∧
      MeasureTheory.IsProbabilityMeasure (BorelToolkit.Bernoulli.freeMeasure (G := G) ν) ∧
      MeasureTheory.SMulInvariantMeasure G (BorelToolkit.Bernoulli.FreeSpace G Y)
        (BorelToolkit.Bernoulli.freeMeasure ν) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

example {G Y : Type*} [Group G] (x : BorelToolkit.Bernoulli.FreeSpace G Y) :
    Function.Injective (fun g : G => g • x) := BorelToolkit.Bernoulli.free x
```

## VolumeConsumer.lean

```lean
import RecurrentSections.DerivedCharacterization

open RecurrentSections

example {G : Type} [Group G] [DecidableEq G] (W : WordGeometry G) :
    PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G :=
  polynomialGrowth_iff_virtuallyNilpotent W

example {G : Type} [Group G] [DecidableEq G] (W : WordGeometry G)
    (h : PolynomialGrowth W.volume) :
    ∃ C d : ℕ, 0 < C ∧ ∀ n,
      (n + 1) ^ d ≤ C * W.volume n ∧ W.volume n ≤ C * (n + 1) ^ d :=
  polynomialVolumeTheorem W h

example {G : Type} [Group G] [DecidableEq G] (W : WordGeometry G) :
    UniversalMaximalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  maximalRecurrence_iff_virtuallyNilpotent_of_standard_theorems W

example {G : Type} [Group G] [DecidableEq G] (W : WordGeometry G) :
    UniversalFreeRecurrence W ↔ PolynomialGrowth W.volume :=
  freeRecurrence_iff_polynomialGrowth_of_standard_theorems W
```
