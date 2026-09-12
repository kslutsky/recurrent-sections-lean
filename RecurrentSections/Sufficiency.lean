/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.Recentering
import RecurrentSections.FiniteColorAssembly
import RecurrentSections.Characterization

namespace RecurrentSections

open MeasureTheory

variable {G : Type} [Group G] [DecidableEq G]

/-- The full positive recurrence construction, relative to explicitly
stated standard geometric, selection, and Borel graph theorems. No
recurrence or invariant-recentering assertion is an input. -/
theorem universalRecurrence_of_polynomialGrowth (W : WordGeometry G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W)
    (hpoly : PolynomialGrowth W.volume) : UniversalRecurrence W := by
  classical
  intro X _ _ _ _ r hr hrpos
  obtain ⟨M, hM, hpack⟩ := geometry.packing hpoly
  obtain ⟨K, metric, hmodel⟩ := geometry.models hpoly r hr hrpos
  let := metric
  obtain ⟨compact, φ, hφ⟩ := hmodel
  let := compact
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : Nonempty K := ⟨φ 0 1⟩
  have hinit (n : ℕ) := tools.extension X (r n) ∅ MeasurableSet.empty
    (by intro x hx; simp at hx)
  choose A _ hAm hAs hnet using hinit
  obtain ⟨choice⟩ := tools.compactChoice (K × K)
  let T (x : X) := returnCluster W r φ A x
  have hTc (x : X) : IsCompact (T x) := returnCluster_compact W r φ A x
  have hTn (x : X) : (T x).Nonempty := returnCluster_nonempty W r hrpos φ hφ A hnet x
  have hTm : MeasurableSet {p : X × (K × K) | p.2 ∈ T p.1} :=
    measurableSet_returnCluster_graph W r φ A hAm
  let f (x : X) : K × K := choice.select (T x)
  have hfm : Measurable f := choice.measurable X T hTc hTn hTm
  have hfi (g : G) (x : X) : f (g • x) = f x :=
    congrArg choice.select (returnCluster_smul W r hr hrpos φ hφ A g x)
  have hfs (x : X) : f x ∈ returnCluster W r φ A x := choice.mem (T x) (hTc x) (hTn x)
  have hnearest (n : ℕ) := tools.finiteNearest K (W.ball (3 * r n))
    ⟨1, W.one_mem_ball _⟩ (φ n)
  choose h hm hb hmin using hnearest
  let H (n : ℕ) (x : X) : G := h n (f x).2
  have hHm (n : ℕ) (g : G) : MeasurableSet {x : X | H n x = g} :=
    (hm n g).preimage hfm.snd
  have hHi (n : ℕ) (g : G) (x : X) : H n (g • x) = H n x := by
    simp only [H, hfi]
  have hHb (n : ℕ) (x : X) : H n x ∈ W.ball (3 * r n) := hb n (f x).2
  let D := recentered H A
  have hDm (n : ℕ) : MeasurableSet (D n) :=
    measurableSet_variable_translate W (H n) (hHm n) (A n) (hAm n)
  have hDr : Recurrent W r D := recentered_recurrent W r hrpos φ hφ A f hfs H hHi hHb
    (fun n x g hg => hmin n (f x).2 g hg)
  have hDb (n : ℕ) : LocalMultiplicity W (r n) M (D n) :=
    recentered_multiplicity W (r n) M (hrpos n) hpack (H n) (hHi n) (hHb n) (A n) (hAs n)
  have hcolor (n : ℕ) := tools.coloring X (r n) M hM (D n) (hDm n) (hDb n)
  choose C hCm hCs hcover using hcolor
  have hCr : Recurrent W r (fun n => ⋃ i, C n i) := by
    simpa only [← hcover] using hDr
  exact finite_color_assembly W tools r hr M hM (fun i n => C n i)
    (fun i n => hCm n i) (fun i n => hCs n i) hCr

theorem positiveConstruction_of_standardInputs (W : WordGeometry G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W) :
    PositiveConstruction W := universalRecurrence_of_polynomialGrowth W geometry tools

/-- Virtual nilpotence implies prescribed-radius recurrence in every Borel
action, with arbitrary stabilizers, using only the listed standard inputs. -/
theorem universalRecurrence_of_virtuallyNilpotent (W : WordGeometry G)
    (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W)
    (hnil : Group.IsVirtuallyNilpotent G) : UniversalRecurrence W :=
  universalRecurrence_of_polynomialGrowth W geometry tools (gromov.mpr hnil)

/-- The complete characterization relative to the permitted standard
inputs. There is no positive-construction or recurrence hypothesis. -/
theorem recurrence_iff_virtuallyNilpotent (W : WordGeometry G)
    (gromov : PolynomialGrowth W.volume ↔ Group.IsVirtuallyNilpotent G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W) :
    UniversalRecurrence W ↔ Group.IsVirtuallyNilpotent G :=
  recurrence_iff_virtuallyNilpotent_of_positive W gromov
    (positiveConstruction_of_standardInputs W geometry tools)

theorem recurrence_iff_polynomialGrowth (W : WordGeometry G)
    (geometry : PolynomialGeometry W) (tools : StandardBorelTools W) :
    UniversalRecurrence W ↔ PolynomialGrowth W.volume :=
  ⟨polynomialGrowth_of_universalRecurrence W,
    universalRecurrence_of_polynomialGrowth W geometry tools⟩

end RecurrentSections
