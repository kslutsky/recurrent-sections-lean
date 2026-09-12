/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import BorelToolkit.MeasureRestriction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.Action

/-! # Free probability-preserving Bernoulli actions

The classical atomless Bernoulli construction, for every countable group.
The coordinate independence and reindexing theorems used below are proved
in mathlib by Etienne Marion; no free-action existence theorem is assumed.
-/

namespace BorelToolkit

open MeasureTheory ProbabilityTheory

/-- Distinct coordinates of an atomless independent product are almost surely unequal. -/
theorem infinitePi_ae_ne {ι Y : Type*} [MeasurableSpace Y] [MeasurableEq Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] {i j : ι} (hij : i ≠ j) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ι => ν), x i ≠ x j := by
  have hind := (iIndepFun_infinitePi (P := fun _ : ι => ν)
    (X := fun _ => id) (fun _ => measurable_id)).indepFun hij
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp hind
  simp only [Measure.infinitePi_map_eval] at hmap
  have hdiag : (ν.prod ν) {p : Y × Y | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    have hzero (y : Y) : ν (Prod.mk y ⁻¹' {p : Y × Y | p.1 = p.2}) = 0 := by
      rw [show Prod.mk y ⁻¹' {p : Y × Y | p.1 = p.2} = {y} by
        ext z; simp [eq_comm]]
      exact measure_singleton y
    simp only [hzero, lintegral_zero]
  rw [ae_iff]
  simp only [not_not]
  change (Measure.infinitePi (fun _ : ι => ν)) {x | x i = x j} = 0
  have hm : MeasurableSet {p : Y × Y | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hp : Measurable (fun x : ι → Y => (x i, x j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have heq := Measure.map_apply (μ := Measure.infinitePi (fun _ : ι => ν)) hp hm
  exact heq.symm.trans ((congrArg (fun m : Measure (Y × Y) =>
    m {p | p.1 = p.2}) hmap).trans hdiag)

/-- Countably many atomless independent labels are almost surely pairwise distinct. -/
theorem infinitePi_ae_injective {ι Y : Type*} [Countable ι]
    [MeasurableSpace Y] [MeasurableEq Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ι => ν), Function.Injective x := by
  have h : ∀ i j : ι, ∀ᵐ x ∂Measure.infinitePi (fun _ : ι => ν), x i = x j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ _ => hij)
    · filter_upwards [infinitePi_ae_ne ν hij] with x hx heq
      exact (hx heq).elim
  simpa only [Function.Injective, ae_all_iff] using h

namespace Bernoulli

variable {G Y : Type*} [Group G]

/-- The left Bernoulli shift. -/
def shift (g : G) (x : G → Y) (h : G) : Y := x (g⁻¹ * h)

@[simp] theorem shift_one (x : G → Y) : shift 1 x = x := by ext; simp [shift]

theorem shift_mul (g h : G) (x : G → Y) : shift (g * h) x = shift g (shift h x) := by
  ext k
  simp [shift, mul_assoc]

/-- The actual free part: every orbit map is injective. -/
def freePart : Set (G → Y) := {x | Function.Injective (fun g => shift g x)}

theorem shift_mem_freePart (g : G) {x : G → Y} (hx : x ∈ freePart) :
    shift g x ∈ freePart := by
  intro a b hab
  apply mul_right_cancel (b := g)
  exact hx (by simpa only [shift_mul] using hab)

theorem injective_mem_freePart {x : G → Y} (hx : Function.Injective x) : x ∈ freePart := by
  intro g h heq
  have := hx (congrFun heq 1)
  simpa only [shift, mul_one, inv_inj] using this

variable [MeasurableSpace Y]

theorem measurable_shift (g : G) : Measurable (shift (Y := Y) g) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

variable [Countable G] [StandardBorelSpace Y]

theorem measurableSet_freePart : MeasurableSet (freePart (G := G) (Y := Y)) := by
  let := upgradeStandardBorel Y
  simp only [freePart, Function.Injective, Set.ofPred_forall]
  apply MeasurableSet.iInter fun g => MeasurableSet.iInter fun h => ?_
  by_cases heq : g = h
  · simp [heq]
  · simpa only [heq, imp_false, Set.compl_ofPred] using
      (measurableSet_eq_fun (measurable_shift g) (measurable_shift h)).compl

theorem ae_freePart (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : G => ν), x ∈ freePart := by
  let := upgradeStandardBorel Y
  exact (infinitePi_ae_injective ν).mono (fun _ => injective_mem_freePart)

/-- The standard Borel space underlying the free Bernoulli action. -/
def FreeSpace (G Y : Type*) [Group G] := {x : G → Y // x ∈ freePart}

instance : MeasurableSpace (FreeSpace G Y) :=
  inferInstanceAs (MeasurableSpace {x : G → Y // x ∈ freePart})

instance : StandardBorelSpace (FreeSpace G Y) := measurableSet_freePart.standardBorel

instance : MulAction G (FreeSpace G Y) where
  smul g x := ⟨shift g x.val, shift_mem_freePart g x.property⟩
  one_smul x := Subtype.ext (shift_one x.val)
  mul_smul g h x := Subtype.ext (shift_mul g h x.val)

instance : MeasurableConstSMul G (FreeSpace G Y) where
  measurable_const_smul g :=
    ((measurable_shift g).comp measurable_subtype_coe).subtype_mk

omit [MeasurableSpace Y] [Countable G] [StandardBorelSpace Y] in
theorem free (x : FreeSpace G Y) : Function.Injective (fun g : G => g • x) := by
  intro g h heq
  exact x.property (congrArg Subtype.val heq)

/-- The product measure, pulled back to its conull free part. -/
noncomputable def freeMeasure (ν : Measure Y) [IsProbabilityMeasure ν] :
    Measure (FreeSpace G Y) :=
  (Measure.infinitePi (fun _ : G => ν)).comap Subtype.val

instance (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    IsProbabilityMeasure (freeMeasure (G := G) ν) :=
  (MeasurableEmbedding.subtype_coe measurableSet_freePart).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe] using ae_freePart (G := G) ν)

omit [Countable G] [StandardBorelSpace Y] in
/-- Product measure is preserved by every Bernoulli shift. -/
theorem measurePreserving_shift (ν : Measure Y) [IsProbabilityMeasure ν] (g : G) :
    MeasurePreserving (shift (Y := Y) g) (Measure.infinitePi (fun _ : G => ν))
      (Measure.infinitePi (fun _ : G => ν)) := by
  refine ⟨measurable_shift g, ?_⟩
  convert! Measure.infinitePi_map_piCongrLeft (fun _ : G => ν) (Equiv.mulLeft g) using 1
  congr 1
  funext x h
  simp [shift, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

instance (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    SMulInvariantMeasure G (FreeSpace G Y) (freeMeasure ν) where
  measure_preimage_smul g s hs := by
    have hp := measurePreserving_restrict_conull (measurePreserving_shift ν g)
      measurableSet_freePart (ae_freePart ν) (fun _ => shift_mem_freePart g)
    exact hp.measure_preimage hs.nullMeasurableSet

end Bernoulli
end BorelToolkit
