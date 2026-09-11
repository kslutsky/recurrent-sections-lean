/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-! # Measurable independent sets and graph colorings

The graph API uses mathlib's `SimpleGraph`. The measurability hypothesis
is that taking graph neighbors preserves measurable sets. Finite or
countable families of measurable maps give this property directly;
arbitrary locally countable Borel graphs need the Lusin--Novikov theorem
to establish it. No uniformization theorem is silently assumed here.

The constructions follow the standard arguments of Kechris--Solecki--
Todorcevic; see REFERENCES.md. No group action or recurrence is involved.
-/

namespace BorelToolkit

open Set MeasurableSpace

variable {X : Type*} [MeasurableSpace X]

/-- Open graph neighborhood of a set; it need not contain the set. -/
def neighbors (g : SimpleGraph X) (S : Set X) : Set X :=
  {x | ∃ y ∈ S, g.Adj x y}

/-- The measurable-neighborhood hypothesis is useful even without
local finiteness, and is kept separate from that combinatorial condition. -/
def MeasurableNeighborhoods (g : SimpleGraph X) : Prop :=
  ∀ S : Set X, MeasurableSet S → MeasurableSet (neighbors g S)

omit [MeasurableSpace X] in
theorem neighbors_mono (g : SimpleGraph X) {S T : Set X} (h : S ⊆ T) :
    neighbors g S ⊆ neighbors g T := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, h hy, hxy⟩

/-- Every locally finite graph with measurable neighborhoods on a
countably separated measurable space has a countable measurable
independent cover. Standard Borelness is not required. -/
theorem exists_countable_independent_cover [CountablySeparated X]
    (g : SimpleGraph X) (hg : MeasurableNeighborhoods g)
    (hfinite : ∀ x, (g.neighborSet x).Finite) :
    ∃ C : ℕ → Set X, (∀ n, MeasurableSet (C n)) ∧
      (∀ n, g.IsIndepSet (C n)) ∧ (⋃ n, C n) = univ := by
  classical
  obtain ⟨f, hfm, hfi⟩ := measurable_injection_nat_bool_of_countablySeparated X
  let Code := Σ n : ℕ, Fin n → Bool
  letI : Encodable Code := Encodable.ofCountable Code
  let U (c : Code) : Set X := {x | ∀ i : Fin c.1, f x i = c.2 i}
  let A (c : Code) := U c \ neighbors g (U c)
  have hUm (c : Code) : MeasurableSet (U c) := by
    simp only [U, setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq_fun ((measurable_pi_apply (i : ℕ)).comp hfm) measurable_const
  have hAm (c : Code) : MeasurableSet (A c) := (hUm c).diff (hg _ (hUm c))
  have hAi (c : Code) : g.IsIndepSet (A c) := by
    intro x hx y hy _ hxy
    exact hx.2 ⟨y, hy.1, hxy⟩
  have hAc (x : X) : ∃ c : Code, x ∈ A c := by
    letI : Fintype (g.neighborSet x) := (hfinite x).fintype
    have hdist (y : g.neighborSet x) : ∃ n, f x n ≠ f y n := by
      by_contra! h
      have : x = y := hfi (funext h)
      exact g.ne_of_adj y.2 this
    choose k hk using hdist
    let n := Finset.univ.sup k + 1
    let c : Code := ⟨n, fun i => f x i⟩
    refine ⟨c, ⟨fun _ => rfl, ?_⟩⟩
    rintro ⟨y, hy, hxy⟩
    let z : g.neighborSet x := ⟨y, hxy⟩
    have hkn : k z < n := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ z))
    exact hk z (hy ⟨k z, hkn⟩).symm
  let C (n : ℕ) : Set X := match Encodable.decode (α := Code) n with
    | none => ∅
    | some c => A c
  refine ⟨C, ?_, ?_, ?_⟩
  · intro n
    dsimp only [C]
    cases Encodable.decode (α := Code) n with
    | none => exact MeasurableSet.empty
    | some c => exact hAm c
  · intro n
    dsimp only [C]
    cases Encodable.decode (α := Code) n with
    | none => simp [SimpleGraph.IsIndepSet]
    | some c => exact hAi c
  · apply eq_univ_of_forall
    intro x
    obtain ⟨c, hc⟩ := hAc x
    exact mem_iUnion.mpr ⟨Encodable.encode c, by simpa [C] using hc⟩

/-- A measurable independent seed extends inside any measurable domain
to an independent set dominating that domain. Only a countable measurable
independent cover and measurable neighborhoods are needed. -/
theorem exists_maximal_extension_of_cover (g : SimpleGraph X)
    (hg : MeasurableNeighborhoods g) (C : ℕ → Set X)
    (hCm : ∀ n, MeasurableSet (C n)) (hCi : ∀ n, g.IsIndepSet (C n))
    (hCc : (⋃ n, C n) = univ) (D S : Set X)
    (hDm : MeasurableSet D) (hSm : MeasurableSet S)
    (hSD : S ⊆ D) (hSi : g.IsIndepSet S) :
    ∃ A : Set X, S ⊆ A ∧ A ⊆ D ∧ MeasurableSet A ∧ g.IsIndepSet A ∧
      ∀ x ∈ D, x ∈ A ∨ ∃ y ∈ A, g.Adj x y := by
  let stage : ℕ → Set X := Nat.rec S (fun n A => A ∪ ((D ∩ C n) \ neighbors g A))
  have hzero : stage 0 = S := rfl
  have hstep (n : ℕ) : stage (n + 1) =
      stage n ∪ ((D ∩ C n) \ neighbors g (stage n)) := rfl
  have hmono : Monotone stage := monotone_nat_of_le_succ fun n => by
    rw [hstep]; exact subset_union_left
  have hst (n : ℕ) : stage n ⊆ D ∧ MeasurableSet (stage n) ∧
      g.IsIndepSet (stage n) := by
    induction n with
    | zero => exact ⟨hSD, hSm, hSi⟩
    | succ n ih =>
      rw [hstep]
      refine ⟨union_subset ih.1 (fun _ hx => hx.1.1),
        ih.2.1.union ((hDm.inter (hCm n)).diff (hg _ ih.2.1)), ?_⟩
      intro x hx y hy hxy hadj
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact ih.2.2 hx hy hxy hadj
      · exact hy.2 ⟨x, hx, hadj.symm⟩
      · exact hx.2 ⟨y, hy, hadj⟩
      · exact hCi n hx.1.2 hy.1.2 hxy hadj
  let A := ⋃ n, stage n
  have hsub (n : ℕ) : stage n ⊆ A := subset_iUnion stage n
  refine ⟨A, hsub 0, iUnion_subset (fun n => (hst n).1),
    MeasurableSet.iUnion (fun n => (hst n).2.1), ?_, ?_⟩
  · intro x hx y hy hxy hadj
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    exact (hst (max i j)).2.2 (hmono (le_max_left i j) hi)
      (hmono (le_max_right i j) hj) hxy hadj
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hCc.symm ▸ mem_univ x)
    by_cases h : x ∈ neighbors g (stage n)
    · obtain ⟨y, hy, hxy⟩ := h
      exact Or.inr ⟨y, hsub n hy, hxy⟩
    · exact Or.inl (hsub (n + 1) (Or.inr ⟨⟨hx, hn⟩, h⟩))

/-- The locally finite, countably separated version of seeded measurable
maximal independent-set extension. -/
theorem exists_maximal_extension [CountablySeparated X]
    (g : SimpleGraph X) (hg : MeasurableNeighborhoods g)
    (hfinite : ∀ x, (g.neighborSet x).Finite) (D S : Set X)
    (hDm : MeasurableSet D) (hSm : MeasurableSet S)
    (hSD : S ⊆ D) (hSi : g.IsIndepSet S) :
    ∃ A : Set X, S ⊆ A ∧ A ⊆ D ∧ MeasurableSet A ∧ g.IsIndepSet A ∧
      ∀ x ∈ D, x ∈ A ∨ ∃ y ∈ A, g.Adj x y := by
  obtain ⟨C, hCm, hCi, hCc⟩ := exists_countable_independent_cover g hg hfinite
  exact exists_maximal_extension_of_cover g hg C hCm hCi hCc D S hDm hSm hSD hSi

/-- Closed graph neighborhood, restricted to a domain. Its cardinality
counts the vertex itself when that vertex belongs to the domain. -/
def closedNeighbors (g : SimpleGraph X) (D : Set X) (x : X) : Set X :=
  D ∩ insert x (g.neighborSet x)

/-- A closed-neighborhood bound of `M` gives `M` measurable independent
sets covering the domain. This is the usual degree-plus-one bound. -/
theorem exists_finite_independent_cover [CountablySeparated X]
    (g : SimpleGraph X) (hg : MeasurableNeighborhoods g)
    (hfinite : ∀ x, (g.neighborSet x).Finite) (M : ℕ)
    (D : Set X) (hDm : MeasurableSet D)
    (hbound : ∀ x ∈ D, (closedNeighbors g D x).ncard ≤ M) :
    ∃ C : Fin M → Set X, (∀ i, MeasurableSet (C i)) ∧
      (∀ i, g.IsIndepSet (C i)) ∧ D = ⋃ i, C i := by
  classical
  have hfin (D : Set X) (x : X) : (closedNeighbors g D x).Finite :=
    ((hfinite x).insert x).subset inter_subset_right
  induction M generalizing D with
  | zero =>
    have hD : D = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hpos : 0 < (closedNeighbors g D x).ncard :=
        ncard_pos (hfin D x) |>.mpr ⟨x, hx, mem_insert _ _⟩
      have := hbound x hx
      omega
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hD]⟩
  | succ M ih =>
    obtain ⟨A, _, hAD, hAm, hAi, hdom⟩ := exists_maximal_extension g hg hfinite D ∅
      hDm MeasurableSet.empty (empty_subset D) (by simp [SimpleGraph.IsIndepSet])
    have hred : ∀ x ∈ D \ A, (closedNeighbors g (D \ A) x).ncard ≤ M := by
      intro x hx
      obtain h | ⟨y, hy, hxy⟩ := hdom x hx.1
      · exact (hx.2 h).elim
      have hyout : y ∉ closedNeighbors g (D \ A) x := fun h => h.1.2 hy
      have hsub : insert y (closedNeighbors g (D \ A) x) ⊆ closedNeighbors g D x := by
        intro z hz
        rcases hz with rfl | hz
        · exact ⟨hAD hy, Or.inr hxy⟩
        · exact ⟨hz.1.1, hz.2⟩
      have hcard := (ncard_le_ncard hsub (hfin D x)).trans (hbound x hx.1)
      rw [ncard_insert_of_notMem hyout (hfin (D \ A) x)] at hcard
      omega
    obtain ⟨C, hCm, hCi, hCc⟩ := ih (D \ A) (hDm.diff hAm) hred
    refine ⟨Fin.cons A C, Fin.cases hAm hCm, Fin.cases hAi hCi, ?_⟩
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ A
      · exact mem_iUnion.mpr ⟨0, h⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp (hCc ▸ (show x ∈ D \ A from ⟨hx, h⟩))
        exact mem_iUnion.mpr ⟨i.succ, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine Fin.cases (fun hx => hAD hx) (fun j hx => ?_) i hi
      have : x ∈ D \ A := hCc.symm ▸ mem_iUnion.mpr ⟨j, hx⟩
      exact this.1

end BorelToolkit
