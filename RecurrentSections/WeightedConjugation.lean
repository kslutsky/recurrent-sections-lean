/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.WeightedWords

namespace RecurrentSections
open scoped Pointwise commutatorElement
open WeightedWords
variable {G : Type*} [Group G] [DecidableEq G] {c : ℕ}

/-- Conjugation by at most `L R^i` letters of weight `i` sends a fixed
letter of weight `j` to a weighted word of cost `O(R^(c-j))`. The finite
output alphabet is independent of both `L` and `R`. -/
theorem exists_weighted_conjugation_bound (F : CentralFiltration G c)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (S A : Finset G) (hS : ∀ s ∈ S, s ∈ F.level i) (hA : ∀ a ∈ A, a ∈ F.level j) :
    ∃ B : Finset (G × ℕ), F.Valid j B ∧
      ∀ L : ℕ, ∃ D : ℕ, ∀ R : ℕ, 0 < R → ∀ m g, g ∈ S ^ m → m ≤ L * R ^ i →
        ∀ a ∈ A, Rep B c R (D * R ^ (c - j)) (g * a * g⁻¹) := by
  classical
  have hmain : ∀ d j : ℕ, c + 1 - j = d → 0 < j →
      ∀ A : Finset G, (∀ a ∈ A, a ∈ F.level j) →
      ∃ B : Finset (G × ℕ), F.Valid j B ∧
        ∀ L : ℕ, ∃ D : ℕ, ∀ R : ℕ, 0 < R → ∀ m g, g ∈ S ^ m → m ≤ L * R ^ i →
          ∀ a ∈ A, Rep B c R (D * R ^ (c - j)) (g * a * g⁻¹) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hd hj A hA
      by_cases hjc : c < j
      · refine ⟨∅, by simp [CentralFiltration.Valid], fun L => ⟨0, ?_⟩⟩
        intro R hR m g hg hm a ha
        have ha1 := F.eq_one_of_mem hjc (hA a ha)
        simpa [ha1] using (Rep.one (∅ : Finset (G × ℕ)) c R 0)
      have hjle : j ≤ c := by omega
      let A' : Finset (G × ℕ) := A.image (fun a => (a, j))
      have hA' : F.Valid j A' := by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
        exact ⟨le_rfl, hjle, hA b hb⟩
      have hletter (R : ℕ) (a : G) (ha : a ∈ A) : Rep A' c R (R ^ (c - j)) a :=
        Rep.letter (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      by_cases hij : c < i + j
      · have hcomm (s : G) (hs : s ∈ S) (a : G) (ha : a ∈ A) : s * a * s⁻¹ = a := by
          have hh : ⁅s, a⁆ = 1 := F.eq_one_of_mem hij
            (F.commutator_le i j hi hj (Subgroup.commutator_mem_commutator (hS s hs) (hA a ha)))
          have he : s * a * s⁻¹ = ⁅s, a⁆ * a := by group
          simpa [hh] using he
        have hconj : ∀ m g, g ∈ S ^ m → ∀ a ∈ A, g * a * g⁻¹ = a := by
          intro m
          induction m with
          | zero =>
            intro g hg a ha
            have hg1 : g = 1 := by simpa using hg
            simp [hg1]
          | succ m hm =>
            intro g hg a ha
            rw [pow_succ] at hg
            obtain ⟨u, hu, s, hs, rfl⟩ := Finset.mem_mul.mp hg
            calc
              u * s * a * (u * s)⁻¹ = u * (s * a * s⁻¹) * u⁻¹ := by group
              _ = a := by rw [hcomm s hs a ha, hm u hu a ha]
        refine ⟨A', hA', fun L => ⟨1, ?_⟩⟩
        intro R hR m g hg hm a ha
        simpa only [one_mul, hconj m g hg a ha] using hletter R a ha
      have hijle : i + j ≤ c := by omega
      let E : Finset G := (S ×ˢ A).image (fun p => ⁅p.1, p.2⁆)
      have hE : ∀ e ∈ E, e ∈ F.level (i + j) := by
        intro e he
        obtain ⟨⟨s, a⟩, hsa, rfl⟩ := Finset.mem_image.mp he
        exact F.commutator_le i j hi hj (Subgroup.commutator_mem_commutator
          (hS s (Finset.mem_product.mp hsa).1) (hA a (Finset.mem_product.mp hsa).2))
      obtain ⟨B, hB, hBC⟩ := ih (c + 1 - (i + j)) (by omega) (i + j) rfl (by omega) E hE
      refine ⟨A' ∪ B, hA'.union (hB.weaken (by omega)), fun L => ?_⟩
      obtain ⟨D, hD⟩ := hBC L
      refine ⟨1 + L * D, fun R hR => ?_⟩
      have hrec : ∀ m g, g ∈ S ^ m → m ≤ L * R ^ i → ∀ a ∈ A,
          Rep (A' ∪ B) c R (R ^ (c - j) + m * D * R ^ (c - (i + j))) (g * a * g⁻¹) := by
        intro m
        induction m with
        | zero =>
          intro g hg hm a ha
          have hg1 : g = 1 := by simpa using hg
          simpa [hg1] using (hletter R a ha).alphabet_mono Finset.subset_union_left
        | succ m hm =>
          intro g hg hml a ha
          rw [pow_succ] at hg
          obtain ⟨u, hu, s, hs, rfl⟩ := Finset.mem_mul.mp hg
          have hml' : m ≤ L * R ^ i := by omega
          have he : ⁅s, a⁆ ∈ E := Finset.mem_image.mpr
            ⟨(s, a), Finset.mem_product.mpr ⟨hs, ha⟩, rfl⟩
          have h₁ := (hD R hR m u hu hml' ⁅s, a⁆ he).alphabet_mono
            (Finset.subset_union_right (s₁ := A'))
          have h₂ := hm u hu hml' a ha
          have hx := h₁.mul h₂
          have heq : (u * ⁅s, a⁆ * u⁻¹) * (u * a * u⁻¹) =
              u * s * a * (u * s)⁻¹ := by group
          rw [heq] at hx
          convert hx using 1
          ring
      intro m g hg hm a ha
      apply (hrec m g hg hm a ha).mono
      calc
        R ^ (c - j) + m * D * R ^ (c - (i + j))
            ≤ R ^ (c - j) + (L * R ^ i) * D * R ^ (c - (i + j)) := by gcongr
        _ = (1 + L * D) * R ^ (c - j) := by
          have hex : i + (c - (i + j)) = c - j := by omega
          have hp : R ^ i * R ^ (c - (i + j)) = R ^ (c - j) := by rw [← pow_add, hex]
          calc
            _ = R ^ (c - j) + L * D * (R ^ i * R ^ (c - (i + j))) := by ring
            _ = _ := by rw [hp]; ring
  exact hmain (c + 1 - j) j rfl hj A hA

end RecurrentSections
