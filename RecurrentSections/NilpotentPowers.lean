/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2026 Konstantin Slutsky and contributors.
Developed with AI assistance; see ACKNOWLEDGEMENTS.md and AUTHORS.md.
-/

import RecurrentSections.PowerCompression
import RecurrentSections.LowerCentralCommutators

/-! # Compression in the last lower-central term

The discrete power argument follows Druţu--Kapovich, *Geometric Group
Theory*, 2017 author draft, Lemma 14.15 and Corollary 14.16, pp. 503--504:
https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf
The index need not be the minimal nilpotency class. Torsion is allowed.
Only the compression half of sharp distortion is proved here.
-/

namespace RecurrentSections
open scoped commutatorElement

variable {G : Type*} [Group G] [DecidableEq G]

theorem PowerCompression.one (W : WordGeometry G) (k : ℕ) : PowerCompression W 1 k := by
  exact ⟨0, fun r n hn => by simp [W.length_one]⟩

theorem PowerCompression.inv {W : WordGeometry G} {g : G} {k : ℕ}
    (h : PowerCompression W g k) : PowerCompression W g⁻¹ k := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun r n hn => by simpa only [inv_pow, W.length_inv] using hC r n hn⟩

theorem PowerCompression.mul {W : WordGeometry G} {g h : G} {k : ℕ}
    (hg : PowerCompression W g k) (hh : PowerCompression W h k) (hcomm : Commute g h) :
    PowerCompression W (g * h) k := by
  obtain ⟨C, hC⟩ := hg
  obtain ⟨D, hD⟩ := hh
  refine ⟨C + D, fun r n hn => ?_⟩
  rw [hcomm.mul_pow]
  exact (W.length_mul_le _ _).trans (by nlinarith [hC r n hn, hD r n hn])

/-- Every element in the last possibly nontrivial lower-central term has
power compression of the corresponding weight. The index need not be
minimal; the group may have torsion. -/
theorem powerCompression_of_last_lowerCentralSeries (c : ℕ)
    (W : WordGeometry G) (hc : (⊤ : Subgroup G).lowerCentralSeries (c + 1) = ⊥)
    {g : G} (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries c) :
    PowerCompression W g (c + 1) := by
  classical
  induction c generalizing G with
  | zero =>
    refine ⟨W.length g, fun r n hn => ?_⟩
    have hn' : n ≤ r := by simpa using hn
    exact (W.length_pow_le g n).trans (by nlinarith)
  | succ c ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (c + 1)
    have hN : N ≤ Subgroup.center G := by
      apply (Subgroup.commutator_top_right_eq_bot_iff_le_center).mp
      exact hc
    let f := QuotientGroup.mk' N
    let V := W.map f QuotientGroup.mk_surjective
    have htop : (⊤ : Subgroup G).map f = ⊤ :=
      Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective
    have hq : (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries (c + 1) = ⊥ := by
      rw [← htop, ← Subgroup.map_lowerCentralSeries, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
    change g ∈ Subgroup.closure {z | ∃ a ∈ (⊤ : Subgroup G).lowerCentralSeries c,
      ∃ b ∈ (⊤ : Subgroup G), ⁅a, b⁆ = z} at hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      have hqa : f a ∈ (⊤ : Subgroup (G ⧸ N)).lowerCentralSeries c := by
        rw [← htop, ← Subgroup.map_lowerCentralSeries]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hpa := ih V hq hqa
      have hba : ⁅b, a⁆ ∈ N := by
        have hab : ⁅a, b⁆ ∈ N := Subgroup.commutator_mem_commutator ha hb
        simpa only [commutatorElement_inv] using N.inv_mem hab
      have hp := powerCompression_commutator W N hN b a (hN hba) (c + 1) hpa
      simpa only [commutatorElement_inv, Nat.succ_eq_add_one] using hp.inv
    | one => exact PowerCompression.one W _
    | mul a b ha hb hpa hpb =>
      exact hpa.mul hpb (Subgroup.mem_center_iff.mp (hN hb) a)
    | inv a ha hpa => exact hpa.inv

/-- A subadditive natural-valued length bounds a finite product by the sum
of its factor lengths. -/
theorem subadditive_length_prod_le {A ι : Type*} [CommMonoid A]
    (ell : A → ℕ) (h1 : ell 1 = 0) (hmul : ∀ a b, ell (a * b) ≤ ell a + ell b)
    (s : Finset ι) (a : ι → A) : ell (∏ i ∈ s, a i) ≤ ∑ i ∈ s, ell (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hmul _ _).trans (Nat.add_le_add_left ih _)

/-- Uniform compression of generators of an abelian group extends to its
whole balls. The target group and the homomorphism are arbitrary. -/
theorem exists_ball_compression_of_commGroup {A : Type*} [CommGroup A] [DecidableEq A]
    (V : WordGeometry A) (W : WordGeometry G) (f : A →* G) (k : ℕ)
    (hgen : ∀ a ∈ V.generators, PowerCompression W (f a) k) :
    ∃ C : ℕ, ∀ r a, a ∈ V.ball (r ^ k) → W.length (f a) ≤ C * (r + 1) := by
  classical
  choose C hC using (fun a : V.generators => hgen a a.property)
  let M := Finset.univ.sup C
  refine ⟨V.generators.card * M, fun r a ha => ?_⟩
  obtain ⟨v, hv⟩ := Finset.mem_pow.mp ha
  let l : List A := List.ofFn (fun i => (v i : A))
  have hlen : l.length = r ^ k := by simp [l]
  have hl : l.toFinset ⊆ V.generators := by
    intro b hb
    have hb' : b ∈ l := List.mem_toFinset.mp hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb'
    exact (v i).property
  have hprod : a = ∏ b ∈ V.generators, b ^ l.count b :=
    hv.symm.trans (Finset.prod_list_count_of_subset l V.generators hl)
  rw [hprod]
  calc
    W.length (f (∏ b ∈ V.generators, b ^ l.count b))
        ≤ ∑ b ∈ V.generators, W.length (f (b ^ l.count b)) :=
      subadditive_length_prod_le (fun a => W.length (f a)) (by simp [W.length_one])
        (fun a b => by simpa only [map_mul] using W.length_mul_le (f a) (f b)) _ _
    _ ≤ ∑ _b ∈ V.generators, M * (r + 1) := by
      apply Finset.sum_le_sum
      intro b hb
      have hn : l.count b ≤ r ^ k := (List.count_le_length).trans hlen.le
      have hcb := hC ⟨b, hb⟩ r (l.count b) hn
      have hCM : C ⟨b, hb⟩ ≤ M := Finset.le_sup (Finset.mem_univ _)
      rw [map_pow]
      exact hcb.trans (Nat.mul_le_mul_right _ hCM)
    _ = (V.generators.card * M) * (r + 1) := by simp [Nat.mul_assoc]

/-- The intrinsic ball of radius `r^(c+1)` in the last lower-central term
lies in an ambient ball of radius linear in `r`. This is the compression
half of the sharp distortion comparison. -/
theorem exists_last_lowerCentralSeries_ball_inclusion (c : ℕ)
    (W : WordGeometry G) (hc : (⊤ : Subgroup G).lowerCentralSeries (c + 1) = ⊥)
    (V : WordGeometry ((⊤ : Subgroup G).lowerCentralSeries c)) :
    ∃ C : ℕ, 0 < C ∧ ∀ r,
      (V.ball (r ^ (c + 1))).image ((⊤ : Subgroup G).lowerCentralSeries c).subtype ⊆
        W.ball (C * (r + 1)) := by
  classical
  let N := (⊤ : Subgroup G).lowerCentralSeries c
  have hN : N ≤ Subgroup.center G :=
    (Subgroup.commutator_top_right_eq_bot_iff_le_center).mp hc
  let : CommGroup N := { (inferInstance : Group N) with
    mul_comm a b := Subtype.ext (Subgroup.mem_center_iff.mp (hN b.property) a) }
  obtain ⟨C, hC⟩ := exists_ball_compression_of_commGroup V W N.subtype (c + 1)
    (fun a _ => powerCompression_of_last_lowerCentralSeries c W hc a.property)
  refine ⟨C + 1, by omega, fun r g hg => ?_⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
  apply (W.mem_ball_iff_length_le _ _).mpr
  exact (hC r a ha).trans (Nat.mul_le_mul_right (r + 1) (by omega))

end RecurrentSections
