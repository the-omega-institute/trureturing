/- GID: D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Universal rational leg factors reconstruct complement-symmetric set functions. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval

/-!
The hyperlink transform is Eq. (5) of Santalla, Singha Roy, Sierra and
Rodríguez-Laguna, *The hyperlink representation of entanglement and the
inclusion-exclusion principle*, arXiv:2601.17926v2, Appendix B.

The reconstruction concerns every real complement-symmetric set function
vanishing at the empty set. Subsystem entropies of finite-dimensional pure
states satisfy these hypotheses by equality of the complementary nonzero
spectra and zero entropy of the empty subsystem. The identification with
the repository's density-state and von Neumann entropy definitions is not
formalized here.
-/

open scoped BigOperators

namespace D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The inclusion-exclusion hyperlink coefficient. -/
def hyperlink (S : Finset α → ℝ) (I : Finset α) : ℝ :=
  ∑ B ∈ I.powerset, (-1 : ℝ) ^ (I.card - B.card) * S B

/-- Rational coefficients of the inverse triangular system on even ranks. -/
def legInverseCoeff : ℕ → ℚ :=
  Nat.strongRec (fun r prev =>
    if r = 0 then 1
    else if Even r then
      -(1 / 2 : ℚ) * ∑ j : Fin r,
        if Even j.val then (r.choose j.val : ℚ) * prev j.val j.isLt else 0
    else 0)

/-- Universal leg factors, with zero totalization outside the leg range. -/
def legFactor (m p : ℕ) : ℚ :=
  if p ≤ m then
    -(1 / 2 : ℚ) *
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k => 2 ≤ k ∧ Even k),
        legInverseCoeff (m - k) *
          ((m.choose k : ℚ) - (p.choose k : ℚ) - ((m - p).choose k : ℚ))
  else 0

/-- One rational coefficient family works for every finite ambient system. -/
def claim : Prop :=
  ∃ L : ℕ → ℕ → ℚ,
    (∀ m, L m 0 = 0 ∧ L m m = 0) ∧
    (∀ m p, L m p = L m (m - p)) ∧
    ∀ (N : ℕ) (S : Finset (Fin N) → ℝ),
      S ∅ = 0 → (∀ A, S Aᶜ = S A) → ∀ A,
        S A =
          ∑ I ∈ (Finset.univ : Finset (Fin N)).powerset.filter
              (fun I => Even I.card ∧ I ≠ ∅),
            (L I.card (I ∩ A).card : ℝ) * hyperlink S I

private theorem legInverseCoeff_eq (r : ℕ) :
    legInverseCoeff r =
      if r = 0 then 1
      else if Even r then
        -(1 / 2 : ℚ) *
          ∑ j ∈ (Finset.range r).filter (fun j => Even j),
            (r.choose j : ℚ) * legInverseCoeff j
      else 0 := by
  rw [legInverseCoeff, Nat.strongRec_eq]
  change (if r = 0 then 1 else if Even r then
    -(1 / 2 : ℚ) * ∑ j : Fin r,
      if Even j.val then (r.choose j.val : ℚ) * legInverseCoeff j.val else 0
    else 0) = _
  by_cases hz : r = 0
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    by_cases he : Even r
    · rw [if_pos he, if_pos he]
      congr 1
      rw [Finset.sum_filter]
      exact Fin.sum_univ_eq_sum_range
        (fun j => if Even j then (r.choose j : ℚ) * legInverseCoeff j else 0) r
    · rw [if_neg he, if_neg he]

private theorem legInverseCoeff_convolution (r : ℕ) (hr : Even r) :
    legInverseCoeff r +
        (1 / 2 : ℚ) *
          ∑ j ∈ (Finset.range r).filter (fun j => Even j),
            (r.choose j : ℚ) * legInverseCoeff j =
      if r = 0 then 1 else 0 := by
  rw [legInverseCoeff_eq]
  by_cases h : r = 0
  · subst r
    simp only [ite_true, Finset.range_zero, Finset.filter_empty, Finset.sum_empty,
      mul_zero, add_zero]
  · rw [if_neg h, if_pos hr, if_neg h]
    ring

private theorem alternating_powerset (A : Finset α) :
    (∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card) = if A = ∅ then 1 else 0 := by
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := A))

private theorem powerset_interval_sum (A B : Finset α) (hBA : B ⊆ A)
    (f : Finset α → ℝ) :
    (∑ I ∈ A.powerset.filter (fun I => B ⊆ I), f I) =
      ∑ D ∈ (A \ B).powerset, f (B ∪ D) := by
  rw [← Finset.Icc_eq_filter_powerset, Finset.Icc_eq_image_powerset hBA,
    Finset.sum_image]
  intro D hD E hE h
  exact Finset.disjoint_injOn_union_left B
    (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hD))
    (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hE))
    (by simpa only [Finset.union_comm] using h)

private theorem alternating_interval (A B : Finset α) (hBA : B ⊆ A) :
    (∑ I ∈ A.powerset.filter (fun I => B ⊆ I),
      (-1 : ℝ) ^ (I.card - B.card)) = if A = B then 1 else 0 := by
  rw [powerset_interval_sum A B hBA]
  have hc : ∀ D ∈ (A \ B).powerset, (B ∪ D).card - B.card = D.card := by
    intro D hD
    rw [Finset.card_union_of_disjoint
      (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hD))]
    omega
  rw [Finset.sum_congr rfl (fun D hD => congrArg ((-1 : ℝ) ^ ·) (hc D hD))]
  rw [alternating_powerset]
  have he : A \ B = ∅ ↔ A = B := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm h hBA, fun h => h ▸ Finset.Subset.refl B⟩
  simp only [he]

private theorem sign_sub (n m : ℕ) (h : m ≤ n) :
    (-1 : ℝ) ^ (n - m) = (-1 : ℝ) ^ n * (-1 : ℝ) ^ m := by
  have hs : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul]
    exact (even_two_mul m).neg_one_pow
  calc
    _ = (-1 : ℝ) ^ (n - m) * ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) := by rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]

omit [DecidableEq α] in
private theorem zeta_hyperlink (S : Finset α → ℝ) (A : Finset α) :
    (∑ I ∈ A.powerset, hyperlink S I) = S A := by
  classical
  simp only [hyperlink]
  rw [Finset.sum_comm' (t' := A.powerset)
    (s' := fun B => A.powerset.filter (fun I => B ⊆ I))]
  · simp_rw [← Finset.sum_mul]
    have h : ∀ B ∈ A.powerset,
        (∑ I ∈ A.powerset.filter (fun I => B ⊆ I),
          (-1 : ℝ) ^ (I.card - B.card)) = if A = B then 1 else 0 :=
      fun B hB => alternating_interval A B (Finset.mem_powerset.mp hB)
    rw [Finset.sum_congr rfl (fun B hB => congrArg (· * S B) (h B hB))]
    simp only [ite_mul, one_mul, zero_mul]
    simp
  · intro I B
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩

omit [DecidableEq α] in
private theorem hyperlink_zeta (v : Finset α → ℝ) (I : Finset α) :
    hyperlink (fun A => ∑ K ∈ A.powerset, v K) I = v I := by
  classical
  simp only [hyperlink, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := I.powerset)
    (s' := fun K => I.powerset.filter (fun B => K ⊆ B))]
  · simp_rw [← Finset.sum_mul]
    have h : ∀ K ∈ I.powerset,
        (∑ B ∈ I.powerset.filter (fun B => K ⊆ B),
          (-1 : ℝ) ^ (I.card - B.card)) = if I = K then 1 else 0 := by
      intro K hK
      rw [powerset_interval_sum I K (Finset.mem_powerset.mp hK)]
      have he : ∀ D ∈ (I \ K).powerset,
          I.card - (K ∪ D).card = (I \ K).card - D.card := by
        intro D hD
        rw [Finset.card_union_of_disjoint
          (disjoint_sdiff_self_right.mono_right (Finset.mem_powerset.mp hD)),
          Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hK)]
        omega
      rw [Finset.sum_congr rfl (fun D hD => congrArg ((-1 : ℝ) ^ ·) (he D hD))]
      have hb := Finset.sum_pow_mul_eq_add_pow (1 : ℝ) (-1) (I \ K)
      simp only [one_pow, one_mul, add_neg_cancel] at hb
      rw [hb]
      by_cases hk : I = K
      · subst K
        simp
      · have hn : (I \ K).card ≠ 0 := by
          intro hz
          have h := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hz)
          exact hk (Finset.Subset.antisymm h (Finset.mem_powerset.mp hK))
        simp only [zero_pow hn, if_neg hk]
    rw [Finset.sum_congr rfl (fun K hK => congrArg (· * v K) (h K hK))]
    simp only [ite_mul, one_mul, zero_mul]
    simp
  · intro B K
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2.trans h.1⟩, fun h => ⟨h.1.1, h.1.2⟩⟩

variable [Fintype α]

private theorem hyperlink_compl (S : Finset α → ℝ) (I : Finset α) :
    hyperlink (fun A => S Aᶜ) I =
      (-1 : ℝ) ^ I.card *
        ∑ K ∈ (Finset.univ : Finset α).powerset.filter (fun K => I ⊆ K),
          hyperlink S K := by
  rw [hyperlink]
  simp_rw [← zeta_hyperlink S, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset α).powerset)
    (s' := fun K => (I \ K).powerset)]
  · have h : ∀ K ∈ (Finset.univ : Finset α).powerset,
        (∑ B ∈ (I \ K).powerset, (-1 : ℝ) ^ (I.card - B.card)) =
          if I ⊆ K then (-1 : ℝ) ^ I.card else 0 := by
      intro K _
      calc
        _ = (-1 : ℝ) ^ I.card * ∑ B ∈ (I \ K).powerset, (-1 : ℝ) ^ B.card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun B hB =>
            sign_sub I.card B.card
              (Finset.card_le_card ((Finset.mem_powerset.mp hB).trans Finset.sdiff_subset)))
        _ = _ := by
          rw [alternating_powerset]
          simp only [Finset.sdiff_eq_empty_iff_subset, mul_ite, mul_one, mul_zero]
    simp_rw [← Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun K hK => congrArg (· * hyperlink S K) (h K hK))]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
  · intro B K
    simp only [Finset.mem_powerset, Finset.subset_univ, and_true,
      Finset.subset_sdiff, Finset.subset_compl_iff_disjoint_left]

omit [DecidableEq α] [Fintype α] in
private theorem hyperlink_weighted_sum {β : Type*} (t : Finset β)
    (a : β → ℝ) (F : β → Finset α → ℝ) (I : Finset α) :
    hyperlink (fun A => ∑ b ∈ t, a b * F b A) I =
      ∑ b ∈ t, a b * hyperlink (F b) I := by
  simp only [hyperlink, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact Finset.sum_congr rfl (fun B _ => mul_left_comm _ _ _)

private theorem even_hyperlink_ext (S T : Finset α → ℝ)
    (hzero : S ∅ = T ∅) (hS : ∀ A, S Aᶜ = S A) (hT : ∀ A, T Aᶜ = T A)
    (heven : ∀ I, Even I.card → I ≠ ∅ → hyperlink S I = hyperlink T I) :
    S = T := by
  have hc : ∀ n I, Fintype.card α - I.card = n → hyperlink S I = hyperlink T I := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I hn
      by_cases hz : I = ∅
      · subst I
        simpa only [hyperlink, Finset.powerset_empty, Finset.sum_singleton,
          Finset.card_empty, Nat.sub_self, pow_zero, one_mul] using hzero
      by_cases he : Even I.card
      · exact heven I he hz
      have hsign : (-1 : ℝ) ^ I.card = -1 := (Nat.not_even_iff_odd.mp he).neg_one_pow
      have hs := hyperlink_compl S I
      have ht := hyperlink_compl T I
      rw [funext hS, hsign] at hs
      rw [funext hT, hsign] at ht
      let t := (Finset.univ : Finset α).powerset.filter (fun K => I ⊆ K)
      have hi : I ∈ t := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ I), Finset.Subset.refl I⟩
      have hrest : (∑ K ∈ t.erase I, hyperlink S K) =
          ∑ K ∈ t.erase I, hyperlink T K := by
        refine Finset.sum_congr rfl (fun K hK => ?_)
        have hk := Finset.mem_erase.mp hK
        have hIK := (Finset.mem_filter.mp hk.2).2
        have hlt : I.card < K.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hIK, Ne.symm hk.1⟩)
        have hbound := K.card_le_univ
        have hm : Fintype.card α - K.card < n := by omega
        exact ih (Fintype.card α - K.card) hm K rfl
      change hyperlink S I = -1 * ∑ K ∈ t, hyperlink S K at hs
      change hyperlink T I = -1 * ∑ K ∈ t, hyperlink T K at ht
      rw [← Finset.sum_erase_add t (hyperlink S) hi, hrest] at hs
      rw [← Finset.sum_erase_add t (hyperlink T) hi] at ht
      linarith
  funext A
  rw [← zeta_hyperlink S A, ← zeta_hyperlink T A]
  exact Finset.sum_congr rfl (fun I _ => hc (Fintype.card α - I.card) I rfl)

end

end D5.S3.Quantum.Information.EvenLeggedHyperlinkReconstruction
