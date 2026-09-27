/- GID: D5/S3/Combinatorics/ArrowWilfTwelveCard
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwelveCard
   mirror-E: none(waiver:cardinality-of-decorated-twelve-fibers)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Antidiag.FinsuppEquiv]
   utility: none
   digest: A fixed upper moving set yields a derangement factor and a positive-gap binomial factor. -/

import D5.S3.Combinatorics.ArrowWilfTwelveCount
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwelveCard

noncomputable section

open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfGapData
open D5.S3.Combinatorics.ArrowWilfTwelveCount

noncomputable instance (n m k : ℕ) : Fintype (TwelveData n m k) := by
  let H := upperSupport n m
  let e : TwelveData n m k ≃
      Σ K : ↑(H.powersetCard k),
        ExactFixed H (H \ K.1) ×
          {g : PositiveGapsOn (Option ↑H) (m - 1) (fixedGapLabels H K.1) //
            (H \ K.1).card ≤ m - 1} := {
    toFun := fun d => ⟨d.K, d.sigma, ⟨d.gaps, d.enough⟩⟩
    invFun := fun ⟨K, sigma, gaps⟩ =>
      ⟨K, sigma, gaps.2, gaps.1⟩
    left_inv := by intro d; cases d; rfl
    right_inv := by intro d; cases d with | mk K rest => cases rest with
      | mk sigma gaps => cases gaps; rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Under the admissible gap bound, the decorated family has the summand cardinality (2.1). -/
theorem card_twelveData_of_enough {n m k : ℕ} (hm : 1 ≤ m)
    (henough : (upperSupport n m).card - k ≤ m - 1) :
    Fintype.card (TwelveData n m k) =
      (n - m).choose k * numDerangements k * (m + k - 1).choose (n - m) := by
  let H := upperSupport n m
  let e : TwelveData n m k ≃
      Σ K : ↑(H.powersetCard k),
        ExactFixed H (H \ K.1) ×
          PositiveGapsOn (Option ↑H) (m - 1) (fixedGapLabels H K.1) := {
    toFun := fun d => ⟨d.K, d.sigma, d.gaps⟩
    invFun := fun ⟨K, sigma, gaps⟩ =>
      { K := K
        sigma := sigma
        enough := by
          have hKsub : K.1 ⊆ H := (Finset.mem_powersetCard.mp K.2).1
          have hKcard : K.1.card = k := (Finset.mem_powersetCard.mp K.2).2
          simpa [H, Finset.card_sdiff_of_subset hKsub, hKcard] using henough
        gaps := gaps }
    left_inv := by intro d; cases d; rfl
    right_inv := by intro d; cases d with | mk K rest => cases rest; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hfiber : ∀ K : ↑(H.powersetCard k),
      Fintype.card
        (ExactFixed H (H \ K.1) ×
          PositiveGapsOn (Option ↑H) (m - 1) (fixedGapLabels H K.1)) =
        numDerangements k * (m + k - 1).choose (n - m) := by
    intro K
    let F := H \ K.1
    let R := fixedGapLabels H K.1
    have hKsub : K.1 ⊆ H := (Finset.mem_powersetCard.mp K.2).1
    have hKcard : K.1.card = k := (Finset.mem_powersetCard.mp K.2).2
    have hkH : k ≤ H.card := by
      rw [← hKcard]
      exact Finset.card_le_card hKsub
    have hFsub : F ⊆ H := Finset.sdiff_subset
    have hFcard : F.card = H.card - k := by
      dsimp [F]
      rw [Finset.card_sdiff_of_subset hKsub, hKcard]
    have hHcard : H.card = n - m := by
      simp [H, upperSupport, List.toFinset_card_of_nodup List.nodup_range']
    have hRcard : R.card = F.card := by
      simp [R, fixedGapLabels, F]
    have hFbound : F.card ≤ m - 1 := by simpa [hFcard] using henough
    have hcardExact : Fintype.card (ExactFixed H F) = numDerangements k := by
      rw [card_exactFixed hFsub]
      congr 1
      omega
    have hcardGap :
        Fintype.card (PositiveGapsOn (Option ↑H) (m - 1) R) =
          (H.card + (m - 1 - F.card)).choose (m - 1 - F.card) := by
      have hEq := positiveGapsEquiv (ι := Option ↑H) (t := m - 1) (R := R)
        (by simpa [hRcard] using hFbound)
      rw [Fintype.card_congr hEq]
      change Fintype.card ↑((Finset.univ : Finset (Option ↑H)).finsuppAntidiag
        (m - 1 - R.card)) = _
      rw [Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
      simp [Fintype.card_option, hRcard]
    rw [Fintype.card_prod, hcardExact, hcardGap]
    congr 1
    have hFadd : F.card + k = H.card := by
      rw [hFcard, Nat.sub_add_cancel hkH]
    have hRadd : (m - 1 - F.card) + F.card = m - 1 := Nat.sub_add_cancel hFbound
    have hupper : H.card + (m - 1 - F.card) = m + k - 1 := by omega
    rw [hupper]
    exact Nat.choose_symm_of_eq_add (by omega)
  simp_rw [hfiber]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard]
  simp [H, upperSupport, List.toFinset_card_of_nodup List.nodup_range', mul_assoc]

/-- The positive-gap obstruction is counted by a zero binomial coefficient. -/
theorem card_twelveData {n m k : ℕ} (hm : 1 ≤ m) :
    Fintype.card (TwelveData n m k) =
      (n - m).choose k * numDerangements k * (m + k - 1).choose (n - m) := by
  let H := upperSupport n m
  have hHcard : H.card = n - m := by
    simp [H, upperSupport, List.toFinset_card_of_nodup List.nodup_range']
  by_cases henough : H.card - k ≤ m - 1
  · exact card_twelveData_of_enough hm henough
  · have hk : k ≤ H.card := by omega
    have hlt : m + k - 1 < H.card := by omega
    haveI : IsEmpty (TwelveData n m k) := ⟨by
      intro d
      have hKsub : d.K.1 ⊆ H := (Finset.mem_powersetCard.mp d.K.2).1
      have hKcard : d.K.1.card = k := (Finset.mem_powersetCard.mp d.K.2).2
      have hbound : H.card - k ≤ m - 1 := by
        simpa [H, Finset.card_sdiff_of_subset hKsub, hKcard] using d.enough
      exact henough hbound⟩
    rw [Fintype.card_of_isEmpty]
    rw [← hHcard]
    simp [Nat.choose_eq_zero_of_lt hlt]

end

end D5.S3.Combinatorics.ArrowWilfTwelveCard
