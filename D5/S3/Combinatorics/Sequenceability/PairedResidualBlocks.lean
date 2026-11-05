/- GID: D5/S3/Combinatorics/Sequenceability/PairedResidualBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PairedResidualBlocks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Exact complement pairing and finite residual zero-block mass on actual paired circles. -/

import D5.S3.Combinatorics.Sequenceability.PairedCircleEvents
import D5.S3.Combinatorics.Sequenceability.PairedBinomialTail

/-! Complementary proper zero blocks describe the same circular event and contribute twice. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.PairedResidualBlocks

open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open D5.S3.Combinatorics.Sequenceability.PairedCircleEvents
open D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open Finset
open scoped BigOperators Classical
noncomputable section

/-- Coordinate subsets left after both single-pair endpoint classes are removed. -/
def indices (r : ℕ) : Finset (Finset (Fin r)) :=
  univ.powerset.filter (fun I => 2 ≤ I.card ∧ I.card ≤ r-2)

/-- The event is always a filter of the same original-label circle inventory. -/
def event {r : ℕ} (I : Finset (Fin r)) : Finset (Cycle (V r)) :=
  (circles (alphabet r)).filter (Arc (alphabet r) (pairs I))

/-- Actual union of the remaining proper zero-block events. -/
def bad (r : ℕ) : Finset (Cycle (V r)) := (indices r).biUnion event

private theorem mem_indices {r : ℕ} {I : Finset (Fin r)} :
    I ∈ indices r ↔ 2 ≤ I.card ∧ I.card ≤ r-2 := by simp [indices]

private theorem complement_mem {r : ℕ} (hr : 4 ≤ r) {I : Finset (Fin r)}
    (hI : I ∈ indices r) : univ \ I ∈ indices r := by
  have hc : (univ \ I).card = r-I.card := by simp [card_sdiff_of_subset]
  rw [mem_indices,hc]
  have := mem_indices.mp hI
  have : I.card ≤ r := by simpa using card_le_card (subset_univ I)
  omega

private theorem complement_ne {r : ℕ} (hr : 0 < r) (I : Finset (Fin r)) : I ≠ univ \ I := by
  intro he
  let i : Fin r := ⟨0,hr⟩
  have hh : i ∈ I ↔ i ∈ univ \ I := by rw [←he]
  simp only [mem_sdiff,mem_univ,true_and] at hh
  tauto

/-- Complementation preserves each event, including the middle cardinality. -/
theorem event_complement {r : ℕ} (I : Finset (Fin r)) : event (univ \ I) = event I := by
  ext C
  simp only [event,mem_filter,pairs_complement]
  exact and_congr_right (fun _ => (arc_complement (pairs_subset I) C).symm)

/-- The complement pair gives exactly two distinct subset witnesses for every residual event. -/
theorem residual_double_card {r : ℕ} (hr : 4 ≤ r) :
    2*(bad r).card ≤ ∑ I ∈ indices r, (event I).card := by
  have hsub : bad r ⊆ circles (alphabet r) := by
    intro C hC
    obtain ⟨I,hI,hC⟩ := mem_biUnion.mp hC
    exact (mem_filter.mp hC).1
  have hf (C : Cycle (V r)) (hC : C ∈ bad r) :
      2 ≤ ((indices r).filter (fun I => C ∈ event I)).card := by
    obtain ⟨I,hI,hC⟩ := mem_biUnion.mp hC
    have hh : ({I,univ \ I} : Finset (Finset (Fin r))) ⊆
        (indices r).filter (fun J => C ∈ event J) := by
      intro J hJ
      rcases mem_insert.mp hJ with rfl|hJ
      · exact mem_filter.mpr ⟨hI,hC⟩
      · have he : J=univ \ I := mem_singleton.mp hJ
        subst J
        exact mem_filter.mpr ⟨complement_mem hr hI,by rw [event_complement]; exact hC⟩
    have hcard := card_le_card hh
    simpa [card_pair (complement_ne (by omega) I)] using hcard
  calc
    _ = ∑ _C ∈ bad r, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ C ∈ bad r, ((indices r).filter (fun I => C ∈ event I)).card := sum_le_sum hf
    _ ≤ ∑ C ∈ circles (alphabet r), ((indices r).filter (fun I => C ∈ event I)).card :=
      sum_le_sum_of_subset hsub
    _ = ∑ I ∈ indices r, (event I).card := by
      simp only [card_eq_sum_ones,sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro I hI
      simp only [event,card_eq_sum_ones,sum_filter,mem_filter]
      apply sum_congr rfl
      intro C hC
      simp [hC]

/-- Single-arc cardinality divided by the actual free-rotation normalization. -/
theorem event_ratio {r : ℕ} (hr : 6 ≤ r) {I : Finset (Fin r)} (hI : I ∈ indices r) :
    ((event I).card : ℚ) / ((2*r-1).factorial : ℚ) =
      (2*(r:ℚ)) / ((2*r).choose (2*I.card) : ℚ) := by
  have hi := mem_indices.mp hI
  have hj : I.card ≤ r := by simpa using card_le_card (subset_univ I)
  have hs : (pairs I).Nonempty := card_pos.mp (by rw [pairs_card]; omega)
  have hv : (alphabet r \ pairs I).Nonempty := by
    rw [←card_pos,card_sdiff_of_subset (pairs_subset I),alphabet_card,pairs_card]
    omega
  have hc : (event I).card = (2*I.card).factorial * (2*r-2*I.card).factorial := by
    rw [event,arc_filter_card _ _ (pairs_subset I) hs hv,pairs_card,
      card_sdiff_of_subset (pairs_subset I),alphabet_card,pairs_card]
  have hchoose := Nat.choose_mul_factorial_mul_factorial (by omega : 2*I.card ≤ 2*r)
  have hfac := Nat.mul_factorial_pred (by omega : 2*r ≠ 0)
  have he : ((2*r).choose (2*I.card) : ℚ) * ((event I).card : ℚ) =
      (2*(r:ℚ)) * ((2*r-1).factorial : ℚ) := by
    rw [hc]
    exact_mod_cast (by nlinarith [hchoose,hfac] :
      (2*r).choose (2*I.card) * ((2*I.card).factorial * (2*r-2*I.card).factorial) =
        (2*r) * (2*r-1).factorial)
  apply (div_eq_div_iff (by positivity : ((2*r-1).factorial : ℚ) ≠ 0)
    (by exact_mod_cast Nat.choose_ne_zero (by omega : 2*I.card ≤ 2*r))).mpr
  nlinarith [he]

/-- The unconditional residual mass has the exact complement factor r. -/
theorem residual_mass_le {r : ℕ} (hr : 6 ≤ r) :
    ((bad r).card : ℚ) / ((2*r-1).factorial : ℚ) ≤
      (r:ℚ) * ∑ j ∈ Icc 2 (r-2), density r j := by
  have hfiber (j : ℕ) (hj : j ∈ Icc 2 (r-2)) :
      (indices r).filter (fun I => I.card=j) = (univ : Finset (Fin r)).powersetCard j := by
    ext I
    simp only [mem_filter,mem_indices,mem_powersetCard,subset_univ,true_and]
    have hj := mem_Icc.mp hj
    omega
  have hsum : (∑ I ∈ indices r, ((event I).card : ℚ) / ((2*r-1).factorial : ℚ)) =
      2*(r:ℚ) * ∑ j ∈ Icc 2 (r-2), density r j := by
    calc
      _ = ∑ I ∈ indices r, 2*(r:ℚ) / ((2*r).choose (2*I.card) : ℚ) := by
        apply sum_congr rfl
        exact fun I hI => event_ratio hr hI
      _ = ∑ j ∈ Icc 2 (r-2), ∑ I ∈ (indices r).filter (fun I => I.card=j),
          2*(r:ℚ) / ((2*r).choose (2*j) : ℚ) := by
        symm
        exact sum_fiberwise_of_maps_to' (fun I hI => mem_Icc.mpr (mem_indices.mp hI)) _
      _ = ∑ j ∈ Icc 2 (r-2), (r.choose j : ℚ) *
          (2*(r:ℚ) / ((2*r).choose (2*j) : ℚ)) := by
        apply sum_congr rfl
        intro j hj
        rw [hfiber j hj]
        simp [card_powersetCard]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        unfold density
        ring
  have hdouble : 2*((bad r).card : ℚ) ≤ ∑ I ∈ indices r, ((event I).card : ℚ) := by
    exact_mod_cast residual_double_card (r := r) (by omega)
  have hN : (0:ℚ) < (2*r-1).factorial := by positivity
  have hd := div_le_div_of_nonneg_right hdouble hN.le
  rw [sum_div, hsum, mul_div_assoc] at hd
  linarith

end
end D5.S3.Combinatorics.Sequenceability.PairedResidualBlocks
