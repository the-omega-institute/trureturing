/- GID: D5/S3/Combinatorics/Sequenceability/PairedQuantitativeOrdering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PairedQuantitativeOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   utility: none
   digest: Explicit uniform positive lower bound for actual proper-interval-Good C3 paired orders. -/

import D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate
import D5.S3.Combinatorics.Sequenceability.PairedResidualBlocks
import D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
import D5.S3.Combinatorics.CircularWords.CircularOrderCount

/-! Actual distinct original labels, original group addition and coefficient one throughout. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering

open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open D5.S3.Combinatorics.Sequenceability.PairedCircleEvents
open D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
open D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate
open D5.S3.Combinatorics.Sequenceability.ZeroTotalCircleGood
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.CircularOrderCount
open Finset
open scoped BigOperators Classical
noncomputable section

/-- Exactly the actual orders satisfying the original proper-interval convention. -/
def goodOrders (r : ℕ) : Finset (List (V r)) := (orders (alphabet r)).filter Good

/-- No nonempty proper union of original opposite pairs is a circular arc. -/
def circleGood {r : ℕ} (C : Cycle (V r)) : Prop :=
  ∀ I : Finset (Fin r), I.Nonempty → I ≠ univ → ¬ Arc (alphabet r) (pairs I) C

/-- The prescribed explicit rational lower bound. -/
def lowerFraction (r : ℕ) : ℚ :=
  (8*(r:ℚ)^3-123*r^2+388*r-45) / (3*(2*r-1)*(2*r-3)*(2*r-5))

private theorem pairs_nonempty {r : ℕ} {I : Finset (Fin r)} (hI : I.Nonempty) :
    (pairs I).Nonempty := card_pos.mp (by rw [pairs_card]; exact Nat.mul_pos (by decide) hI.card_pos)

private theorem pair_complement_nonempty {r : ℕ} {I : Finset (Fin r)} (hI : I ≠ univ) :
    (alphabet r \ pairs I).Nonempty := by
  rw [←pairs_complement]
  apply pairs_nonempty
  apply sdiff_nonempty_of_card_lt_card
  simpa using (Finset.card_lt_iff_ne_univ I).mpr hI

private theorem good_iff_circleGood {r : ℕ} {w : List (V r)} (hw : w ∈ orders (alphabet r)) :
    Good w ↔ circleGood (w : Cycle (V r)) := by
  rw [good_iff_no_zero_arc (alphabet_sum_zero r) hw]
  constructor
  · intro h I hi hp
    exact h (pairs I) (pairs_subset I) (pairs_nonempty hi)
      (pair_complement_nonempty hp) (pairs_sum_zero I)
  · intro h S hS hs hv hz
    rcases eq_or_ne S.card 1 with hsingle | hmultiple
    · obtain ⟨x, rfl⟩ := card_eq_one.mp hsingle
      have hx : x = 0 := by simpa using hz
      subst x
      exact (zero_not_mem_alphabet r (hS (mem_singleton_self 0))).elim
    · obtain ⟨I,hI,_⟩ := (zero_subset_spectrum S hS).mp hz
      subst S
      have hi : I.Nonempty := by
        apply card_pos.mp
        have := hs.card_pos
        rw [pairs_card] at this
        omega
      have hp : I ≠ univ := by
        intro he
        subst I
        rw [pairs_univ,sdiff_self] at hv
        exact not_nonempty_empty hv
      exact h I hi hp

private theorem surviving_circle {r : ℕ} (hr : 12 ≤ r) {C : Cycle (V r)}
    (hC : C ∈ noAdjacency r \ PairedResidualBlocks.bad r) : circleGood C := by
  obtain ⟨hno,hbad⟩ := mem_sdiff.mp hC
  have hadj : ∀ i : Fin r, ¬ adjacency i C := (mem_filter.mp hno).2
  intro I hi hp hArc
  have hcard : I.card < r := by simpa using (card_lt_iff_ne_univ I).mpr hp
  by_cases hone : I.card=1
  · obtain ⟨i,rfl⟩ := card_eq_one.mp hone
    exact hadj i hArc
  by_cases hc : (univ \ I).card=1
  · obtain ⟨i,he⟩ := card_eq_one.mp hc
    have hcomp : Arc (alphabet r) (pairs (univ \ I)) C := by
      rw [pairs_complement]
      exact (arc_complement (pairs_subset I) C).mp hArc
    rw [he] at hcomp
    exact hadj i hcomp
  · apply hbad
    apply mem_biUnion.mpr
    refine ⟨I,?_,mem_filter.mpr ⟨(mem_filter.mp hno).1,hArc⟩⟩
    have hcc : (univ \ I).card = r-I.card := by simp [card_sdiff_of_subset]
    have hpos := hi.card_pos
    simp only [PairedResidualBlocks.indices,mem_filter,mem_powerset,subset_univ,true_and]
    omega

private theorem circle_subtraction {r : ℕ} (hr : 12 ≤ r) :
    (noAdjacency r).card ≤ ((circles (alphabet r)).filter circleGood).card +
      (PairedResidualBlocks.bad r).card := by
  have hs : noAdjacency r \ PairedResidualBlocks.bad r ⊆
      (circles (alphabet r)).filter circleGood := by
    intro C hC
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp hC).1).1,surviving_circle hr hC⟩
  exact (card_le_card_sdiff_add_card (s := noAdjacency r) (t := PairedResidualBlocks.bad r)).trans
    (by nlinarith [card_le_card hs])

private theorem combined_fraction {r : ℕ} (hr : 12 ≤ r) :
    (4*(r:ℚ)^2-11*r+9)/(3*(2*r-1)*(2*r-3)) -
      (r:ℚ)*(27*r-105)/((2*r-1)*(2*r-3)*(2*r-5)) = lowerFraction r := by
  have hq : (12:ℚ) ≤ r := by exact_mod_cast hr
  have h1 : 0 < 2*(r:ℚ)-1 := by linarith
  have h3 : 0 < 2*(r:ℚ)-3 := by linarith
  have h5 : 0 < 2*(r:ℚ)-5 := by linarith
  have h13 := mul_pos h1 h3
  have h135 := mul_pos h13 h5
  unfold lowerFraction
  field_simp (discharger := nlinarith [h1,h3,h5,h13,h135])
  <;> ring

private theorem lowerFraction_pos {r : ℕ} (hr : 12 ≤ r) : 0 < lowerFraction r := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hr
  have hs : (0:ℚ) ≤ s := by positivity
  have hn : 8*((12+s:ℕ):ℚ)^3-123*((12+s:ℕ):ℚ)^2+388*((12+s:ℕ):ℚ)-45 =
      8*(s:ℚ)^3+165*s^2+892*s+723 := by push_cast; ring
  unfold lowerFraction
  rw [hn]
  apply div_pos
  · positivity
  · push_cast
    have h1 : (0 : ℚ) < 2 * (12 + (s : ℚ)) - 1 := by linarith
    have h3 : (0 : ℚ) < 2 * (12 + (s : ℚ)) - 3 := by linarith
    have h5 : (0 : ℚ) < 2 * (12 + (s : ℚ)) - 5 := by linarith
    exact mul_pos (mul_pos (mul_pos (by norm_num) h1) h3) h5

/-- The all-r finite quantitative bound for actual original-label proper-interval-Good orders.
This is a density estimate for the paired C3 family, not arbitrary-subset sequenceability. -/
theorem quantitative_good_orders {r : ℕ} (hr : 12 ≤ r) :
    ((2*r).factorial : ℚ) * lowerFraction r ≤ ((goodOrders r).card : ℚ) ∧
      0 < lowerFraction r ∧ 0 < (goodOrders r).card := by
  have hN : (0:ℚ) < (2*r-1).factorial := by positivity
  have hn := no_adjacency_lower_bound hr
  have ht := PairedResidualBlocks.residual_mass_le (r := r) (by omega)
  have htail := paired_tail_bound (r := r) (by omega)
  have hb : ((PairedResidualBlocks.bad r).card : ℚ) / ((2*r-1).factorial : ℚ) ≤
      (r:ℚ)*(27*r-105)/((2*r-1)*(2*r-3)*(2*r-5)) := ht.trans htail
  have hs : ((noAdjacency r).card : ℚ) ≤
      (((circles (alphabet r)).filter circleGood).card : ℚ) +
        ((PairedResidualBlocks.bad r).card : ℚ) := by exact_mod_cast circle_subtraction hr
  have hd := div_le_div_of_nonneg_right hs hN.le
  rw [add_div] at hd
  have hc : lowerFraction r ≤ (((circles (alphabet r)).filter circleGood).card : ℚ) /
      ((2*r-1).factorial : ℚ) := by
    rw [←combined_fraction hr]
    linarith
  have hA : (alphabet r).Nonempty := card_pos.mp (by rw [alphabet_card]; omega)
  have he : goodOrders r = (orders (alphabet r)).filter
      (fun (w : List (V r)) => circleGood (w : Cycle (V r))) := by
    ext w
    simp only [goodOrders,mem_filter]
    exact and_congr_right (fun hw => good_iff_circleGood hw)
  have hwords : (goodOrders r).card = 2*r * ((circles (alphabet r)).filter circleGood).card := by
    rw [he,event_order_card (alphabet r) hA,alphabet_card]
  have hf : ((2*r).factorial : ℚ) = 2*(r:ℚ)*((2*r-1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : 2*r ≠ 0)).symm
  have hratio : ((goodOrders r).card : ℚ) / ((2*r).factorial : ℚ) =
      (((circles (alphabet r)).filter circleGood).card : ℚ) / ((2*r-1).factorial : ℚ) := by
    apply (div_eq_div_iff (by positivity : ((2*r).factorial : ℚ) ≠ 0) (ne_of_gt hN)).mpr
    rw [hwords,hf]
    push_cast
    ring
  rw [←hratio] at hc
  have hmain := (le_div_iff₀ (show (0:ℚ) < (2*r).factorial by positivity)).mp hc
  have hp := lowerFraction_pos hr
  refine ⟨by simpa [mul_comm] using hmain,hp,?_⟩
  have hh : (0:ℚ) < (goodOrders r).card :=
    (mul_pos (by positivity : (0:ℚ) < (2*r).factorial) hp).trans_le (by simpa [mul_comm] using hmain)
  exact_mod_cast hh

end
end D5.S3.Combinatorics.Sequenceability.PairedQuantitativeOrdering
