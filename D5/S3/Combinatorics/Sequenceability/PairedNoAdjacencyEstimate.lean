/- GID: D5/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PairedNoAdjacencyEstimate
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Third-order common-circle Bonferroni estimate for original opposite-pair adjacencies. -/

import D5.S3.Combinatorics.Sequenceability.PairedCircleEvents

/-! The intersections are contracted jointly; no products of marginal probabilities occur. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate

open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
open D5.S3.Combinatorics.Sequenceability.PairedCircleEvents
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.CircularWords.FiniteEventBonferroniThree
open Finset
open scoped BigOperators Classical
noncomputable section

/-- Actual circles containing none of the r designated opposite-pair adjacencies. -/
def noAdjacency (r : ℕ) : Finset (Cycle (V r)) :=
  (circles (alphabet r)).filter (fun C => ∀ i : Fin r, ¬ adjacency i C)

private theorem factorial_lower {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℚ) = (n:ℚ) * ((n-1).factorial : ℚ) := by
  exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm

private theorem bonferroni_normalize {r : ℕ} (hr : 12 ≤ r) :
    ((∑ p ∈ range 4, (-1:ℚ)^p *
      ((r.choose p : ℚ) * (2^p * (2*r-p-1).factorial : ℕ))) /
        ((2*r-1).factorial : ℚ)) =
      (4*(r:ℚ)^2-11*r+9) / (3*(2*r-1)*(2*r-3)) := by
  have hq : (12:ℚ) ≤ r := by exact_mod_cast hr
  have hc2a : (r.choose 2 : ℚ)*2 = (r:ℚ)*(r-1) := by
    have h : (r.choose 2 : ℚ)*2 = (r:ℚ)*(r-1:ℕ) := by
      exact_mod_cast (by simpa only [Nat.choose_one_right] using Nat.choose_succ_right_eq r 1 :
        r.choose 2 * 2 = r*(r-1))
    simpa only [Nat.cast_sub (by omega : 1 ≤ r),Nat.cast_one] using h
  have hc3a : (r.choose 3 : ℚ)*3 = (r.choose 2 : ℚ)*(r-2) := by
    have h : (r.choose 3 : ℚ)*3 = (r.choose 2 : ℚ)*(r-2:ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq r 2
    simpa only [Nat.cast_sub (by omega : 2 ≤ r),Nat.cast_ofNat] using h
  have hc2 : (r.choose 2 : ℚ) = (r:ℚ)*(r-1)/2 := by linarith
  have hc3 : (r.choose 3 : ℚ) = (r:ℚ)*(r-1)*(r-2)/6 := by
    nlinarith [hc2a,hc3a,congrArg (fun x : ℚ => x*(r-2)) hc2a]
  have hN := factorial_lower (n := 2*r-1) (by omega)
  have hF1 := factorial_lower (n := 2*r-2) (by omega)
  have hF2 := factorial_lower (n := 2*r-3) (by omega)
  have hi1 : 2*r-1-1=2*r-2 := by omega
  have hi2 : 2*r-2-1=2*r-3 := by omega
  have hi3 : 2*r-3-1=2*r-4 := by omega
  rw [hi1] at hN
  rw [hi2] at hF1
  rw [hi3] at hF2
  rw [Nat.cast_sub (by omega : 1 ≤ 2*r)] at hN
  rw [Nat.cast_sub (by omega : 2 ≤ 2*r)] at hF1
  rw [Nat.cast_sub (by omega : 3 ≤ 2*r)] at hF2
  push_cast at hN hF1 hF2
  have h1 : 2*(r:ℚ)-1 ≠ 0 := by linarith
  have h2 : 2*(r:ℚ)-2 ≠ 0 := by linarith
  have h3 : 2*(r:ℚ)-3 ≠ 0 := by linarith
  have hf : ((2*r-4).factorial : ℚ) ≠ 0 := by positivity
  norm_num [Finset.sum_range_succ,Nat.sub_sub]
  rw [hc2,hc3,hN,hF1,hF2]
  simp only [div_eq_mul_inv,mul_inv_rev]
  field_simp [h1,h2,h3,hf]
  <;> field_simp (discharger := linarith [hq])
  <;> ring

/-- Explicit lower density from the actual three-term Bonferroni intersections. -/
theorem no_adjacency_lower_bound {r : ℕ} (hr : 12 ≤ r) :
    (4*(r:ℚ)^2-11*r+9) / (3*(2*r-1)*(2*r-3)) ≤
      ((noAdjacency r).card : ℚ) / ((2*r-1).factorial : ℚ) := by
  have hb := bonferroni_three (circles (alphabet r)) (univ : Finset (Fin r))
    (fun i C => adjacency i C)
  have hm : (∑ p ∈ range 4, (-1:ℚ)^p *
      ∑ T ∈ (univ : Finset (Fin r)).powersetCard p,
        (((circles (alphabet r)).filter (fun C => ∀ i ∈ T, adjacency i C)).card : ℚ)) =
      ∑ p ∈ range 4, (-1:ℚ)^p *
        ((r.choose p : ℚ) * (2^p * (2*r-p-1).factorial : ℕ)) := by
    apply sum_congr rfl
    intro p hp
    rw [adjacency_moment hr (by have := mem_range.mp hp; omega)]
  have hb' : (∑ p ∈ range 4, (-1:ℚ)^p *
      ∑ T ∈ (univ : Finset (Fin r)).powersetCard p,
        (((circles (alphabet r)).filter (fun C => ∀ i ∈ T, adjacency i C)).card : ℚ)) ≤
      ((noAdjacency r).card : ℚ) := by
    unfold noAdjacency
    convert hb using 1
    · apply sum_congr rfl
      intro p hp
      apply congrArg (fun z : ℚ => (-1 : ℚ)^p * z)
      apply sum_congr rfl
      intro T hT
      apply congrArg (fun s : Finset (Cycle (V r)) => (s.card : ℚ))
      ext C
      simp
    · apply congrArg (fun s : Finset (Cycle (V r)) => (s.card : ℚ))
      ext C
      simp
  rw [hm] at hb'
  have hd := div_le_div_of_nonneg_right hb'
    (show (0:ℚ) ≤ (2*r-1).factorial by positivity)
  rw [bonferroni_normalize hr] at hd
  exact hd

end
end D5.S3.Combinatorics.Sequenceability.PairedNoAdjacencyEstimate
