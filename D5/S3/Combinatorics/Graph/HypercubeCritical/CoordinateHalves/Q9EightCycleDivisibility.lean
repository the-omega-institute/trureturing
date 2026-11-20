/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9EightCycleDivisibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9EightCycleDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A normalized eight-cycle projection forces the support order to be divisible by 24. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleProjection

/-! The degree sums of the two suffix supports constrain the order of the cubic support. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleDivisibility

open Finset
open Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced direction_edge_count)
open Q4SmallProjectionOrbits (representative)
open Q5EightCycleQuotient (neighbors)
open Q9EightCycleProjection (Normalized evenSupport oddSupport evenOnly oddOnly fullSupport
  normalized_card)
open private normalized_direction_zero_edges supports_disjoint even_union_full odd_union_full
  same_class_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleProjection
open private sum_degree_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5EightCycleQuotient

private theorem suffix_degree_sum_even {R F : Finset (Q 5)} (hRF : Disjoint R F)
    (hexclusive : ∀ x ∈ R, (neighbors (R ∪ F) x).card = 3)
    (hfull : ∀ x ∈ F, (neighbors (R ∪ F) x).card = 1) :
    2 ∣ 3 * R.card + F.card := by
  have h := sum_degree_twice (R ∪ F) false
  rw [sum_union hRF, sum_const_nat hexclusive, sum_const_nat hfull, Nat.mul_one] at h
  omega

open Classical in
/-- A Huang-balanced induced cubic support with a normalized eight-cycle projection
has order divisible by 24. -/
theorem normalized_card_dvd_twenty_four {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hn : Normalized C) : 24 ∣ C.card := by
  obtain ⟨_, hRF, hBF⟩ := supports_disjoint C
  have hcard : C.card = 12 * (fullSupport C).card := by
    have h := direction_edge_count (d := 3) C hr hb ((0 : Fin 4).castAdd 5)
    rw [normalized_direction_zero_edges hr hb hn] at h
    omega
  have hexclusive : (evenOnly C).card + (oddOnly C).card = (fullSupport C).card := by
    have h := normalized_card hr hb hn
    rw [← even_union_full C, ← odd_union_full C, card_union_of_disjoint hRF,
      card_union_of_disjoint hBF] at h
    omega
  have h0 : (0 : BitVec 4) ∈ representative false := by decide +kernel
  have h1 : (1 : BitVec 4) ∈ representative false := by decide +kernel
  have hd0 {y : Q 5} (hy : y ∈ evenSupport C) :
      (neighbors (evenSupport C) y).card = if y ∈ oddSupport C then 1 else 3 :=
    same_class_degree hr hb hn h0 hy
  have hd1 {y : Q 5} (hy : y ∈ oddSupport C) :
      (neighbors (oddSupport C) y).card = if y ∈ evenSupport C then 1 else 3 :=
    same_class_degree hr hb hn h1 hy
  have hEven : 2 ∣ 3 * (evenOnly C).card + (fullSupport C).card := by
    apply suffix_degree_sum_even hRF
    all_goals rw [even_union_full C]
    · intro y hy
      obtain ⟨he, ho⟩ := mem_sdiff.mp hy
      simpa only [ite_eq_right ho] using hd0 he
    · intro y hy
      obtain ⟨he, ho⟩ := mem_inter.mp hy
      simpa only [ite_eq_left ho] using hd0 he
  have hOdd : 2 ∣ 3 * (oddOnly C).card + (fullSupport C).card := by
    apply suffix_degree_sum_even hBF
    all_goals rw [odd_union_full C]
    · intro y hy
      obtain ⟨ho, he⟩ := mem_sdiff.mp hy
      simpa only [ite_eq_right he] using hd1 ho
    · intro y hy
      obtain ⟨he, ho⟩ := mem_inter.mp hy
      simpa only [ite_eq_left he] using hd1 ho
  have hFull : 2 ∣ (fullSupport C).card := by
    have hFive : 2 ∣ 5 * (fullSupport C).card := by omega
    omega
  obtain ⟨k, hk⟩ := hFull
  exact ⟨k, by omega⟩

#print axioms normalized_card_dvd_twenty_four

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleDivisibility
