/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjectionEleven
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourProjectionEleven
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The 28-point half condition forces at least eleven patterns on every four axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenProjectionOnlyK4
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4TightStarObstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4NoSingletonCase
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4EightSingletons
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4TwelveSingletons

/-! This projection bound concerns the order-72 branch of Hong–Wu–Xia,
arXiv:2610.09483v1, §7 Problem 2. In the ten-pattern orbit, the signed fibers of
the subdivided K₄ projection are governed by cut indicators. Half cardinalities
constrain the even occupation of the zero cuts, and parity in Q₅ constrains the
singleton cuts. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourProjectionEleven

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9FourFiberSpectrum (leftProjection)
open Q9SignedProjection (join signedRow)
open Q9TenPatternIncidence (tenProjection vertexCode)
open Q9K4CutBalance
open Q9K4ZeroCutArithmetic (zeroCutOccupation)
open Q4TenProjectionOrbits (representative)
open Q9ThetaProjection (leftCode)
open private label_values countIf singletonSupport_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4CutBalance
open private occupation_totals from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9K4ZeroCutArithmetic
open private pattern from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private exists_normalized_projection from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenProjectionOnlyK4

open Classical in
private theorem normalized_k4_excluded {C : Finset (Q 9)} (hsize : C.card = 72)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hP : leftProjection C = tenProjection)
    (hhalf : ∀ i, 28 ≤
      (C.filter fun u => u ((starAxis i).castAdd 5) = decide (i ≠ 0)).card) : False := by
  obtain ⟨z, hu, hz, hrow, hrows, ht, hcases⟩ :=
    Q9K4ZeroCutArithmetic.balanced_zero_cut_occupation hsize hreg hb hP hhalf
  rcases hcases with ⟨_, h30⟩ | ⟨hzero, h28⟩
  · exact Q9K4TightStarObstruction.tight_stars_impossible hsize hreg hb hP
      (fun i => (h30 i).ge)
  obtain ⟨_, heven, hodd, _⟩ := occupation_totals hsize hreg hb hP hu hz hrow
    (fun i y => (hrows i y).1) ht
  have hcutCount : 3 * singletons z + 4 * balancedCuts z = ∑ y, oddCount z y := by
    have hlocalCount (y : Q 5) :
        3 * countIf (oddCount z y = 3) + 4 * countIf (oddCount z y = 4) = oddCount z y := by
      rcases ht y with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨h, _⟩ <;> norm_num [h, countIf]
    have h := sum_congr (s₁ := (univ : Finset (Q 5))) rfl (fun y _ => hlocalCount y)
    simpa only [sum_add_distrib, ← mul_sum, singletons, balancedCuts] using h
  have hB : 0 ≤ balancedCuts z := by
    unfold balancedCuts
    exact sum_nonneg (fun _ _ => by unfold countIf; split <;> omega)
  have hfix := (singleton_parity_rows
    (fun i y => label_values hu hz (join (pattern (vertexCode i)) y)) hrows ht).2
  have hclasses := singleton_count_cases hfix (by omega) (by omega)
  rcases hclasses with hs | hs | hs | hs
  · have hempty : singletonSupport z = ∅ := by
      apply card_eq_zero.mp
      have hcard := singletonSupport_card z
      omega
    have hcuts (y : Q 5) : oddCount z y = 0 ∨ oddCount z y = 4 := by
      rcases ht y with ⟨_, ho, _⟩ | ⟨_, _, ho, _⟩ | ⟨ho, _⟩
      · exact Or.inl ho
      · have hmem : (cubeBitVec 5).symm y ∈ singletonSupport z := by
          simpa [singletonSupport] using ho
        rw [hempty] at hmem
        exact (notMem_empty _ hmem).elim
      · exact Or.inr ho
    let A (y : Q 5) := evenCount (fun i => evenLabel z i y)
    have hsum : (∑ y, A y) =
        zeroCutOccupation z + ∑ y ∈ univ.filter (fun y => oddCount z y = 4), A y := by
      rw [zeroCutOccupation, sum_filter, ← sum_add_distrib]
      refine sum_congr rfl (fun y _ => ?_)
      rcases hcuts y with h | h <;> simp [h, A]
    have hactive : (∑ y ∈ univ.filter (fun y : Q 5 => oddCount z y = 4), A y) = 24 := by
      change (∑ y, A y) = _ at heven
      omega
    exact Q9K4NoSingletonCase.no_zero_singleton_case hreg hb hP hu hz hrow hcuts
      (by omega) hactive
  · exact Q9K4EightSingletons.eight_singletons_impossible_of_half_twenty_eight
      hsize hreg hb hP h28 hu hz hrow hrows ht hzero hs
  · exact Q9K4TwelveSingletons.singletons_ne_twelve_of_zeroCutOccupation_eight
      hsize hreg hb hP hu hz hrow hrows ht hzero hs
  · omega

open Classical in
/-- Every choice of four distinct axes realizes at least eleven patterns on an
order-72 balanced induced cubic support in Q₉ with at least 28 vertices in each half. -/
theorem four_projection_card_ge_eleven_of_twenty_eight {S : Finset (Q 9)}
    (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 28 ≤ (S.filter (fun x => x j = b)).card)
    (axes : Fin 4 ↪ Fin 9) :
    11 ≤ (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card := by
  have h10 := Q9PairProjectionSharp.four_projection_card_ge_ten_of_twenty_eight
    hsize hreg hb hhalf axes
  by_contra hnot
  have hten :
      (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card = 10 := by omega
  obtain ⟨σ, t, hproj⟩ := Q9TenProjectionOnlyK4.ten_projection_only_k4 hsize hreg hb hhalf axes hten
  obtain ⟨C, hreg', hb', hC, hcard, hhalf'⟩ :=
    exists_normalized_projection hreg hb hhalf axes (representative 5) σ t hproj
  have heq : (representative 5).image (cubeBitVec 4) = tenProjection := by decide +kernel
  have hleft : leftProjection C = tenProjection := by
    rw [← heq, ← hC, Finset.image_image]
    unfold leftProjection
    apply Finset.image_congr
    intro x _
    exact ((cubeBitVec 4).apply_symm_apply _).symm
  exact normalized_k4_excluded (hcard.trans hsize) hreg' hb' hleft
    (fun i => hhalf' ((starAxis i).castAdd 5) (decide (i ≠ 0)))

#check four_projection_card_ge_eleven_of_twenty_eight
#print axioms four_projection_card_ge_eleven_of_twenty_eight

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9FourProjectionEleven
