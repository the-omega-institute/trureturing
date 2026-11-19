import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerWeightsProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9WeightLayerParityProbe

/-! Five normalized profiles are incompatible with the forced incident directions
at vertices attaining the distance-seven weight bound. -/

set_option autoImplicit false

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
  (directions regular_directions)
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound sixty_six_edge_weight_inequality from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open BalancedCriticalSpectrum (Q IsBalanced flip directionEndpoints)

private def trueWeight (a : Fin 9 → ℤ) (x : Q 9) : ℤ :=
  ∑ i, if x i = true then a i else 0

private def heavyTrueDirections (r : Fin 9 → ℤ) (x : Q 9) : Finset (Fin 9) :=
  univ.filter fun i => x i = true ∧ 2 ≤ r i

open Classical in
/-- Equality in the normalized vertex weight bound forces every true
direction of deficit at least two to be incident, so there are at most three. -/
theorem q9_sixty_six_weight_bound_with_forced_directions
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (r : Fin 9 → ℤ) (hr : ∀ i, 0 ≤ r i)
    (hhalf : ∀ i, ((C.filter (fun y => y i = true)).card : ℤ) + 2 * r i = 33)
    {x : Q 9} (hx : x ∈ C) :
    2 * trueWeight r x + 12 ≤ (∑ i, r i) + 8 ∧
      (2 * trueWeight r x + 12 = (∑ i, r i) + 8 →
        (heavyTrueDirections r x).card ≤ 3) := by
  have hw := coordinate_profile_weight_bound hC hreg hb (fun _ => true) r hhalf hx
  change 2 * trueWeight r x + 12 ≤ (∑ i, r i) + (shell C x 7).card at hw
  have hs : ((shell C x 7).card : ℤ) ≤ 8 := by
    exact_mod_cast sixty_six_distance_seven_le_eight hC hreg hb hd hx
  refine ⟨by omega, fun he => ?_⟩
  have h8 : (shell C x 7).card = 8 := by omega
  have hsub : heavyTrueDirections r x ⊆ directions C x := by
    intro i hi
    have hit := (mem_filter.mp hi).2
    exact (mem_directions C x i).mpr
      (eight_partners_force_minority_directions_used hC hreg hb hd
        (fun _ => true) r hhalf hr hx h8 hit.1 hit.2)
  exact (card_le_card hsub).trans_eq (regular_directions C hreg hx)

open Classical in
/-- A uniform bound on the test weight gives a bound on its sum over the
coordinate halves, strengthened by the edges that cross each half. -/
theorem q9_sixty_six_test_weight_bound
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (r a : Fin 9 → ℤ) (K : ℤ)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33)
    (hK : ∀ x ∈ C, trueWeight a x ≤ K) :
    (∑ i, a i * (110 - 6 * r i)) ≤ 198 * K := by
  let t (x : Q 9) (i : Fin 9) : ℤ := if x i = true then a i else 0
  let g (x : Q 9) : ℤ := K - trueWeight a x
  have hn (x : Q 9) (hx : x ∈ C) : 0 ≤ g x := sub_nonneg.mpr (hK x hx)
  have hlocal (i : Fin 9) (x : Q 9) (hx : x ∈ directionEndpoints C i) :
      a i ≤ g x + g (flip x i) := by
    have hxC := (mem_filter.mp hx).1
    have hfC := (mem_filter.mp hx).2
    have hsplit (y : Q 9) :
        trueWeight a y = (∑ j ∈ (univ : Finset (Fin 9)).erase i, t y j) + t y i :=
      (sum_erase_add _ _ (mem_univ i)).symm
    have hs : (∑ j ∈ (univ : Finset (Fin 9)).erase i, t (flip x i) j) =
        ∑ j ∈ (univ : Finset (Fin 9)).erase i, t x j := by
      apply sum_congr rfl
      intro j hj
      simp [t, BalancedCriticalSpectrum.flip, (mem_erase.mp hj).1]
    have hdiff : g (flip x i) - g x = t x i - t (flip x i) i := by
      dsimp only [g]
      rw [hsplit x, hsplit (flip x i), hs]
      ring
    cases hi : x i <;>
      simp [t, BalancedCriticalSpectrum.flip_apply_same, hi] at hdiff <;>
      linarith [hn x hxC, hn _ hfC]
  have hedge := sixty_six_edge_weight_inequality hC hreg hb a g hlocal
  have htotal : (∑ x ∈ C, trueWeight a x) = ∑ i, (33 - 2 * r i) * a i := by
    unfold trueWeight
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter, sum_const, nsmul_eq_mul, eq_sub_of_add_eq (hhalf i)]
  have hgap : (∑ x ∈ C, g x) = 66 * K - ∑ i, (33 - 2 * r i) * a i := by
    dsimp only [g]
    rw [sum_sub_distrib, sum_const, hC, nsmul_eq_mul, htotal]
    rfl
  have heq : (∑ i, a i * (110 - 6 * r i)) =
      11 * (∑ i, a i) + 3 * ∑ i, (33 - 2 * r i) * a i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun i _ => by ring)
  rw [hgap] at hedge
  rw [heq]
  linarith

private structure ForcedEdgeCertificate where
  deficit : Fin 9 → ℤ
  test : Fin 9 → ℤ
  bound : ℤ

private def forcedEdgeCertificate : Fin 5 → ForcedEdgeCertificate :=
  ![⟨![2, 3, 5, 5, 5, 5, 5, 5, 5], ![0, 1, 1, 1, 1, 1, 1, 1, 1], 3⟩,
    ⟨![3, 4, 5, 5, 5, 5, 5, 5, 5], ![0, 1, 1, 1, 1, 1, 1, 1, 1], 3⟩,
    ⟨![4, 5, 5, 5, 5, 5, 5, 5, 5], ![0, 1, 1, 1, 1, 1, 1, 1, 1], 3⟩,
    ⟨![4, 4, 4, 4, 4, 5, 5, 5, 5], ![2, 2, 2, 2, 2, 3, 3, 3, 3], 9⟩,
    ⟨![4, 4, 4, 5, 5, 5, 5, 5, 5], ![1, 1, 1, 2, 2, 2, 2, 2, 2], 6⟩]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Check the allowed Boolean vertices and the arithmetic gap for each certificate.
private theorem forcedEdgeCertificate_valid (k : Fin 5) :
    let c := forcedEdgeCertificate k
    (∀ i, 0 ≤ c.deficit i) ∧
    (∀ x : Q 9, 2 * trueWeight c.deficit x + 12 ≤ (∑ i, c.deficit i) + 8 →
      (2 * trueWeight c.deficit x + 12 = (∑ i, c.deficit i) + 8 →
        (heavyTrueDirections c.deficit x).card ≤ 3) →
      trueWeight c.test x ≤ c.bound) ∧
    198 * c.bound < ∑ i, c.test i * (110 - 6 * c.deficit i) := by
  fin_cases k <;> decide +kernel

/-- The five profiles excluded using the forced directions at equality. -/
def sixtySixForcedEdgeProfiles : List (List ℤ) :=
  List.ofFn fun k => List.ofFn (forcedEdgeCertificate k).deficit

open Classical in
/-- None of the five listed normalized deficits is realizable by an induced
66-vertex Huang-balanced cubic support. -/
theorem q9_sixty_six_excludes_forced_edge_profiles
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (r : Fin 9 → ℤ)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) :
    List.ofFn r ∉ sixtySixForcedEdgeProfiles := by
  intro hp
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp hp
  have he := List.ofFn_inj.mp hk
  subst r
  let c := forcedEdgeCertificate k
  obtain ⟨hr, htest, hstrict⟩ := forcedEdgeCertificate_valid k
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hK (x : Q 9) (hx : x ∈ C) : trueWeight c.test x ≤ c.bound := by
    have hw := q9_sixty_six_weight_bound_with_forced_directions hC hreg hb hd c.deficit hr hhalf hx
    exact htest x hw.1 hw.2
  exact (not_lt_of_ge (q9_sixty_six_test_weight_bound hC hreg hb c.deficit c.test c.bound
    hhalf hK)) hstrict

/-- The weight-parity list after the forced-direction exclusions. -/
def sixtySixProfilesAfterForcedEdges : List (List ℤ) :=
  sixtySixProfilesAfterWeightParity.filter fun p => !sixtySixForcedEdgeProfiles.contains p

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
-- Reduce the composed finite profile filters in the kernel.
theorem sixtySixProfilesAfterForcedEdges_length : sixtySixProfilesAfterForcedEdges.length = 39 := by
  decide +kernel

open Classical in
/-- The normalized profile of a hypothetical 66-vertex Huang-balanced cubic
support belongs to the 39 profiles surviving the forced-direction exclusions. -/
theorem q9_sixty_six_mem_profiles_after_forced_edges
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterForcedEdges := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hp⟩ :=
    q9_sixty_six_mem_profiles_after_weight_parity hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  simp only [sixtySixProfilesAfterForcedEdges, List.mem_filter, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not]
  exact ⟨hp, q9_sixty_six_excludes_forced_edge_profiles hS hregS hbS r hhalf⟩

#print axioms q9_sixty_six_weight_bound_with_forced_directions
#print axioms q9_sixty_six_test_weight_bound
#print axioms q9_sixty_six_excludes_forced_edge_profiles
#print axioms sixtySixProfilesAfterForcedEdges_length
#print axioms q9_sixty_six_mem_profiles_after_forced_edges

end D5.S3.Combinatorics.Graph.HypercubeCritical
