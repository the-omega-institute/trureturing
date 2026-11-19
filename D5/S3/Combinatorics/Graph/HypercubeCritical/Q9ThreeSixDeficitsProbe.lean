import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe

/-! An integer certificate excluding the profile with three deficits of three
and six deficits of five. -/

set_option autoImplicit false

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges directionEndpoints
  direction_edge_count)
local notation "flip" => BalancedCriticalSpectrum.flip
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private endpoint_weight_sum endpoint_weight_swap from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private cubic_parity_half_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private def profile (i : Fin 9) : ℤ := if i.val < 3 then 3 else 5

private def cost (x : Q 9) : ℤ := ∑ i : Fin 9, if x i then profile i else 0

private def potential (x : Q 9) : ℤ :=
  let low := ∑ i : Fin 9, if i.val < 3 ∧ x i = true then (1 : ℕ) else 0
  let high := ∑ i : Fin 9, if 3 ≤ i.val ∧ x i = true then (1 : ℕ) else 0
  match low, high with
  | 0, 0 | 3, 0 => 1080
  | 1, 1 | 2, 1 => 1120
  | 0, 2 => 2244
  | 0, 3 => -1125
  | _, _ => 0

private def halfCoefficient (i : Fin 9) : ℤ := if i.val < 3 then -3360 else -6750

private def directionCoefficient (i : Fin 9) : ℤ := if i.val < 3 then 0 else -1110

private def vertexScore (x : Q 9) : ℤ :=
  20160 + (if cubeParity x then -3420 else 0) +
    (∑ i : Fin 9, if x i then halfCoefficient i else 0) - 3 * potential x

private def edgeScore (i : Fin 9) (x : Q 9) : ℤ :=
  potential x + potential (flip x i) + directionCoefficient i

private def cubeIndex : Fin 512 ≃ Q 9 :=
  BitVec.equivFin.toEquiv.symm.trans (cubeBitVec 9)

private lemma vertex_floor :
    (∑ x : Fin 512, if cost (cubeIndex x) ≤ 17 then min 0 (vertexScore (cubeIndex x)) else 0) =
      -13500 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
-- The kernel sums the contributions of all directed edges of the allowed cube.
private lemma edge_floor :
    (∑ i : Fin 9, ∑ x : Fin 512,
      if cost (cubeIndex x) ≤ 17 ∧ cost (flip (cubeIndex x) i) ≤ 17
        then min 0 (edgeScore i (cubeIndex x)) else 0) = -720 := by
  decide +kernel

attribute [local instance] Classical.propDecidable

private lemma sum_score_on_selected (C : Finset (Q 9)) (hC : C.card = 66)
    (hparity : (C.filter (fun x => cubeParity x = true)).card = 33)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * profile i = 33) :
    (∑ x ∈ C, vertexScore x) = -59220 + 73260 - 3 * ∑ x ∈ C, potential x := by
  have hpar : (∑ x ∈ C, if cubeParity x then (-3420 : ℤ) else 0) = -112860 := by
    rw [← sum_filter, sum_const, hparity]
    rfl
  have hhalfSum : (∑ x ∈ C, ∑ i : Fin 9, if x i then halfCoefficient i else 0) =
      ∑ i : Fin 9, (33 - 2 * profile i) * halfCoefficient i := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    linarith only [hhalf i]
  have hnum : (∑ i : Fin 9, (33 - 2 * profile i) * halfCoefficient i) = -1203660 := by
    decide +kernel
  simp only [vertexScore, sum_sub_distrib, sum_add_distrib, sum_const, hC, nsmul_eq_mul, hpar,
    hhalfSum, hnum, ← mul_sum]
  norm_num

private lemma sum_score_on_endpoints (C : Finset (Q 9))
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hedge : ∀ i, directionEdges C i = 11) :
    (∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, edgeScore i x) =
      6 * (∑ x ∈ C, potential x) - 146520 := by
  have hdir (i : Fin 9) : (directionEndpoints C i).card = 22 := by
    rw [endpoint_card_twice, hedge i]
  have hnum : (∑ i : Fin 9, 22 * directionCoefficient i) = -146520 := by decide +kernel
  simp only [edgeScore, sum_add_distrib, endpoint_weight_swap, sum_const, hdir, nsmul_eq_mul,
    Nat.cast_ofNat, hnum]
  rw [endpoint_weight_sum C hreg]
  ring

/-- An actual Huang-balanced cubic support of size 66 cannot have a sorted
minority profile consisting of three threes followed by six fives. -/
theorem no_three_six_deficit_profile {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * profile i = 33)
    (hcost : ∀ x ∈ C, cost x ≤ 17) : False := by
  have hpar := cubic_parity_half_card hC hreg true
  have hdir (i : Fin 9) : directionEdges C i = 11 := by
    have h := direction_edge_count (d := 3) C hreg hb i
    omega
  have hpoint := sum_score_on_selected C hC hpar hhalf
  have hedge := sum_score_on_endpoints C hreg hdir
  let A := (univ : Finset (Q 9)).filter (fun x => cost x ≤ 17)
  have hCsub : C ⊆ A := fun x hx => mem_filter.mpr ⟨mem_univ _, hcost x hx⟩
  have hpointLower : -13500 ≤ ∑ x ∈ C, vertexScore x := by
    have hfloor : (∑ x ∈ A, min 0 (vertexScore x)) = -13500 := by
      dsimp only [A]
      rw [sum_filter, ← Equiv.sum_comp cubeIndex]
      exact vertex_floor
    rw [← hfloor]
    exact (sum_le_sum_of_subset_of_nonpos hCsub (fun _ _ _ => min_le_left _ _)).trans
      (sum_le_sum fun _ _ => min_le_right _ _)
  have hedgeLower : -720 ≤ ∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, edgeScore i x := by
    have hi (i : Fin 9) : directionEndpoints C i ⊆ A.filter (fun x => cost (flip x i) ≤ 17) := by
      intro x hx
      obtain ⟨hx, hf⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hCsub hx, hcost _ hf⟩
    have hfloor : (∑ i : Fin 9, ∑ x ∈ A.filter (fun x => cost (flip x i) ≤ 17),
        min 0 (edgeScore i x)) = -720 := by
      refine Eq.trans ?_ edge_floor
      apply sum_congr rfl
      intro i _
      dsimp only [A]
      rw [sum_filter, sum_filter]
      simp only [← ite_and]
      exact (Equiv.sum_comp cubeIndex _).symm
    rw [← hfloor]
    apply sum_le_sum
    intro i _
    exact (sum_le_sum_of_subset_of_nonpos (hi i) (fun _ _ _ => min_le_left _ _)).trans
      (sum_le_sum fun _ _ => min_le_right _ _)
  linarith

#print axioms no_three_six_deficit_profile

private lemma cost_bound_of_three_six_deficits {C : Finset (Q 9)}
    (hC : C.card = 66) (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * profile i = 33)
    (x : Q 9) (hx : x ∈ C) : cost x ≤ 17 := by
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hcap : ((shell C x 7).card : ℤ) ≤ 8 := by
    exact_mod_cast sixty_six_distance_seven_le_eight hC hreg hb hd hx
  have hw := coordinate_profile_weight_bound hC hreg hb (fun _ => true) profile hhalf hx
  have hprofile : (∑ i, profile i) = 39 := by decide +kernel
  rw [hprofile] at hw
  change 2 * cost x + 12 ≤ 39 + (shell C x 7).card at hw
  omega

/-- The radius constraints and the integer certificate leave 154 sorted
minority profiles for a hypothetical balanced cubic 66-point support. -/
def sixtySixProfilesAfterThreeSix : List (List ℤ) :=
  sixtySixProfilesAfterThinHalf.filter (· != List.ofFn profile)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Evaluate each of the existing profile filters as well as the new removal.
theorem sixtySixProfilesAfterThreeSix_length : sixtySixProfilesAfterThreeSix.length = 154 := by
  decide +kernel

/-- Any actual 66-point support would have a surviving sorted profile. -/
theorem q9_sixty_six_mem_profiles_after_three_six {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterThreeSix := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_thin_half hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterThreeSix, List.mem_filter]
  refine ⟨hprofile, bne_iff_ne.mpr ?_⟩
  intro he
  have hr := List.ofFn_inj.mp he
  subst r
  exact no_three_six_deficit_profile hS hregS hbS hhalf
    (cost_bound_of_three_six_deficits hS hregS hbS hhalf)

#print axioms q9_sixty_six_mem_profiles_after_three_six

end D5.S3.Combinatorics.Graph.HypercubeCritical
