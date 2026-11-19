import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DegreeCertificatesProbe

/-! The diameter-seven bound excludes profiles that survive the degree equations alone. -/

set_option autoImplicit false

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced directionEdges directionEndpoints direction_edge_count)
local notation "flip" => BalancedCriticalSpectrum.flip

open private DegreeCertificate DegreeCertificate.mk DegreeCertificate.deficit DegreeCertificate.cost
  DegreeCertificate.limit DegreeCertificate.vertexScore DegreeCertificate.edgeScore
  DegreeCertificate.vertexTotal DegreeCertificate.edgeTotal DegreeCertificate.edgeFloor
  sum_vertex_scores sum_edge_scores all_decide_sound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9DegreeCertificatesProbe
open private cubeIndex from D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThreeSixDeficitsProbe
open private cubic_parity_half_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private shell from D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private def pairCount (pairs : List (Fin 512 × Fin 512)) (x : Fin 512) : ℤ :=
  (pairs.map fun (a, b) => (if x = a then 1 else 0) + (if x = b then 1 else 0)).sum

private lemma sum_pairCount_le (C : Finset (Q 9))
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7) (pairs : List (Fin 512 × Fin 512))
    (hfar : ∀ p ∈ pairs, 7 < hammingDist (cubeIndex p.1) (cubeIndex p.2)) :
    (∑ x ∈ C, pairCount pairs (cubeIndex.symm x)) ≤ (pairs.length : ℤ) := by
  have hcount (i : Fin 512) : (∑ x ∈ C, if cubeIndex.symm x = i then (1 : ℤ) else 0) =
      cubeMembership C (cubeIndex i) := by
    simp only [Equiv.symm_apply_eq, Finset.sum_ite_eq', cubeMembership]
  induction pairs with
  | nil => simp [pairCount]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have hne := hfar (a, b) (List.mem_cons_self)
    have hp := cube_lifted_forbidden_pair_row C (cubeIndex a) (cubeIndex b)
      (fun ha hb => (not_le_of_gt hne) (hd _ ha _ hb))
    have ht := ih (fun q hq => hfar q (List.mem_cons_of_mem _ hq))
    simp only [pairCount, List.map_cons, List.sum_cons, Finset.sum_add_distrib, hcount,
      List.length_cons, Nat.cast_add, Nat.cast_one] at ⊢
    change cubeMembership C (cubeIndex a) + cubeMembership C (cubeIndex b) +
      (∑ x ∈ C, pairCount ps (cubeIndex.symm x)) ≤ (ps.length : ℤ) + 1
    linarith

private def certificate : DegreeCertificate :=
  DegreeCertificate.mk [2, 2, 4, 4, 5, 5, 5, 5, 5] 4800 (-420)
    [-870, -870, -1320, -1320, -1752, -1752, -1752, -1752, -1752]
    [150, 150, 0, 0, -144, -144, -144, -144, -144]
    [(0, 120), (10200, 150), (20000, 120), (20100, 300), (100100, 144), (100200, 288), (110000, 294),
      (110100, 147), (120100, -144), (200000, 438), (200200, -144), (210000, -147), (300000, -294)]

-- Every pair differs in eight coordinates.
private def forbiddenPairs : List (Fin 512 × Fin 512) := [
    (53, 202), (53, 330), (53, 394), (54, 201), (54, 329), (54, 393), (57, 198), (57, 326),
      (57, 390), (58, 197), (58, 325), (58, 389), (85, 170), (85, 298), (85, 394), (86, 169),
      (86, 297), (86, 393), (89, 166), (89, 294), (89, 390), (90, 165), (90, 293), (90, 389),
      (101, 154), (101, 282), (101, 394), (102, 153), (102, 281), (102, 393), (105, 150),
      (105, 278), (105, 390), (106, 149), (106, 277), (106, 389), (149, 298), (149, 330),
      (150, 297), (150, 329), (153, 294), (153, 326), (154, 293), (154, 325), (165, 282),
      (165, 330), (166, 281), (166, 329), (169, 278), (169, 326), (170, 277), (170, 325),
      (197, 282), (197, 298), (198, 281), (198, 297), (201, 278), (201, 294), (202, 277),
      (202, 293)]
private def penalty : ℤ := 292

private def vertexScore (c : DegreeCertificate) (x : Fin 512) : ℤ :=
  DegreeCertificate.vertexScore c (cubeIndex x) + penalty * pairCount forbiddenPairs x

private def vertexFloor (c : DegreeCertificate) : ℤ :=
  (List.ofFn fun x : Fin 512 =>
    if DegreeCertificate.cost c (cubeIndex x) ≤ DegreeCertificate.limit c then
      min 0 (vertexScore c x) else 0).sum

set_option maxRecDepth 4096 in
private lemma forbiddenPairs_far :
    forbiddenPairs.all (fun p => decide (7 < hammingDist (cubeIndex p.1) (cubeIndex p.2))) =
      true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
-- Evaluate all scores on the finite cube, including the distance-eight corrections.
private lemma certificate_gap :
    2 * (DegreeCertificate.vertexTotal certificate + penalty * forbiddenPairs.length) +
      DegreeCertificate.edgeTotal certificate <
      2 * vertexFloor certificate + DegreeCertificate.edgeFloor certificate := by
  decide +kernel

attribute [local instance] Classical.propDecidable

/-- A balanced cubic 66-vertex support cannot have normalized deficits
`(2,2,4,4,5,5,5,5,5)`. The finite certificate uses distance-eight pairs. -/
theorem no_two_two_five_deficit_profile {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) +
      2 * DegreeCertificate.deficit certificate i = 33) : False := by
  let c := certificate
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hcost (x : Q 9) (hx : x ∈ C) :
      DegreeCertificate.cost c x ≤ DegreeCertificate.limit c := by
    have hcap : ((shell C x 7).card : ℤ) ≤ 8 := by
      exact_mod_cast sixty_six_distance_seven_le_eight hC hreg hb hd hx
    have hw := coordinate_profile_weight_bound hC hreg hb (fun _ => true)
      (DegreeCertificate.deficit c) hhalf hx
    change 2 * DegreeCertificate.cost c x + 12 ≤ (∑ i, DegreeCertificate.deficit c i) +
      (shell C x 7).card at hw
    unfold DegreeCertificate.limit
    omega
  have hdir (i : Fin 9) : directionEdges C i = 11 := by
    have h := direction_edge_count (d := 3) C hreg hb i
    omega
  have hpoint := sum_vertex_scores c C hC (cubic_parity_half_card hC hreg true) hhalf
  have hedge := sum_edge_scores c C hreg hdir
  have hpair := sum_pairCount_le C hd forbiddenPairs
    (fun _ hp => all_decide_sound forbiddenPairs_far hp)
  have hpenalty : 0 ≤ penalty := by decide
  have hbudget := mul_le_mul_of_nonneg_left hpair hpenalty
  let A := (univ : Finset (Q 9)).filter (fun x =>
    DegreeCertificate.cost c x ≤ DegreeCertificate.limit c)
  have hCsub : C ⊆ A := fun x hx => mem_filter.mpr ⟨mem_univ _, hcost x hx⟩
  have hpointLower : vertexFloor c ≤ ∑ x ∈ C, vertexScore c (cubeIndex.symm x) := by
    have hfloor : (∑ x ∈ A, min 0 (vertexScore c (cubeIndex.symm x))) = vertexFloor c := by
      dsimp only [A, vertexFloor]
      rw [List.sum_ofFn, sum_filter, ← Equiv.sum_comp cubeIndex]
      simp only [Equiv.symm_apply_apply]
    rw [← hfloor]
    exact (sum_le_sum_of_subset_of_nonpos hCsub (fun _ _ _ => min_le_left _ _)).trans
      (sum_le_sum fun _ _ => min_le_right _ _)
  have hedgeLower : DegreeCertificate.edgeFloor c ≤
      ∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, DegreeCertificate.edgeScore c i x := by
    have hi (i : Fin 9) : directionEndpoints C i ⊆
        A.filter (fun x => DegreeCertificate.cost c (flip x i) ≤ DegreeCertificate.limit c) := by
      intro x hx
      obtain ⟨hx, hf⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hCsub hx, hcost _ hf⟩
    have hfloor : (∑ i : Fin 9, ∑ x ∈ A.filter
        (fun x => DegreeCertificate.cost c (flip x i) ≤ DegreeCertificate.limit c),
        min 0 (DegreeCertificate.edgeScore c i x)) = DegreeCertificate.edgeFloor c := by
      unfold DegreeCertificate.edgeFloor
      rw [List.sum_ofFn]
      apply sum_congr rfl
      intro i _
      dsimp only [A]
      rw [List.sum_ofFn, sum_filter, sum_filter]
      simp only [← ite_and]
      exact (Equiv.sum_comp cubeIndex _).symm
    rw [← hfloor]
    apply sum_le_sum
    intro i _
    exact (sum_le_sum_of_subset_of_nonpos (hi i) (fun _ _ _ => min_le_left _ _)).trans
      (sum_le_sum fun _ _ => min_le_right _ _)
  simp only [vertexScore, Equiv.apply_symm_apply, sum_add_distrib, ← mul_sum] at hpointLower
  have hgap : 2 * (DegreeCertificate.vertexTotal c + penalty * forbiddenPairs.length) +
      DegreeCertificate.edgeTotal c < 2 * vertexFloor c + DegreeCertificate.edgeFloor c :=
    certificate_gap
  linarith

#print axioms no_two_two_five_deficit_profile

/-- The profiles remaining after the first distance-eight certificate. -/
def sixtySixProfilesAfterDiameterCertificate : List (List ℤ) :=
  sixtySixProfilesAfterDegreeCertificates.filter
    (· != List.ofFn (DegreeCertificate.deficit certificate))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- The count evaluates all previous finite filters as well as this exclusion.
theorem sixtySixProfilesAfterDiameterCertificate_length :
    sixtySixProfilesAfterDiameterCertificate.length = 103 := by
  decide +kernel

/-- Every 66-point Huang-balanced cubic support normalizes to one of the
103 profiles that survive the degree and first distance-eight certificates. -/
theorem q9_sixty_six_mem_profiles_after_diameter_certificate {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterDiameterCertificate := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_degree_certificates hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterDiameterCertificate, List.mem_filter]
  refine ⟨hprofile, bne_iff_ne.mpr ?_⟩
  intro he
  have hr := List.ofFn_inj.mp he
  subst r
  exact no_two_two_five_deficit_profile hS hregS hbS hhalf

#print axioms q9_sixty_six_mem_profiles_after_diameter_certificate

end D5.S3.Combinatorics.Graph.HypercubeCritical
