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
open private shell from D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private abbrev WeightedPair := Fin 512 × Fin 512 × ℤ

private def pairWeight (pairs : List WeightedPair) (x : Fin 512) : ℤ :=
  (pairs.map fun (a, b, weight) =>
    (if x = a then weight else 0) + (if x = b then weight else 0)).sum

private def pairingBudget (pairs : List WeightedPair) : ℤ :=
  (pairs.map fun (_, _, weight) => weight).sum

private def validPair (p : WeightedPair) : Prop :=
  0 ≤ p.2.2 ∧ 7 < hammingDist (cubeIndex p.1) (cubeIndex p.2.1)

private instance (p : WeightedPair) : Decidable (validPair p) := by
  unfold validPair
  infer_instance

private lemma sum_pairWeight_le (C : Finset (Q 9))
    (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7) (pairs : List WeightedPair)
    (hfar : ∀ p ∈ pairs, validPair p) :
    (∑ x ∈ C, pairWeight pairs (cubeIndex.symm x)) ≤ pairingBudget pairs := by
  have hcount (i : Fin 512) (w : ℤ) :
      (∑ x ∈ C, if cubeIndex.symm x = i then w else 0) =
        w * cubeMembership C (cubeIndex i) := by
    simp only [Equiv.symm_apply_eq, Finset.sum_ite_eq', cubeMembership, mul_ite, mul_one, mul_zero]
  induction pairs with
  | nil => simp [pairWeight, pairingBudget]
  | cons p ps ih =>
    obtain ⟨a, b, w⟩ := p
    obtain ⟨hw, hne⟩ := hfar (a, b, w) List.mem_cons_self
    have hp := cube_lifted_forbidden_pair_row C (cubeIndex a) (cubeIndex b)
      (fun ha hb => (not_le_of_gt hne) (hd _ ha _ hb))
    have ht := ih (fun q hq => hfar q (List.mem_cons_of_mem _ hq))
    simp only [pairWeight, pairingBudget, List.map_cons, List.sum_cons, sum_add_distrib, hcount]
    change w * cubeMembership C (cubeIndex a) + w * cubeMembership C (cubeIndex b) +
      (∑ x ∈ C, pairWeight ps (cubeIndex.symm x)) ≤ w + pairingBudget ps
    have hscaled := mul_le_mul_of_nonneg_left hp (show 0 ≤ w from hw)
    rw [mul_add, mul_one] at hscaled
    linarith only [ht, hscaled]

private structure DiameterCertificate where
  degree : DegreeCertificate
  pairs : List WeightedPair

private def DiameterCertificate.vertexScore (c : DiameterCertificate) (x : Fin 512) : ℤ :=
  DegreeCertificate.vertexScore c.degree (cubeIndex x) + pairWeight c.pairs x

private def DiameterCertificate.vertexFloor (c : DiameterCertificate) : ℤ :=
  (List.ofFn fun x : Fin 512 =>
    if DegreeCertificate.cost c.degree (cubeIndex x) ≤ DegreeCertificate.limit c.degree then
      min 0 (c.vertexScore x) else 0).sum

private def DiameterCertificate.hasGap (c : DiameterCertificate) : Prop :=
  2 * (DegreeCertificate.vertexTotal c.degree + pairingBudget c.pairs) +
    DegreeCertificate.edgeTotal c.degree <
    2 * c.vertexFloor + DegreeCertificate.edgeFloor c.degree

private def DiameterCertificate.Valid (c : DiameterCertificate) : Prop :=
  c.pairs.all (fun p => decide (validPair p)) = true ∧ c.hasGap

private instance (c : DiameterCertificate) : Decidable c.Valid := by
  unfold DiameterCertificate.Valid DiameterCertificate.hasGap
  infer_instance

attribute [local instance] Classical.propDecidable

private lemma no_support_with_diameter_certificate (cert : DiameterCertificate)
    (hcert : cert.Valid) {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) +
      2 * DegreeCertificate.deficit cert.degree i = 33) : False := by
  let c := cert.degree
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
  have hbudget := sum_pairWeight_le C hd cert.pairs
    (fun _ hp => all_decide_sound hcert.1 hp)
  let A := (univ : Finset (Q 9)).filter (fun x =>
    DegreeCertificate.cost c x ≤ DegreeCertificate.limit c)
  have hCsub : C ⊆ A := fun x hx => mem_filter.mpr ⟨mem_univ _, hcost x hx⟩
  have hpointLower : cert.vertexFloor ≤ ∑ x ∈ C, cert.vertexScore (cubeIndex.symm x) := by
    have hfloor : (∑ x ∈ A, min 0 (cert.vertexScore (cubeIndex.symm x))) = cert.vertexFloor := by
      dsimp only [A, DiameterCertificate.vertexFloor, c]
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
  simp only [DiameterCertificate.vertexScore, Equiv.apply_symm_apply, sum_add_distrib]
    at hpointLower
  have hgap : 2 * (DegreeCertificate.vertexTotal c + pairingBudget cert.pairs) +
      DegreeCertificate.edgeTotal c < 2 * cert.vertexFloor + DegreeCertificate.edgeFloor c :=
    hcert.2
  linarith

private def exampleCertificate : DiameterCertificate :=
  ⟨DegreeCertificate.mk [2, 2, 4, 4, 5, 5, 5, 5, 5]
      4800 (-420)
      [-870, -870, -1320, -1320, -1752, -1752, -1752, -1752, -1752]
      [150, 150, 0, 0, -144, -144, -144, -144, -144]
      [(0, 120), (10200, 150), (20000, 120), (20100, 300), (100100, 144), (100200, 288),
      (110000, 294), (110100, 147), (120100, -144), (200000, 438), (200200, -144),
      (210000, -147), (300000, -294)],
    [(53, 202, 292), (53, 330, 292), (53, 394, 292), (54, 201, 292), (54, 329, 292),
      (54, 393, 292), (57, 198, 292), (57, 326, 292), (57, 390, 292), (58, 197, 292),
      (58, 325, 292), (58, 389, 292), (85, 170, 292), (85, 298, 292), (85, 394, 292),
      (86, 169, 292), (86, 297, 292), (86, 393, 292), (89, 166, 292), (89, 294, 292),
      (89, 390, 292), (90, 165, 292), (90, 293, 292), (90, 389, 292), (101, 154, 292),
      (101, 282, 292), (101, 394, 292), (102, 153, 292), (102, 281, 292), (102, 393, 292),
      (105, 150, 292), (105, 278, 292), (105, 390, 292), (106, 149, 292), (106, 277, 292),
      (106, 389, 292), (149, 298, 292), (149, 330, 292), (150, 297, 292), (150, 329, 292),
      (153, 294, 292), (153, 326, 292), (154, 293, 292), (154, 325, 292), (165, 282, 292),
      (165, 330, 292), (166, 281, 292), (166, 329, 292), (169, 278, 292), (169, 326, 292),
      (170, 277, 292), (170, 325, 292), (197, 282, 292), (197, 298, 292), (198, 281, 292),
      (198, 297, 292), (201, 278, 292), (201, 294, 292), (202, 277, 292), (202, 293, 292)]⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Check all forbidden pairs and the integer score bounds.
private lemma exampleCertificate_valid : exampleCertificate.Valid := by
  decide +kernel

/-- A balanced cubic support on 66 vertices cannot have this coordinate profile. -/
theorem no_two_two_five_deficit_profile {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) +
      2 * DegreeCertificate.deficit exampleCertificate.degree i = 33) : False :=
  no_support_with_diameter_certificate exampleCertificate exampleCertificate_valid hC hreg hb hhalf

#print axioms no_two_two_five_deficit_profile

/-- The profiles remaining after the first distance-eight certificate. -/
def sixtySixProfilesAfterDiameterCertificate : List (List ℤ) :=
  sixtySixProfilesAfterDegreeCertificates.filter
    (· != List.ofFn (DegreeCertificate.deficit exampleCertificate.degree))

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
