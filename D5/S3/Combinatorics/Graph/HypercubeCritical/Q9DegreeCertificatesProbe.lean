import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThreeSixDeficitsProbe

/-! Integer combinations of the cardinality and degree equations of a 66-point cube support. -/

set_option autoImplicit false

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced directionEdges directionEndpoints direction_edge_count)
local notation "flip" => BalancedCriticalSpectrum.flip
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private endpoint_card_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private endpoint_weight_sum endpoint_weight_swap coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private cubic_parity_half_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private cubeIndex from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThreeSixDeficitsProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

private structure DegreeCertificate where
  profile : List ℤ
  sizeCoefficient : ℤ
  parityCoefficient : ℤ
  halfCoefficients : List ℤ
  directionCoefficients : List ℤ
  potentials : List (ℕ × ℤ)

private def DegreeCertificate.deficit (c : DegreeCertificate) (i : Fin 9) : ℤ :=
  c.profile[i.val]?.getD 0

private def DegreeCertificate.cost (c : DegreeCertificate) (x : Q 9) : ℤ :=
  ∑ i : Fin 9, if x i then c.deficit i else 0

private def DegreeCertificate.limit (c : DegreeCertificate) : ℤ :=
  ((∑ i, c.deficit i) - 4) / 2

private def DegreeCertificate.potential (c : DegreeCertificate) (x : Q 9) : ℤ :=
  let signature := ∑ i : Fin 9, if x i then 10 ^ (c.deficit i).toNat else 0
  ((c.potentials.find? fun p => p.1 == signature).map Prod.snd).getD 0

private def DegreeCertificate.half (c : DegreeCertificate) (i : Fin 9) : ℤ :=
  c.halfCoefficients[i.val]?.getD 0

private def DegreeCertificate.direction (c : DegreeCertificate) (i : Fin 9) : ℤ :=
  c.directionCoefficients[i.val]?.getD 0

private def DegreeCertificate.vertexScore (c : DegreeCertificate) (x : Q 9) : ℤ :=
  c.sizeCoefficient + (if cubeParity x then c.parityCoefficient else 0) +
    (∑ i : Fin 9, if x i then c.half i else 0) - 3 * c.potential x

private def DegreeCertificate.edgeScore (c : DegreeCertificate) (i : Fin 9) (x : Q 9) : ℤ :=
  c.potential x + c.potential (flip x i) + c.direction i

private def DegreeCertificate.vertexFloor (c : DegreeCertificate) : ℤ :=
  ∑ x : Fin 512, if c.cost (cubeIndex x) ≤ c.limit
    then min 0 (c.vertexScore (cubeIndex x)) else 0

private def DegreeCertificate.edgeFloor (c : DegreeCertificate) : ℤ :=
  ∑ i : Fin 9, ∑ x : Fin 512,
    if c.cost (cubeIndex x) ≤ c.limit ∧ c.cost (flip (cubeIndex x) i) ≤ c.limit
      then min 0 (c.edgeScore i (cubeIndex x)) else 0

private def DegreeCertificate.vertexTotal (c : DegreeCertificate) : ℤ :=
  66 * c.sizeCoefficient + 33 * c.parityCoefficient +
    ∑ i, (33 - 2 * c.deficit i) * c.half i

private def DegreeCertificate.edgeTotal (c : DegreeCertificate) : ℤ :=
  ∑ i, 22 * c.direction i

attribute [local instance] Classical.propDecidable

private lemma sum_vertex_scores (c : DegreeCertificate) (C : Finset (Q 9)) (hC : C.card = 66)
    (hparity : (C.filter (fun x => cubeParity x = true)).card = 33)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * c.deficit i = 33) :
    (∑ x ∈ C, c.vertexScore x) = c.vertexTotal - 3 * ∑ x ∈ C, c.potential x := by
  have hpar : (∑ x ∈ C, if cubeParity x then c.parityCoefficient else 0) =
      33 * c.parityCoefficient := by
    rw [← sum_filter, sum_const, hparity, nsmul_eq_mul]
    rfl
  have hhalfSum : (∑ x ∈ C, ∑ i : Fin 9, if x i then c.half i else 0) =
      ∑ i : Fin 9, (33 - 2 * c.deficit i) * c.half i := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    linarith only [hhalf i]
  simp only [DegreeCertificate.vertexScore, DegreeCertificate.vertexTotal, sum_sub_distrib,
    sum_add_distrib, sum_const, hC, nsmul_eq_mul, hpar, hhalfSum, ← mul_sum, Nat.cast_ofNat]

private lemma sum_edge_scores (c : DegreeCertificate) (C : Finset (Q 9))
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hedge : ∀ i, directionEdges C i = 11) :
    (∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, c.edgeScore i x) =
      6 * (∑ x ∈ C, c.potential x) + c.edgeTotal := by
  have hdir (i : Fin 9) : (directionEndpoints C i).card = 22 := by
    rw [endpoint_card_twice, hedge i]
  simp only [DegreeCertificate.edgeScore, DegreeCertificate.edgeTotal, sum_add_distrib,
    endpoint_weight_swap, sum_const, hdir, nsmul_eq_mul, Nat.cast_ofNat]
  rw [endpoint_weight_sum C hreg]
  ring

private lemma no_support_with_degree_certificate
    (c : DegreeCertificate)
    (hcert : 2 * c.vertexTotal + c.edgeTotal < 2 * c.vertexFloor + c.edgeFloor)
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter (fun x => x i = true)).card : ℤ) + 2 * c.deficit i = 33) :
    False := by
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hcost (x : Q 9) (hx : x ∈ C) : c.cost x ≤ c.limit := by
    have hcap : ((shell C x 7).card : ℤ) ≤ 8 := by
      exact_mod_cast sixty_six_distance_seven_le_eight hC hreg hb hd hx
    have hw := coordinate_profile_weight_bound hC hreg hb (fun _ => true) c.deficit hhalf hx
    change 2 * c.cost x + 12 ≤ (∑ i, c.deficit i) + (shell C x 7).card at hw
    unfold DegreeCertificate.limit
    omega
  have hdir (i : Fin 9) : directionEdges C i = 11 := by
    have h := direction_edge_count (d := 3) C hreg hb i
    omega
  have hpoint := sum_vertex_scores c C hC (cubic_parity_half_card hC hreg true) hhalf
  have hedge := sum_edge_scores c C hreg hdir
  let A := (univ : Finset (Q 9)).filter (fun x => c.cost x ≤ c.limit)
  have hCsub : C ⊆ A := fun x hx => mem_filter.mpr ⟨mem_univ _, hcost x hx⟩
  have hpointLower : c.vertexFloor ≤ ∑ x ∈ C, c.vertexScore x := by
    have hfloor : (∑ x ∈ A, min 0 (c.vertexScore x)) = c.vertexFloor := by
      dsimp only [A, DegreeCertificate.vertexFloor]
      rw [sum_filter, ← Equiv.sum_comp cubeIndex]
    rw [← hfloor]
    exact (sum_le_sum_of_subset_of_nonpos hCsub (fun _ _ _ => min_le_left _ _)).trans
      (sum_le_sum fun _ _ => min_le_right _ _)
  have hedgeLower : c.edgeFloor ≤ ∑ i : Fin 9, ∑ x ∈ directionEndpoints C i, c.edgeScore i x := by
    have hi (i : Fin 9) : directionEndpoints C i ⊆
        A.filter (fun x => c.cost (flip x i) ≤ c.limit) := by
      intro x hx
      obtain ⟨hx, hf⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hCsub hx, hcost _ hf⟩
    have hfloor : (∑ i : Fin 9, ∑ x ∈ A.filter (fun x => c.cost (flip x i) ≤ c.limit),
        min 0 (c.edgeScore i x)) = c.edgeFloor := by
      unfold DegreeCertificate.edgeFloor
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

-- The digit at position d records how many selected coordinates have deficit d.
-- Equal-deficit permutations therefore leave each tabulated potential unchanged.
private def degreeCertificates : List DegreeCertificate := [
  ⟨[1, 3, 4, 4, 4, 4, 5, 5, 5], 874, 0,
    [0, -291, -291, -291, -291, -291, -291, -291, -291],
    [0, -97, -97, -97, -97, -97, -97, -97, -97],
    [(0, 97), (10, 97), (11000, 97), (11010, 97), (20000, 97), (20010, 97), (31000, 97),
      (101000, 97), (101010, 97), (110000, 97), (110010, 97), (200000, 97), (200010, 97)]⟩,
  ⟨[1, 3, 4, 4, 5, 5, 5, 5, 5], 865, 0,
    [0, -288, -288, -288, -288, -288, -288, -288, -288],
    [0, -96, -96, -96, -96, -96, -96, -96, -96],
    [(0, 96), (10, 96), (11000, 96), (11010, 96), (20000, 96), (20010, 96), (101000, 96),
      (101010, 96), (110000, 96), (110010, 96), (121000, 96), (200000, 96), (200010, 96)]⟩,
  ⟨[1, 4, 4, 4, 4, 4, 5, 5, 5], 865, 0,
    [0, -288, -288, -288, -288, -288, -288, -288, -288],
    [0, -96, -96, -96, -96, -96, -96, -96, -96],
    [(0, 96), (10, 96), (20000, 96), (20010, 96), (40000, 96), (110000, 96), (110010, 96),
      (200000, 96), (200010, 96)]⟩,
  ⟨[1, 4, 4, 4, 4, 5, 5, 5, 5], 9, 0,
    [0, -3, -3, -3, -3, -3, -3, -3, -3], [0, -1, -1, -1, -1, -1, -1, -1, -1],
    [(0, 1), (10, 1), (20000, 1), (20010, 1), (40000, 1), (110000, 1), (110010, 1), (200000, 1),
      (200010, 1)]⟩,
  ⟨[1, 4, 4, 4, 5, 5, 5, 5, 5], 865, 0,
    [0, -288, -288, -288, -288, -288, -288, -288, -288],
    [0, -96, -96, -96, -96, -96, -96, -96, -96],
    [(0, 96), (10, 96), (20000, 96), (20010, 96), (110000, 96), (110010, 96), (130000, 96),
      (200000, 96), (200010, 96)]⟩,
  ⟨[2, 2, 3, 5, 5, 5, 5, 5, 5], 13500, (-2256),
    [-2256, -2256, -2244, -4500, -4500, -4500, -4500, -4500, -4500],
    [0, 0, 0, -754, -754, -754, -754, -754, -754],
    [(0, 756), (1200, 756), (100100, 753), (100200, 754), (101000, 752), (101100, 751),
      (200000, 1500), (300000, -753)]⟩,
  ⟨[2, 4, 4, 4, 4, 4, 5, 5, 5], 865, 0,
    [0, -288, -288, -288, -288, -288, -288, -288, -288],
    [0, -96, -96, -96, -96, -96, -96, -96, -96],
    [(0, 96), (100, 96), (20000, 96), (20100, 96), (40000, 96), (110000, 96), (110100, 96),
      (200000, 96), (200100, 96)]⟩,
  ⟨[2, 4, 4, 4, 5, 5, 5, 5, 5], 865, 0,
    [0, -288, -288, -288, -288, -288, -288, -288, -288],
    [0, -96, -96, -96, -96, -96, -96, -96, -96],
    [(0, 96), (100, 96), (20000, 96), (20100, 96), (110000, 96), (110100, 96), (130000, 96),
      (200000, 96), (200100, 96)]⟩
]

private def DegreeCertificate.hasGap (c : DegreeCertificate) : Prop :=
  2 * c.vertexTotal + c.edgeTotal < 2 * c.vertexFloor + c.edgeFloor

private instance (c : DegreeCertificate) : Decidable c.hasGap :=
  Int.decLt _ _

private lemma all_decide_sound {α : Type} {p : α → Prop} [DecidablePred p] {xs : List α}
    (h : xs.all (fun x => decide (p x)) = true) {x : α} (hx : x ∈ xs) : p x :=
  of_decide_eq_true (List.all_eq_true.mp h x hx)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- The kernel sums the vertex and edge scores for all eight certificates.
private lemma degreeCertificates_valid :
    degreeCertificates.all (fun c => decide c.hasGap) = true := by
  decide +kernel

/-- The normalized coordinate profiles left by the degree and direction counts. -/
def sixtySixProfilesAfterDegreeCertificates : List (List ℤ) :=
  sixtySixProfilesAfterThreeSix.filter (fun profile =>
    !(degreeCertificates.map (fun c => List.ofFn c.deficit)).contains profile)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- This reduces the preceding finite profile filters along with the eight exclusions.
theorem sixtySixProfilesAfterDegreeCertificates_length :
    sixtySixProfilesAfterDegreeCertificates.length = 146 := by
  decide +kernel

/-- Every 66-point Huang-balanced cubic support normalizes to one of the
146 profiles surviving the degree certificates. -/
theorem q9_sixty_six_mem_profiles_after_degree_certificates {C : Finset (Q 9)}
    (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterDegreeCertificates := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hprofile⟩ :=
    q9_sixty_six_mem_profiles_after_three_six hC hreg hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  simp only [sixtySixProfilesAfterDegreeCertificates, List.mem_filter, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
  refine ⟨hprofile, ?_⟩
  rintro ⟨c, hc, he⟩
  have hcert : c.hasGap := all_decide_sound degreeCertificates_valid hc
  have hr : c.deficit = r := List.ofFn_inj.mp he
  exact no_support_with_degree_certificate c hcert hS hregS hbS (by simpa only [hr] using hhalf)

#print axioms q9_sixty_six_mem_profiles_after_degree_certificates

end D5.S3.Combinatorics.Graph.HypercubeCritical
