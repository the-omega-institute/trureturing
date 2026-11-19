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
  let limit := c.limit
  (List.ofFn fun x : Fin 512 =>
    if c.cost (cubeIndex x) ≤ limit then min 0 (c.vertexScore (cubeIndex x)) else 0).sum

private def DegreeCertificate.edgeFloor (c : DegreeCertificate) : ℤ :=
  let limit := c.limit
  (List.ofFn fun i : Fin 9 =>
    (List.ofFn fun x : Fin 512 =>
      if c.cost (cubeIndex x) ≤ limit ∧ c.cost (flip (cubeIndex x) i) ≤ limit
      then min 0 (c.edgeScore i (cubeIndex x)) else 0).sum).sum

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
      rw [List.sum_ofFn, sum_filter, ← Equiv.sum_comp cubeIndex]
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
  linarith

-- The digit at position d records how many selected coordinates have deficit d.
-- Equal-deficit permutations therefore leave each tabulated potential unchanged.
private def degreeCertificates1 : List DegreeCertificate := [
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
private lemma degreeCertificates1_valid :
    degreeCertificates1.all (fun c => decide c.hasGap) = true := by
  decide +kernel

private def degreeCertificates2 : List DegreeCertificate := [
  ⟨[0, 1, 4, 4, 4, 5, 5, 5, 5], 2628, 0,
    [0, -648, -660, -660, -660, -1314, -1314, -1314, -1314],
    [432, 216, 216, 216, 216, 0, 0, 0, 0],
    [(20010, 216), (20011, 216), (100010, 216), (100011, 216), (110000, 219), (110001, 219),
      (120010, -219), (120011, -219), (200010, -222), (200011, -222), (210000, -220),
      (210001, -220)]⟩,
  ⟨[0, 2, 2, 3, 3, 5, 5, 5, 5], 276, 0,
    [0, -68, -68, -68, -68, -138, -138, -138, -138], [44, 22, 22, 22, 22, 0, 0, 0, 0],
    [(1200, 22), (1201, 22), (2100, 22), (2101, 22), (100100, 23), (100101, 23), (101000, 23),
      (101001, 23), (101200, -23), (101201, -23), (102100, -23), (102101, -23), (200100, -23),
      (200101, -23), (201000, -23), (201001, -23)]⟩,
  ⟨[0, 2, 2, 3, 4, 4, 5, 5, 5], 936, 0,
    [0, -156, -156, -312, -312, -312, -468, -468, -468], [108, 54, 54, 0, 0, 0, -52, -52, -52],
    [(1100, 54), (1101, 54), (1200, 108), (1201, 108), (10100, 51), (10101, 51), (10200, 102),
      (10201, 102), (11000, 102), (11001, 102), (11100, 51), (11101, 51), (20000, 108),
      (20001, 108), (20100, 54), (20101, 54), (21100, -54), (21101, -54), (100000, 52),
      (100001, 52), (100100, 104), (100101, 104), (100200, 52), (100201, 52), (101000, 52),
      (101001, 52), (101200, -52), (101201, -52), (110000, 52), (110001, 52), (110200, -52),
      (110201, -52), (111000, -52), (111001, -52), (120000, -52), (120001, -52), (200100, -52),
      (200101, -52)]⟩,
  ⟨[0, 2, 3, 3, 3, 4, 5, 5, 5], 213, 0,
    [0, -54, -54, -54, -54, -108, -107, -107, -107], [36, 18, 18, 18, 18, 0, 0, 0, 0],
    [(2100, 18), (2101, 18), (3000, 18), (3001, 18), (10100, 18), (10101, 18), (11000, 18),
      (11001, 18), (12100, -18), (12101, -18), (13000, -18), (13001, -18), (100100, 18),
      (100101, 18), (101000, 18), (101001, 18), (102100, -18), (102101, -18), (110100, -18),
      (110101, -18), (111000, -18), (111001, -18), (200100, -18), (200101, -18), (201000, -18),
      (201001, -18)]⟩,
  ⟨[0, 2, 3, 3, 4, 5, 5, 5, 5], 1752, 0,
    [0, -432, -444, -444, -432, -876, -876, -876, -876], [288, 144, 144, 144, 144, 0, 0, 0, 0],
    [(2100, 144), (2101, 144), (11100, 144), (11101, 144), (100100, 144), (100101, 144),
      (101000, 147), (101001, 147), (102100, -144), (102101, -144), (110000, 144),
      (110001, 144), (111100, -147), (111101, -147), (200100, -148), (200101, -148),
      (201000, -146), (201001, -146), (210000, -148), (210001, -148)]⟩,
  ⟨[0, 2, 3, 4, 4, 5, 5, 5, 5], 156, 0,
    [0, -38, -38, -39, -39, -78, -78, -78, -78], [26, 12, 12, 13, 13, 0, 0, 0, 0],
    [(11100, 13), (11101, 13), (100100, 13), (100101, 13), (101000, 13), (101001, 13),
      (110000, 13), (110001, 13), (111100, -13), (111101, -13), (200100, -13), (200101, -13),
      (201000, -13), (201001, -13), (210000, -13), (210001, -13)]⟩,
  ⟨[0, 2, 4, 4, 4, 4, 5, 5, 5], 1008, 0,
    [0, -336, -336, -336, -336, -336, -336, -336, -336],
    [0, -108, -111, -111, -111, -111, -112, -112, -112],
    [(0, 108), (1, 108), (10100, 111), (10101, 111), (20000, 112), (20001, 112), (30100, 111),
      (30101, 111), (100100, 112), (100101, 112), (110000, 112), (110001, 112), (200000, 112),
      (200001, 112)]⟩
]

private def degreeCertificates3 : List DegreeCertificate := [
  ⟨[0, 2, 4, 4, 5, 5, 5, 5, 5], 830, 0,
    [0, -280, -275, -275, -276, -276, -276, -276, -276],
    [0, -90, -90, -90, -92, -92, -92, -92, -92],
    [(0, 90), (1, 90), (10100, 90), (10101, 90), (20000, 90), (20001, 90), (100100, 92),
      (100101, 92), (110000, 92), (110001, 92), (120100, 92), (120101, 92), (200000, 92),
      (200001, 92)]⟩,
  ⟨[0, 3, 3, 3, 3, 5, 5, 5, 5], 276, 0,
    [0, -69, -69, -69, -69, -138, -138, -138, -138], [44, 23, 23, 23, 23, 0, 0, 0, 0],
    [(3000, 23), (3001, 23), (101000, 23), (101001, 23), (103000, -23), (103001, -23),
      (201000, -23), (201001, -23)]⟩,
  ⟨[0, 3, 3, 3, 4, 5, 5, 5, 5], 996, 0,
    [0, -332, -332, -332, -336, -330, -330, -330, -330],
    [0, -112, -112, -112, -108, -111, -111, -111, -111],
    [(0, 108), (1, 108), (2000, 112), (2001, 112), (11000, 112), (11001, 112), (13000, 108),
      (13001, 108), (101000, 110), (101001, 110), (103000, 111), (103001, 111), (110000, 111),
      (110001, 111), (200000, 110), (200001, 110)]⟩,
  ⟨[0, 3, 3, 3, 5, 5, 5, 5, 5], 1245, 0,
    [0, -415, -415, -415, -414, -414, -414, -414, -414],
    [0, -140, -140, -140, -138, -138, -138, -138, -138],
    [(0, 135), (1, 135), (2000, 140), (2001, 140), (101000, 138), (101001, 138), (103000, 138),
      (103001, 138), (200000, 138), (200001, 138)]⟩,
  ⟨[0, 3, 3, 4, 5, 5, 5, 5, 5], 830, 0,
    [0, -275, -275, -280, -276, -276, -276, -276, -276],
    [0, -90, -90, -90, -92, -92, -92, -92, -92],
    [(0, 90), (1, 90), (2000, 90), (2001, 90), (11000, 90), (11001, 90), (101000, 92),
      (101001, 92), (110000, 92), (110001, 92), (112000, 92), (112001, 92), (200000, 92),
      (200001, 92)]⟩,
  ⟨[0, 3, 4, 4, 4, 4, 5, 5, 5], 1008, 0,
    [0, -336, -336, -336, -336, -336, -336, -336, -336],
    [0, -108, -111, -111, -111, -111, -112, -112, -112],
    [(0, 108), (1, 108), (11000, 111), (11001, 111), (20000, 112), (20001, 112), (31000, 111),
      (31001, 111), (101000, 112), (101001, 112), (110000, 112), (110001, 112), (200000, 112),
      (200001, 112)]⟩,
  ⟨[0, 3, 4, 4, 4, 5, 5, 5, 5], 9, 0,
    [0, -3, -3, -3, -3, -3, -3, -3, -3], [0, -1, -1, -1, -1, -1, -1, -1, -1],
    [(0, 1), (1, 1), (11000, 1), (11001, 1), (20000, 1), (20001, 1), (31000, 1), (31001, 1),
      (101000, 1), (101001, 1), (110000, 1), (110001, 1), (200000, 1), (200001, 1)]⟩
]

private def degreeCertificates4 : List DegreeCertificate := [
  ⟨[0, 3, 4, 4, 5, 5, 5, 5, 5], 830, 0,
    [0, -280, -275, -275, -276, -276, -276, -276, -276],
    [0, -90, -90, -90, -92, -92, -92, -92, -92],
    [(0, 90), (1, 90), (11000, 90), (11001, 90), (20000, 90), (20001, 90), (101000, 92),
      (101001, 92), (110000, 92), (110001, 92), (121000, 92), (121001, 92), (200000, 92),
      (200001, 92)]⟩,
  ⟨[0, 4, 4, 4, 4, 5, 5, 5, 5], 9, 0,
    [0, -3, -3, -3, -3, -3, -3, -3, -3], [0, -1, -1, -1, -1, -1, -1, -1, -1],
    [(0, 1), (1, 1), (20000, 1), (20001, 1), (40000, 1), (40001, 1), (110000, 1), (110001, 1),
      (200000, 1), (200001, 1)]⟩,
  ⟨[1, 1, 1, 4, 4, 4, 5, 5, 5], 6, 0,
    [0, 0, 0, -3, -3, -3, -3, -3, -3], [0, 0, 0, -1, -1, -1, -1, -1, -1],
    [(10000, 1), (10010, 1), (10020, 1), (10030, 1), (20000, 1), (100000, 1), (100010, 1),
      (100020, 1), (100030, 1)]⟩,
  ⟨[1, 1, 2, 3, 3, 5, 5, 5, 5], 4176, 0,
    [-600, -600, -624, -1200, -1200, -1800, -1800, -1800, -1800],
    [192, 192, 192, 0, 0, -204, -204, -204, -204],
    [(0, 192), (1020, 192), (1110, 204), (1120, 408), (2000, 192), (2010, 408), (2020, 192),
      (2100, 384), (100010, 198), (100020, 396), (100100, 204), (100110, 402), (100120, 204),
      (101000, 402), (101010, 201), (101100, 198), (101120, -198), (102010, -198),
      (102100, -204), (200000, 200), (200020, -200), (200110, -200), (201000, -200)]⟩,
  ⟨[1, 1, 2, 3, 4, 4, 5, 5, 5], 10356, (-1152),
    [-1152, -1152, -2304, -2304, -3450, -3450, -4600, -4600, -4600],
    [768, 768, 384, 384, 0, 0, -384, -384, -384],
    [(0, 384), (1100, 384), (1110, 384), (1120, 1152), (10010, 384), (10020, 384), (10100, 768),
      (10110, 768), (10120, 768), (11000, 768), (11010, 768), (11020, 768), (11100, 384),
      (11120, -384), (20000, 1152), (20020, 384), (20120, -768), (21020, -768), (21100, -384),
      (100010, 766), (100020, 768), (100100, 1152), (100110, 384), (100120, 384),
      (101000, 1152), (101010, 384), (101020, 384), (101120, -768), (110000, 766),
      (110100, -384), (110110, -383), (110120, -384), (111000, -384), (111010, -383),
      (120000, -768), (200000, 384), (200010, -384), (200020, -384), (200100, -768),
      (201000, -768)]⟩,
  ⟨[1, 1, 3, 4, 4, 5, 5, 5, 5], 2232, 0,
    [-312, -312, -312, -636, -636, -954, -954, -954, -954],
    [108, 108, 96, 0, 0, -108, -108, -108, -108],
    [(0, 96), (10020, 108), (11000, 108), (11010, 108), (11020, 216), (20000, 96), (20010, 216),
      (100010, 105), (100020, 210), (101000, 108), (101010, 210), (101020, 108), (110000, 210),
      (110010, 105), (111020, -105), (120010, -105), (200000, 104), (200020, -104),
      (201010, -106), (210000, -106)]⟩,
  ⟨[1, 2, 2, 2, 3, 5, 5, 5, 5], 2628, 0,
    [0, -660, -660, -660, -648, -1314, -1314, -1314, -1314],
    [432, 216, 216, 216, 216, 0, 0, 0, 0],
    [(300, 216), (310, 216), (1200, 216), (1210, 216), (100100, 219), (100110, 219),
      (100300, -216), (100310, -216), (101000, 216), (101200, -219), (101210, -219),
      (200100, -220), (200110, -220), (201000, -222)]⟩
]

private def degreeCertificates5 : List DegreeCertificate := [
  ⟨[1, 2, 3, 3, 3, 5, 5, 5, 5], 2556, 0,
    [0, -648, -636, -636, -636, -1278, -1278, -1278, -1278],
    [432, 216, 216, 216, 216, 0, 0, 0, 0],
    [(2100, 216), (2110, 216), (3000, 216), (100100, 216), (100110, 216), (101000, 213),
      (101010, 213), (102100, -213), (102110, -213), (103000, -216), (200100, -216),
      (200110, -216), (201000, -214), (201010, -214)]⟩,
  ⟨[1, 3, 3, 3, 3, 4, 5, 5, 5], 888, 0,
    [0, -222, -222, -222, -222, -444, -444, -444, -444], [144, 75, 75, 75, 75, 0, 0, 0, 0],
    [(3000, 75), (3010, 75), (11000, 75), (11010, 75), (13000, -75), (13010, -75), (101000, 74),
      (101010, 74), (103000, -74), (111000, -74), (111010, -74), (201000, -74), (201010, -74)]⟩,
  ⟨[1, 3, 3, 3, 4, 4, 4, 5, 5], 1926, (-234),
    [-234, -480, -480, -480, -600, -600, -600, -720, -720],
    [72, 0, 0, 0, -42, -42, -42, -81, -81],
    [(0, 72), (2000, 78), (2010, 78), (3000, 72), (3010, 72), (10010, 42), (11000, 120),
      (11010, 120), (12000, 40), (12010, 40), (13000, -42), (13010, -42), (20000, 162),
      (20010, 78), (30000, -36), (30010, -36), (100010, 81), (101000, 162), (101010, 81),
      (110000, 201), (110010, 39), (111000, -40), (111010, -40), (120000, -81), (200000, 162),
      (201000, -78), (210000, -120)]⟩,
  ⟨[1, 3, 3, 3, 5, 5, 5, 5, 5], 2730, 0,
    [-210, -840, -840, -840, -1050, -1050, -1050, -1050, -1050],
    [210, 0, 0, 0, -72, -72, -72, -72, -72],
    [(0, 60), (10, 60), (2000, 70), (2010, 140), (3000, 60), (101000, 140), (101010, 210),
      (102010, -70), (103010, 72), (200000, 210), (200010, 141), (201000, -70), (201010, -140),
      (300000, -141)]⟩,
  ⟨[1, 3, 3, 4, 4, 5, 5, 5, 5], 1992, 0,
    [0, -660, -660, -660, -660, -660, -660, -660, -660],
    [0, -216, -216, -216, -216, -222, -222, -222, -222],
    [(0, 216), (10, 216), (2000, 216), (2010, 216), (11000, 222), (11010, 222), (20000, 216),
      (20010, 216), (22000, 216), (22010, 216), (101000, 219), (101010, 219), (110000, 219),
      (110010, 219), (112000, 219), (200000, 220), (200010, 220)]⟩,
  ⟨[1, 3, 4, 4, 4, 4, 4, 5, 5], 830, 0,
    [0, -280, -276, -276, -276, -276, -276, -275, -275],
    [0, -90, -92, -92, -92, -92, -92, -90, -90],
    [(0, 90), (10, 90), (11000, 92), (11010, 92), (20000, 92), (20010, 92), (31000, 92),
      (101000, 90), (101010, 90), (110000, 92), (110010, 92), (200000, 90), (200010, 90)]⟩,
  ⟨[2, 2, 2, 2, 4, 5, 5, 5, 5], 5040, (-816),
    [-840, -840, -840, -840, -1680, -1680, -1680, -1680, -1680],
    [0, 0, 0, 0, -288, -276, -276, -276, -276],
    [(0, 288), (400, 576), (10100, 276), (10200, 280), (10300, 276), (10400, -288),
      (100100, 279), (100200, 280), (100300, 279), (100400, -276), (110000, 564), (200000, 560),
      (210000, -280)]⟩
]

private def degreeCertificates6 : List DegreeCertificate := [
  ⟨[2, 2, 2, 3, 3, 5, 5, 5, 5], 2112, 0,
    [-304, -304, -304, -600, -600, -906, -906, -906, -906],
    [104, 104, 104, 0, 0, -102, -102, -102, -102],
    [(0, 96), (1200, 100), (1300, 204), (2000, 96), (2100, 200), (100100, 100), (100200, 200),
      (100300, 102), (101000, 201), (101100, 100), (101300, -99), (102100, -100), (200000, 100),
      (200200, -100), (201000, -100)]⟩,
  ⟨[2, 2, 2, 3, 4, 4, 5, 5, 5], 15, 0,
    [-3, -3, -3, -3, -6, -6, -6, -6, -6], [1, 1, 1, 1, 0, 0, 0, 0, 0],
    [(1300, 1), (10200, 1), (11100, 1), (11300, -1), (20000, 1), (20200, -1), (21100, -1),
      (100200, 1), (101100, 1), (101300, -1), (110000, 1), (110200, -1), (111100, -1),
      (120000, -1), (200000, 1), (200200, -1), (210000, -1)]⟩,
  ⟨[2, 2, 2, 4, 4, 4, 4, 5, 5], 1800, 0,
    [-304, -304, -304, -600, -600, -600, -600, -900, -900], [104, 104, 104, 0, 0, 0, 0, -96, -96],
    [(0, 96), (300, 96), (10100, 100), (10200, 200), (10300, 102), (20000, 200), (20100, 100),
      (20300, -100), (30100, -100), (100100, 200), (100200, 100), (110000, 99), (110200, -100),
      (120000, -100), (200000, 192), (200100, -104), (210000, -198)]⟩,
  ⟨[2, 2, 2, 4, 5, 5, 5, 5, 5], 1395, 0,
    [-280, -280, -280, -555, -558, -558, -558, -558, -558], [95, 95, 95, 0, 0, 0, 0, 0, 0],
    [(10200, 95), (100200, 93), (110000, 93), (110200, -93), (200000, 93), (200200, -93),
      (210000, -93), (300000, -93)]⟩,
  ⟨[2, 2, 3, 3, 3, 4, 5, 5, 5], 1332, 0,
    [-333, -333, -336, -336, -336, -342, -666, -666, -666],
    [108, 108, 114, 114, 114, 108, 0, 0, 0],
    [(1200, 114), (2100, 111), (3000, 108), (3200, -108), (10200, 108), (11100, 111),
      (12200, -114), (100100, 111), (101000, 112), (101200, -112), (102100, -111),
      (103000, -114), (110000, 114), (110200, -114), (111100, -111), (200100, -111),
      (201000, -112), (210000, -114)]⟩,
  ⟨[2, 2, 3, 3, 4, 5, 5, 5, 5], 1754, 0,
    [-351, -351, -351, -351, -702, -702, -702, -702, -702], [117, 117, 117, 117, 0, 0, 0, 0, 0],
    [(2200, 116), (10200, 116), (11100, 117), (12000, 116), (12200, -116), (100200, 117),
      (101100, 117), (102000, 117), (102200, -117), (110000, 117), (110200, -117),
      (111100, -117), (112000, -117), (200000, 117), (200200, -117), (201100, -117),
      (210000, -117), (300000, -117)]⟩,
  ⟨[2, 2, 3, 4, 4, 5, 5, 5, 5], 4464, 0,
    [-888, -888, -912, -1800, -1800, -1788, -1788, -1788, -1788],
    [288, 288, 288, 0, 0, 0, 0, 0, 0],
    [(10200, 288), (11100, 300), (20000, 288), (20200, -288), (21100, -288), (100200, 300),
      (101100, 300), (110000, 300), (110200, -300), (111100, -297), (120000, -300),
      (200000, 296), (200200, -296), (201100, -300), (210000, -300), (300000, -300)]⟩
]

private def degreeCertificates7 : List DegreeCertificate := [
  ⟨[2, 2, 4, 4, 4, 4, 5, 5, 5], 1092, (-156),
    [-156, -156, -312, -312, -312, -312, -468, -468, -468], [102, 102, 51, 51, 51, 51, 0, 0, 0],
    [(20000, 52), (20100, 52), (100100, 52), (100200, 52), (110000, 104), (120000, -52),
      (120100, -52), (200000, 52), (200100, -52), (200200, -52), (210000, -104), (300000, -48)]⟩,
  ⟨[2, 3, 3, 3, 3, 5, 5, 5, 5], 216, (-28),
    [-28, -54, -54, -54, -54, -81, -81, -81, -81], [18, 9, 9, 9, 9, 0, 0, 0, 0],
    [(3000, 9), (3100, 9), (4100, -18), (101000, 9), (101100, 9), (103000, -9), (200000, 18),
      (201000, -9), (201100, -9), (300000, -18)]⟩,
  ⟨[2, 3, 3, 3, 4, 5, 5, 5, 5], 3672, (-468),
    [-468, -912, -912, -912, -1368, -1377, -1377, -1377, -1377],
    [288, 156, 156, 156, 0, 0, 0, 0, 0],
    [(3000, 144), (3100, 144), (11000, 156), (11100, 156), (13000, -144), (13100, -144),
      (101000, 153), (101100, 153), (103000, -153), (110000, 306), (111000, -153),
      (111100, -153), (200000, 306), (201000, -152), (201100, -152), (210000, -306),
      (300000, -306)]⟩,
  ⟨[2, 3, 3, 4, 5, 5, 5, 5, 5], 930, 0,
    [-190, -185, -185, -370, -372, -372, -372, -372, -372], [60, 60, 60, 0, 0, 0, 0, 0, 0],
    [(11100, 60), (12000, 60), (101100, 62), (102000, 62), (110000, 62), (111100, -62),
      (112000, -62), (200000, 62), (201100, -62), (202000, -62), (210000, -62), (300000, -62)]⟩,
  ⟨[3, 3, 3, 3, 3, 4, 5, 5, 5], 150, (-30),
    [-30, -30, -30, -30, -30, -30, -60, -60, -60], [0, 0, 0, 0, 0, 0, -10, -10, -10],
    [(0, 15), (2000, 9), (3000, 9), (4000, 9), (5000, -15), (11000, 9), (12000, 9),
      (101000, 19), (110000, 20), (200000, 10), (201000, -10), (210000, -10)]⟩,
  ⟨[3, 3, 4, 4, 4, 4, 5, 5, 5], 32580, (-4644),
    [-4662, -4662, -9306, -9306, -9306, -9306, -13968, -13968, -13968],
    [3096, 3096, 1548, 1548, 1548, 1548, 0, 0, 0],
    [(20000, 1554), (21000, 1551), (40000, -1548), (101000, 1554), (102000, 1548),
      (110000, 3102), (120000, -1552), (121000, -1552), (200000, 1548), (201000, -1554),
      (202000, -1548), (210000, -3102), (300000, -1548)]⟩,
  ⟨[3, 4, 4, 4, 4, 4, 4, 5, 5], 6360, (-1560),
    [-780, -1590, -1590, -1590, -1590, -1590, -1590, -2370, -2370],
    [240, 0, 0, 0, 0, 0, 0, -270, -270],
    [(0, 240), (11000, 260), (20000, 528), (21000, 264), (101000, 540), (110000, 795),
      (120000, -264), (200000, 540), (201000, -240), (210000, -530)]⟩
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact score sums for this batch.
private lemma degreeCertificates2_valid :
    degreeCertificates2.all (fun c => decide c.hasGap) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact score sums for this batch.
private lemma degreeCertificates3_valid :
    degreeCertificates3.all (fun c => decide c.hasGap) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact score sums for this batch.
private lemma degreeCertificates4_valid :
    degreeCertificates4.all (fun c => decide c.hasGap) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact score sums for this batch.
private lemma degreeCertificates5_valid :
    degreeCertificates5.all (fun c => decide c.hasGap) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact score sums for this batch.
private lemma degreeCertificates6_valid :
    degreeCertificates6.all (fun c => decide c.hasGap) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Evaluate the exact score sums for this batch.
private lemma degreeCertificates7_valid :
    degreeCertificates7.all (fun c => decide c.hasGap) = true := by
  decide +kernel

private def degreeCertificates : List DegreeCertificate :=
  degreeCertificates1 ++ degreeCertificates2 ++ degreeCertificates3 ++ degreeCertificates4 ++
    degreeCertificates5 ++ degreeCertificates6 ++ degreeCertificates7

private lemma degreeCertificates_valid :
    degreeCertificates.all (fun c => decide c.hasGap) = true := by
  simp only [degreeCertificates, List.all_append, degreeCertificates1_valid,
    degreeCertificates2_valid, degreeCertificates3_valid, degreeCertificates4_valid,
    degreeCertificates5_valid, degreeCertificates6_valid, degreeCertificates7_valid, Bool.and_true]

/-- The normalized coordinate profiles left by the degree and direction counts. -/
def sixtySixProfilesAfterDegreeCertificates : List (List ℤ) :=
  sixtySixProfilesAfterThreeSix.filter (fun profile =>
    !(degreeCertificates.map (fun c => List.ofFn c.deficit)).contains profile)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Reduce the preceding finite profile filters and the 50 certified exclusions.
theorem sixtySixProfilesAfterDegreeCertificates_length :
    sixtySixProfilesAfterDegreeCertificates.length = 104 := by
  decide +kernel

/-- Every 66-point Huang-balanced cubic support normalizes to one of the
104 profiles surviving the degree certificates. -/
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
