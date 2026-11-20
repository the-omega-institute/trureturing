import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjectionRows
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridHubBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport

/-! A balanced cubic support of size 72 projecting into the nine-point grid omits
the central fiber when each coordinate half has at least 28 vertices. With at
least 30 vertices in each half, the entire grid projection is impossible. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9SignedProjection (join fiber signedRow)
open Q9ThetaProjection (leftCode)
open Q9GridProjectionRows (gridEnvelope grid_projection_rows)
open Q9GridHubBound (signed_hub_card_le_six)
open Q5SmallParitySupport (neighborParity eight_le_card_of_neighborParity)
open private pattern rightBlock leftCode_join join_blocks flipCode flip_pattern
  prefixSign prefixSign_eq row_degree occupation flips_one from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private flip_join_left flip_join_right sign_join_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
open private mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

private noncomputable def carrier (S : Finset (Q 9)) (k : BitVec 4) : Finset (Q 5) := by
  classical
  exact univ.filter fun y => join (pattern k) y ∈ S

private theorem mem_carrier (S : Finset (Q 9)) (k : BitVec 4) (y : Q 5) :
    y ∈ carrier S k ↔ join (pattern k) y ∈ S := by
  simp [carrier]

private theorem mem_carrier_iff_fiber_ne_zero {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (k : BitVec 4) (y : Q 5) :
    y ∈ carrier S k ↔ fiber z y (pattern k) ≠ 0 := by
  rw [mem_carrier]
  constructor
  · intro hy
    change z (join (pattern k) y) ≠ 0
    rcases hunit _ hy with hp | hm <;> omega
  · intro hy
    by_contra hn
    exact hy (hzero _ hn)

private theorem grid_carrier_equalities {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hgrid : ∀ u ∈ S, leftCode u ∈ gridEnvelope)
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (hrow : ∀ u, signedRow z u = 3 * z u) :
    carrier S 4 = carrier S 2 ∧ carrier S 5 = carrier S 3 ∧
    carrier S 8 = carrier S 1 ∧ carrier S 10 = carrier S 3 ∧
    carrier S 12 = carrier S 3 := by
  let h (k : BitVec 4) (y : Q 5) := fiber z y (pattern k)
  have rows (y : Q 5) := grid_projection_rows hgrid hzero hrow y
  have selected (k : BitVec 4) (y : Q 5) : y ∈ carrier S k ↔ h k y ≠ 0 :=
    mem_carrier_iff_fiber_ne_zero hunit hzero k y
  have same {k l : BitVec 4} (he : ∀ y, h k y = h l y) : carrier S k = carrier S l := by
    ext y
    simp only [selected, he]
  have same_neg {k l : BitVec 4} (he : ∀ y, h k y = -h l y) : carrier S k = carrier S l := by
    ext y
    simp only [selected, he, neg_ne_zero]
  exact ⟨same (fun y => (rows y).1), same (fun y => (rows y).2.1),
    same (fun y => (rows y).2.2.1), same_neg (fun y => (rows y).2.2.2.1),
    same_neg (fun y => (rows y).2.2.2.2.1)⟩

open Classical in
private theorem no_common_carrier {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (h4 : carrier S 4 = carrier S 2) (h8 : carrier S 8 = carrier S 1) :
    ∀ y ∈ carrier S 0, y ∈ carrier S 1 → y ∉ carrier S 2 := by
  intro y hy hyB hyC
  have h1 := (mem_carrier S 1 y).mp hyB
  have h2 := (mem_carrier S 2 y).mp hyC
  have h4y := (mem_carrier S 4 y).mp (h4.symm ▸ hyC)
  have h8y := (mem_carrier S 8 y).mp (h8.symm ▸ hyB)
  have hdeg := row_degree hr (k := 0) (a := 1) (b := 2) (c := 4) (d := 8)
    (by decide +kernel) ((mem_carrier S 0 y).mp hy)
  simp only [occupation, h1, h2, h4y, h8y, ite_true] at hdeg
  omega

open Classical in
private theorem twelve_direction_edges {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72) (i : Fin 9) :
    directionEdges S i = 12 := by
  have hd := direction_edge_count (d := 3) S hr hb i
  rw [hsize] at hd
  omega

private theorem card_carrier (S : Finset (Q 9)) (k : BitVec 4) :
    (carrier S k).card = (S.filter fun u => leftCode u = k).card := by
  classical
  refine card_bij' (fun y _ => join (pattern k) y) (fun u _ => rightBlock u) ?_ ?_ ?_ ?_
  · intro y hy
    exact mem_filter.mpr ⟨(mem_carrier S k y).mp hy, leftCode_join k y⟩
  · intro u hu
    obtain ⟨huS, hku⟩ := mem_filter.mp hu
    apply (mem_carrier S k (rightBlock u)).mpr
    rw [← hku, join_blocks]
    exact huS
  · intro y _
    funext i
    simp only [rightBlock, join, Fin.append_right]
  · intro u hu
    rw [← (mem_filter.mp hu).2, join_blocks]

private theorem card_sum_carriers {S T : Finset (Q 9)} (hsub : T ⊆ S)
    (hgrid : ∀ u ∈ S, leftCode u ∈ gridEnvelope) :
    T.card = ∑ k ∈ gridEnvelope, (carrier T k).card := by
  classical
  simpa only [card_carrier] using
    (card_eq_sum_card_fiberwise (f := leftCode) (s := T) (t := gridEnvelope)
      (fun u hu => hgrid u (hsub hu)))

private theorem sum_gridEnvelope (f : BitVec 4 → ℕ) :
    (∑ k ∈ gridEnvelope, f k) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 8 + (f 10 + f 12))))))) := by
  let codes : List (BitVec 4) := [0, 1, 2, 3, 4, 5, 8, 10, 12]
  have hcodes : gridEnvelope = codes.toFinset := by decide +kernel
  have hnodup : codes.Nodup := by decide +kernel
  rw [hcodes, List.sum_toFinset f hnodup]
  simp only [codes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem carrier_cut (S : Finset (Q 9)) (k : BitVec 4) (i : Fin 4) :
    carrier (S.filter fun u => u (i.castAdd 5) = true) k =
      cond (pattern k i) (carrier S k) ∅ := by
  classical
  ext y
  rw [mem_carrier, mem_filter]
  simp only [join, Fin.append_left]
  cases pattern k i <;> simp [mem_carrier, join]

private theorem carrier_false_endpoints (S : Finset (Q 9)) (k : BitVec 4) (i : Fin 4) :
    carrier (S.filter fun u => u (i.castAdd 5) = false ∧ flip u (i.castAdd 5) ∈ S) k =
      cond (pattern k i) ∅ (carrier S k ∩ carrier S (flipCode k i)) := by
  classical
  ext y
  rw [mem_carrier, mem_filter, flip_join_left, flip_pattern]
  simp only [join, Fin.append_left]
  cases pattern k i <;> simp [mem_carrier, join]

private theorem outside_grid_carrier {S : Finset (Q 9)}
    (hgrid : ∀ u ∈ S, leftCode u ∈ gridEnvelope) {k : BitVec 4}
    (hk : k ∉ gridEnvelope) : carrier S k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hk (by simpa only [leftCode_join] using hgrid _ ((mem_carrier S k y).mp hy))

-- The same partition counts all vertices, both true cuts, and the two sets of false endpoints.
private theorem carrier_cardinalities {S : Finset (Q 9)}
    (hgrid : ∀ u ∈ S, leftCode u ∈ gridEnvelope)
    (h4 : carrier S 4 = carrier S 2) (h5 : carrier S 5 = carrier S 3)
    (h8 : carrier S 8 = carrier S 1) (h10 : carrier S 10 = carrier S 3)
    (h12 : carrier S 12 = carrier S 3) :
    let A := carrier S 0
    let B := carrier S 1
    let C := carrier S 2
    let D := carrier S 3
    S.card = A.card + 2 * B.card + 2 * C.card + 4 * D.card ∧
    (S.filter fun u => u ((0 : Fin 4).castAdd 5) = true).card = B.card + 2 * D.card ∧
    (S.filter fun u => u ((1 : Fin 4).castAdd 5) = true).card = C.card + 2 * D.card ∧
    directionEdges S ((0 : Fin 4).castAdd 5) = (A ∩ B).card + 2 * (C ∩ D).card ∧
    directionEdges S ((1 : Fin 4).castAdd 5) = (A ∩ C).card + 2 * (B ∩ D).card := by
  classical
  intro A B C D
  have hcut (i : Fin 4) :
      (S.filter fun u => u (i.castAdd 5) = true).card =
        ∑ k ∈ gridEnvelope, (cond (pattern k i) (carrier S k) ∅).card := by
    rw [card_sum_carriers (filter_subset _ S) hgrid]
    simp only [carrier_cut]
  have hedge (i : Fin 4) :
      directionEdges S (i.castAdd 5) =
        ∑ k ∈ gridEnvelope,
          (cond (pattern k i) ∅ (carrier S k ∩ carrier S (flipCode k i))).card := by
    rw [directionEdges, card_sum_carriers (filter_subset _ S) hgrid]
    simp only [carrier_false_endpoints]
  have h6 := outside_grid_carrier hgrid (k := 6) (by decide +kernel)
  have h7 := outside_grid_carrier hgrid (k := 7) (by decide +kernel)
  have h9 := outside_grid_carrier hgrid (k := 9) (by decide +kernel)
  have h11 := outside_grid_carrier hgrid (k := 11) (by decide +kernel)
  have h13 := outside_grid_carrier hgrid (k := 13) (by decide +kernel)
  have h14 := outside_grid_carrier hgrid (k := 14) (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [card_sum_carriers (Subset.rfl : S ⊆ S) hgrid, sum_gridEnvelope, h4, h5, h8, h10, h12]
    change A.card + (B.card + (C.card + (D.card + (C.card +
      (D.card + (B.card + (D.card + D.card))))))) = _
    omega
  · rw [hcut, sum_gridEnvelope]
    change 0 + (B.card + (0 + (D.card + (0 + ((carrier S 5).card + (0 + (0 + 0))))))) = _
    rw [h5]
    dsimp only [D]
    omega
  · rw [hcut, sum_gridEnvelope]
    change 0 + (0 + (C.card + (D.card + (0 + (0 + (0 + ((carrier S 10).card + 0))))))) = _
    rw [h10]
    dsimp only [D]
    omega
  · rw [hedge, sum_gridEnvelope]
    change (A ∩ B).card + (0 + ((C ∩ D).card + (0 +
      ((carrier S 4 ∩ carrier S 5).card + (0 +
      ((carrier S 8 ∩ carrier S 9).card + ((carrier S 10 ∩ carrier S 11).card +
      (carrier S 12 ∩ carrier S 13).card))))))) = _
    simp only [h4, h5, h9, h11, h13, inter_empty, card_empty, zero_add, add_zero]
    dsimp only [C, D]
    omega
  · rw [hedge, sum_gridEnvelope]
    change (A ∩ C).card + ((B ∩ D).card + (0 + (0 +
      ((carrier S 4 ∩ carrier S 6).card + ((carrier S 5 ∩ carrier S 7).card +
      ((carrier S 8 ∩ carrier S 10).card + (0 +
      (carrier S 12 ∩ carrier S 14).card))))))) = _
    simp only [h6, h7, h8, h10, h14, inter_empty, card_empty, zero_add, add_zero]
    dsimp only [B, D]
    omega

private theorem flip_cubeBitVec (x : BitVec 5) (i : Fin 5) :
    flip (cubeBitVec 5 x) i = cubeBitVec 5 (x ^^^ BitVec.twoPow 5 i.val) := by
  have hmask : ∀ j : Fin 5, BitVec.twoPow 5 j.val = BitVec.ofNat 5 (2 ^ j.val) := by
    decide +kernel
  rw [hmask]
  exact (cubeBitVec_xor_single x i).symm

private theorem mem_encoded (A : Finset (Q 5)) (x : BitVec 5) :
    x ∈ A.image (cubeBitVec 5).symm ↔ cubeBitVec 5 x ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := mem_image.mp hx
    rw [← he, Equiv.apply_symm_apply]
    exact hy
  · intro hx
    exact mem_image.mpr ⟨cubeBitVec 5 x, hx, (cubeBitVec 5).symm_apply_apply x⟩

private def bitValue (b : Bool) : ZMod 2 := cond b 1 0

private theorem bitValue_xor (p q : Bool) : bitValue (p ^^ q) = bitValue p + bitValue q := by
  cases p <;> cases q <;> decide +kernel

private theorem bitValue_injective : Function.Injective bitValue := by
  have h : ∀ p q : Bool, bitValue p = bitValue q → p = q := by decide +kernel
  exact fun _ _ => h _ _

private theorem encoded_neighborParity {A : Finset (Q 5)} {a b c : Q 5 → ℤ}
    (hunit : ∀ y ∈ A, a y = 1 ∨ a y = -1) (hzero : ∀ y ∉ A, a y = 0)
    (hrow : ∀ y, signedRow a y = 3 * a y - 2 * b y - 2 * c y) :
    ∀ x, decide (x ∈ A.image (cubeBitVec 5).symm) =
      neighborParity (A.image (cubeBitVec 5).symm) x := by
  let E := A.image (cubeBitVec 5).symm
  have hneg : (-1 : ZMod 2) = 1 := by decide +kernel
  have htwo : (2 : ZMod 2) = 0 := by decide +kernel
  have hthree : (3 : ZMod 2) = 1 := by decide +kernel
  have hcast (x : BitVec 5) : (a (cubeBitVec 5 x) : ZMod 2) = bitValue (decide (x ∈ E)) := by
    by_cases hx : x ∈ E
    · rcases hunit _ ((mem_encoded A x).mp hx) with hp | hm
      · simp [hp, hx, bitValue]
      · simp [hm, hx, bitValue, hneg]
    · have hy : cubeBitVec 5 x ∉ A := fun hy => hx ((mem_encoded A x).mpr hy)
      simp [hzero _ hy, hx, bitValue]
  intro x
  change decide (x ∈ E) = neighborParity E x
  have hsum :
      (∑ i : Fin 5, bitValue (decide ((x ^^^ BitVec.twoPow 5 i.val) ∈ E))) =
        bitValue (decide (x ∈ E)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod 2)) (hrow (cubeBitVec 5 x))
    simpa only [signedRow, Int.cast_sum, Int.cast_mul, Int.cast_sub, truePrefixSign,
      Int.cast_pow, Int.cast_neg, Int.cast_one, hneg, one_pow, one_mul, Int.cast_ofNat,
      hthree, htwo, zero_mul, sub_zero, flip_cubeBitVec, hcast] using h
  apply bitValue_injective
  have masks :
      BitVec.twoPow 5 (0 : Fin 5).val = 1 ∧ BitVec.twoPow 5 (1 : Fin 5).val = 2 ∧
        BitVec.twoPow 5 (2 : Fin 5).val = 4 ∧ BitVec.twoPow 5 (3 : Fin 5).val = 8 ∧
        BitVec.twoPow 5 (4 : Fin 5).val = 16 := by decide +kernel
  obtain ⟨mask0, mask1, mask2, mask3, mask4⟩ := masks
  simpa only [neighborParity, bitValue_xor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.reduceSucc, mask0, mask1, mask2, mask3, mask4, add_zero, add_assoc] using hsum.symm

open Classical in
private theorem encoded_degree {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3) :
    let E := (carrier S 0).image (cubeBitVec 5).symm
    ∀ x ∈ E, ((univ : Finset (Fin 5)).filter fun i =>
      (x ^^^ BitVec.twoPow 5 i.val) ∈ E).card ≤ 3 := by
  intro E x hx
  let y := cubeBitVec 5 x
  have hy : join (pattern 0) y ∈ S := (mem_carrier S 0 y).mp ((mem_encoded _ x).mp hx)
  let T := (univ : Finset (Fin 5)).filter fun i => (x ^^^ BitVec.twoPow 5 i.val) ∈ E
  have hsub : T.map (Fin.natAddEmb 4) ⊆ directions S (join (pattern 0) y) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    have hjE : (x ^^^ BitVec.twoPow 5 j.val) ∈ E := (mem_filter.mp hj).2
    rw [mem_directions]
    change flip (join (pattern 0) y) (j.natAdd 4) ∈ S
    rw [flip_join_right]
    change join (pattern 0) (flip (cubeBitVec 5 x) j) ∈ S
    rw [flip_cubeBitVec]
    exact (mem_carrier S 0 _).mp ((mem_encoded _ _).mp hjE)
  have hcard := card_le_card hsub
  rw [card_map, regular_directions S hr hy] at hcard
  exact hcard

open Classical in
/-- The central code is absent from the grid projection of a balanced induced
cubic support of size 72 whose coordinate halves each have at least 28 vertices. -/
theorem grid_projection_excludes_zero {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72)
    (hhalves : ∀ (i : Fin 9) (b : Bool), 28 ≤ (S.filter fun u => u i = b).card)
    (hgrid : ∀ u ∈ S, leftCode u ∈ gridEnvelope) :
    ∀ u ∈ S, leftCode u ≠ 0 := by
  classical
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hr hb
  let h (k : BitVec 4) (y : Q 5) := fiber z y (pattern k)
  let A := carrier S 0
  let B := carrier S 1
  let C := carrier S 2
  let D := carrier S 3
  have selected (k : BitVec 4) (y : Q 5) : y ∈ carrier S k ↔ h k y ≠ 0 :=
    mem_carrier_iff_fiber_ne_zero hunit hzero k y
  have rows (y : Q 5) := grid_projection_rows hgrid hzero hrow y
  obtain ⟨h4, h5, h8, h10, h12⟩ := grid_carrier_equalities hgrid hunit hzero hrow
  obtain ⟨htotal, hcut0, hcut1, hedge0, hedge1⟩ :=
    carrier_cardinalities hgrid h4 h5 h8 h10 h12
  have hB : 28 ≤ B.card + 2 * D.card := hcut0 ▸ hhalves ((0 : Fin 4).castAdd 5) true
  have hC : 28 ≤ C.card + 2 * D.card := hcut1 ▸ hhalves ((1 : Fin 4).castAdd 5) true
  have hBedge : (A ∩ B).card + 2 * (C ∩ D).card = 12 :=
    hedge0 ▸ twelve_direction_edges hr hb hsize ((0 : Fin 4).castAdd 5)
  have hCedge : (A ∩ C).card + 2 * (B ∩ D).card = 12 :=
    hedge1 ▸ twelve_direction_edges hr hb hsize ((1 : Fin 4).castAdd 5)
  have hno : ∀ y ∈ A, y ∈ B → y ∉ C := no_common_carrier hr h4 h8
  have hprefix : ∀ i : Fin 4, prefixSign 0 i = 1 := by decide +kernel
  have agree (i : Fin 4) (y : Q 5) (hy : y ∈ A) (hi : y ∈ carrier S (flipCode 0 i)) :
      h 0 y = h (flipCode 0 i) y := by
    have hx := (mem_carrier S 0 y).mp hy
    have hf : flip (join (pattern 0) y) (i.castAdd 5) ∈ S := by
      rw [flip_join_left, flip_pattern]
      exact (mem_carrier _ _ _).mp hi
    have hs := hsign _ hx _ hf
    rw [sign_join_left, prefixSign_eq, hprefix, flip_join_left, flip_pattern] at hs
    change 1 = h 0 y * h (flipCode 0 i) y at hs
    have ha : h 0 y = 1 ∨ h 0 y = -1 := hunit _ hx
    rcases ha with hp | hm
    · rw [hp] at hs ⊢
      omega
    · rw [hm] at hs ⊢
      omega
  have hab (y : Q 5) (ha : h 0 y ≠ 0) (hb' : h 1 y ≠ 0) : h 0 y = h 1 y :=
    agree 0 y ((selected 0 y).mpr ha) ((selected 1 y).mpr hb')
  have hac (y : Q 5) (ha : h 0 y ≠ 0) (hc : h 2 y ≠ 0) : h 0 y = h 2 y :=
    agree 1 y ((selected 0 y).mpr ha) ((selected 2 y).mpr hc)
  have hrowA (y : Q 5) : signedRow (h 0) y = 3 * h 0 y - 2 * h 1 y - 2 * h 2 y := by
    obtain ⟨_, _, _, _, _, ha, _, _, _, _⟩ := rows y
    exact ha
  have hrowSum (y : Q 5) :
      signedRow (fun v => h 1 v + h 2 v) y = 2 * h 0 y - 3 * (h 1 y + h 2 y) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hs⟩ := rows y
    exact hs
  have hsmall : A.card ≤ 6 :=
    signed_hub_card_le_six (D := D) hno (htotal.symm.trans hsize) hB hC hBedge hCedge
      (selected 0) (selected 1) (selected 2) hab hac hrowA hrowSum
  let E := A.image (cubeBitVec 5).symm
  have hcard : E.card = A.card := card_image_of_injective _ (cubeBitVec 5).symm.injective
  have hpar : ∀ x, decide (x ∈ E) = neighborParity E x :=
    encoded_neighborParity (A := A) (a := h 0)
      (fun y hy => hunit _ ((mem_carrier S 0 y).mp hy))
      (fun y hy => hzero _ (fun hs => hy ((mem_carrier S 0 y).mpr hs))) hrowA
  intro u hu hcode
  have hy : rightBlock u ∈ A := by
    apply (mem_carrier S 0 (rightBlock u)).mpr
    rw [← hcode, join_blocks]
    exact hu
  have hne : E.Nonempty := ⟨_, mem_image_of_mem _ hy⟩
  have hlarge : 8 ≤ E.card := eight_le_card_of_neighborParity hne hpar (encoded_degree hr)
  omega

#print axioms grid_projection_excludes_zero

open Classical in
/-- A balanced induced cubic support of size 72 whose coordinate halves each
have at least 30 vertices cannot project into the nine-point grid. -/
theorem no_grid_projection_of_thirty_halves {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72)
    (hhalves : ∀ (i : Fin 9) (b : Bool), 30 ≤ (S.filter fun u => u i = b).card) :
    ¬ (∀ u ∈ S, leftCode u ∈ gridEnvelope) := by
  classical
  intro hgrid
  obtain ⟨z, hunit, hzero, _, hrow⟩ := q9_integral_true_prefix_switching hr hb
  obtain ⟨h4, h5, h8, h10, h12⟩ := grid_carrier_equalities hgrid hunit hzero hrow
  let A := carrier S 0
  let B := carrier S 1
  let C := carrier S 2
  let D := carrier S 3
  obtain ⟨htotal, hcut0, hcut1, hedge0, hedge1⟩ :=
    carrier_cardinalities hgrid h4 h5 h8 h10 h12
  have hcard : A.card + 2 * B.card + 2 * C.card + 4 * D.card = 72 := htotal.symm.trans hsize
  have hB : 30 ≤ B.card + 2 * D.card := hcut0 ▸ hhalves ((0 : Fin 4).castAdd 5) true
  have hC : 30 ≤ C.card + 2 * D.card := hcut1 ▸ hhalves ((1 : Fin 4).castAdd 5) true
  have hcuts : A.card + B.card + C.card ≤ 12 := by omega
  have hBedge : (A ∩ B).card + 2 * (C ∩ D).card = 12 :=
    hedge0 ▸ twelve_direction_edges hr hb hsize ((0 : Fin 4).castAdd 5)
  have hCedge : (A ∩ C).card + 2 * (B ∩ D).card = 12 :=
    hedge1 ▸ twelve_direction_edges hr hb hsize ((1 : Fin 4).castAdd 5)
  -- The two edge counts use disjoint portions of the central carrier.
  have hno : ∀ y ∈ A, y ∈ B → y ∉ C := no_common_carrier hr h4 h8
  have hdisj : Disjoint (A ∩ B) (A ∩ C) := by
    refine Finset.disjoint_left.mpr ?_
    intro y hyAB hyAC
    exact hno y (mem_inter.mp hyAB).1 (mem_inter.mp hyAB).2 (mem_inter.mp hyAC).2
  have hhub : (A ∩ B).card + (A ∩ C).card ≤ A.card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset inter_subset_left inter_subset_left)
  have hBDle : (B ∩ D).card ≤ B.card := card_le_card inter_subset_left
  have hCDle : (C ∩ D).card ≤ C.card := card_le_card inter_subset_left
  have hsum : 24 ≤ A.card + 2 * (B.card + C.card) := by omega
  have hA : A = ∅ := card_eq_zero.mp (by omega)
  have hBC : B.card + C.card = 12 := by omega
  rw [hA, empty_inter, card_empty, zero_add] at hBedge hCedge
  have hBD : (B ∩ D).card = 6 := by omega
  have hCD : (C ∩ D).card = 6 := by omega
  have hBcard : B.card = 6 := by omega
  have hsub : B ⊆ D := by
    have heq : B ∩ D = B :=
      eq_of_subset_of_card_le inter_subset_left (by rw [hBD, hBcard])
    exact heq ▸ inter_subset_right
  -- A third neighbor of a code-1 vertex must lie in the same carrier.
  obtain ⟨y, hy⟩ : B.Nonempty := card_pos.mp (by rw [hBcard]; decide)
  have hy1 := (mem_carrier S 1 y).mp hy
  have hy3 := (mem_carrier S 3 y).mp (hsub hy)
  have hy5 := (mem_carrier S 5 y).mp (h5.symm ▸ hsub hy)
  have hy0 : join (pattern 0) y ∉ S := by
    rw [← mem_carrier, show carrier S 0 = ∅ from hA]
    exact notMem_empty y
  have h9 := outside_grid_carrier hgrid (k := 9) (by decide +kernel)
  have hy9 : join (pattern 9) y ∉ S := by
    rw [← mem_carrier, h9]
    exact notMem_empty y
  have hdeg := row_degree hr flips_one hy1
  obtain ⟨j, hj⟩ : ∃ j : Fin 5, join (pattern 1) (flip y j) ∈ S := by
    by_contra! hnone
    simp only [occupation, hy0, hy3, hy5, hy9, hnone, ite_true, ite_false,
      Finset.sum_const_zero] at hdeg
    omega
  have hj3 := (mem_carrier S 3 _).mp (hsub ((mem_carrier S 1 _).mpr hj))
  have hleft (v : Q 5) :
      flip (join (pattern 1) v) ((1 : Fin 4).castAdd 5) = join (pattern 3) v := by
    rw [flip_join_left, flip_pattern, flips_one.2.1]
  have hij : (1 : Fin 4).castAdd 5 ≠ j.natAdd 4 := by
    intro heq
    have hv := congrArg Fin.val heq
    change 1 = 4 + j.val at hv
    omega
  exact BalancedCubeGirth.no_selected_square hb hij hy1 (by rwa [hleft])
    (by rwa [flip_join_right]) (by rwa [hleft, flip_join_right])

#print axioms no_grid_projection_of_thirty_halves

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection
