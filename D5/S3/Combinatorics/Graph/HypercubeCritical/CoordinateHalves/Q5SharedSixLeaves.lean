import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SmallParitySupport
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParallel
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Six-leaf geometry in the five-cube for Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves

open Finset Q5SmallParitySupport

/-- The six leaves of the parallel three-leaf stars centered at 0 and 3. -/
def leaves : Finset (BitVec 5) := {4, 7, 8, 11, 16, 19}

private def adjacent (x y : BitVec 5) : Prop :=
  x ^^^ y ∈ ({1, 2, 4, 8, 16} : Finset (BitVec 5))

private instance (x y : BitVec 5) : Decidable (adjacent x y) :=
  inferInstanceAs (Decidable (_ ∈ (_ : Finset (BitVec 5))))

/-- The degree of a vertex in the induced five-cube on `S`. -/
def degree (S : Finset (BitVec 5)) (x : BitVec 5) : Nat :=
  (S.filter (adjacent x)).card

private abbrev side (S : Finset (BitVec 5)) (p : Bool) :=
  S.filter fun x => bitParity x = p

private theorem bitParity_xor (x y : BitVec 5) :
    bitParity (x ^^^ y) = (bitParity x ^^ bitParity y) := by
  simp only [bitParity, BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm]

private theorem parity_of_adjacent {x y : BitVec 5} (h : adjacent x y) :
    bitParity y = !bitParity x := by
  have units : ∀ i : Fin 32, BitVec.ofFin i ∈ ({1, 2, 4, 8, 16} : Finset (BitVec 5)) →
      bitParity (BitVec.ofFin i) = true := by decide
  have hp := units (x ^^^ y).toFin h
  change bitParity (x ^^^ y) = true at hp
  rw [bitParity_xor] at hp
  have flip : ∀ p q : Bool, (p ^^ q) = true → q = !p := by decide
  exact flip _ _ hp

private theorem neighbors_on_opposite_side {S : Finset (BitVec 5)} {x : BitVec 5}
    {p : Bool} (hx : bitParity x = p) :
    (side S (!p)).filter (adjacent x) = S.filter (adjacent x) := by
  ext y
  simp only [side, mem_filter, and_assoc, and_congr_right_iff]
  intro _
  exact ⟨And.right, fun h => ⟨by rw [parity_of_adjacent h, hx], h⟩⟩

private theorem card_sides (S : Finset (BitVec 5)) :
    (side S false).card + (side S true).card = S.card := by
  simpa only [side, Bool.not_eq_false] using
    (card_filter_add_card_filter_not (s := S) (fun x => bitParity x = false))

private theorem union_sides (S : Finset (BitVec 5)) : side S false ∪ side S true = S := by
  ext x
  cases hx : bitParity x <;> simp [side, hx]

private theorem sum_degrees_sides (S : Finset (BitVec 5)) :
    ∑ x ∈ side S false, degree S x = ∑ y ∈ side S true, degree S y := by
  calc
    _ = ∑ x ∈ side S false, ((side S true).bipartiteAbove adjacent x).card := by
      apply sum_congr rfl
      intro x hx
      exact congrArg card (neighbors_on_opposite_side (mem_filter.mp hx).2).symm
    _ = ∑ y ∈ side S true, ((side S false).bipartiteBelow adjacent y).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ = _ := by
      apply sum_congr rfl
      intro y hy
      unfold bipartiteBelow degree
      simp_rw [show ∀ x, adjacent x y = adjacent y x by
        intro x
        simp only [adjacent, BitVec.xor_comm x y]]
      exact congrArg card (neighbors_on_opposite_side (mem_filter.mp hy).2)

private theorem side_eq_oddNeighborImage {S : Finset (BitVec 5)}
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) (p : Bool) :
    side S (!p) = oddNeighborImage (side S p) := by
  have units : bitParity 1#5 = true ∧ bitParity 2#5 = true ∧ bitParity 4#5 = true ∧
      bitParity 8#5 = true ∧ bitParity 16#5 = true := by decide
  obtain ⟨h1, h2, h4, h8, h16⟩ := units
  have row (x : BitVec 5) : neighborParity (side S p) x =
      if bitParity x = !p then neighborParity S x else false := by
    cases p <;> cases hx : bitParity x <;>
      simp [side, neighborParity, mem_filter, bitParity_xor, hx, h1, h2, h4, h8, h16]
  ext x
  rw [mem_oddNeighborImage, row, ← hpar x]
  by_cases h : bitParity x = !p <;> simp [side, h]

private theorem leaves_card : leaves.card = 6 := by decide

private theorem leaves_odd : ∀ x ∈ leaves, bitParity x = true := by decide

private theorem normalized_card_even {S : Finset (BitVec 5)}
    (hF : leaves ⊆ S) (hdeg : ∀ x ∈ S, degree S x = if x ∈ leaves then 1 else 3) :
    3 * (side S false).card = 6 + 3 * ((side S true).card - 6) := by
  have hFO : leaves ⊆ side S true := fun x hx => mem_filter.mpr ⟨hF hx, leaves_odd x hx⟩
  have he : (∑ x ∈ side S false, degree S x) = (side S false).card * 3 := by
    apply sum_const_nat
    intro x hx
    have hn : x ∉ leaves := fun hl => by
      have hh := (mem_filter.mp hx).2
      rw [leaves_odd x hl] at hh
      contradiction
    exact (hdeg x (mem_filter.mp hx).1).trans (ite_eq_right hn)
  have ho : (∑ x ∈ side S true, degree S x) =
      ((side S true).card - 6) * 3 + 6 := by
    rw [← sum_sdiff hFO]
    have h1 : (∑ x ∈ (side S true \ leaves), degree S x) =
        ((side S true).card - 6) * 3 := by
      rw [← leaves_card, ← card_sdiff_of_subset hFO]
      exact sum_const_nat fun x hx =>
        (hdeg x (mem_filter.mp (mem_sdiff.mp hx).1).1).trans (ite_eq_right (mem_sdiff.mp hx).2)
    have h2 : (∑ x ∈ leaves, degree S x) = 6 := by
      rw [sum_const_nat (fun x hx => (hdeg x (hF hx)).trans (ite_eq_left hx)), leaves_card]
    rw [h1, h2]
  have h := sum_degrees_sides S
  rw [he, ho] at h
  omega

private def evenWord (i : Fin 16) : BitVec 5 :=
  BitVec.cons (bitParity (BitVec.ofNat 5 i.val)) (BitVec.ofNat 4 i.val)

private theorem evenWord_decode (x : BitVec 5) (hx : bitParity x = false) :
    evenWord (x.setWidth 4).toFin = x := by
  have h : ∀ i : Fin 32, bitParity (BitVec.ofFin i) = false →
      evenWord ((BitVec.ofFin (w := 5) i).setWidth 4).toFin = BitVec.ofFin i := by decide
  exact h x.toFin hx

private def vertexMask (x : BitVec 5) : BitVec 32 :=
  1 <<< x.toNat

private def neighborhoodMask (x : BitVec 5) : BitVec 32 :=
  vertexMask (x ^^^ 1) ||| vertexMask (x ^^^ 2) ||| vertexMask (x ^^^ 4) |||
    vertexMask (x ^^^ 8) ||| vertexMask (x ^^^ 16)

private theorem neighborhoodMask_bit (x y : BitVec 5) :
    (neighborhoodMask x).getLsbD y.toNat = true ↔ adjacent x y := by
  have h : ∀ i j : Fin 32, (neighborhoodMask (BitVec.ofFin i)).getLsbD j.val = true ↔
      adjacent (BitVec.ofFin i) (BitVec.ofFin j) := by decide
  exact h x.toFin y.toFin

private abbrev coversLeaves (E : Finset (BitVec 5)) : Prop :=
  degree E 4 = 1 ∧ degree E 7 = 1 ∧ degree E 8 = 1 ∧
    degree E 11 = 1 ∧ degree E 16 = 1 ∧ degree E 19 = 1

private theorem coversLeaves_even {S : Finset (BitVec 5)}
    (hF : leaves ⊆ S) (hdeg : ∀ x ∈ S, degree S x = if x ∈ leaves then 1 else 3) :
    coversLeaves (side S false) := by
  have hd (x : BitVec 5) (hx : x ∈ leaves) : degree (side S false) x = 1 := by
    unfold degree
    rw [show (side S false).filter (adjacent x) = _ from
      neighbors_on_opposite_side (leaves_odd x hx)]
    exact (hdeg x (hF hx)).trans (ite_eq_left hx)
  exact ⟨hd 4 (by decide), hd 7 (by decide), hd 8 (by decide),
    hd 11 (by decide), hd 16 (by decide), hd 19 (by decide)⟩

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the pairs in the even half of the five-cube.
private theorem even_pair_table : ∀ i j : Fin 16,
    let a := evenWord i
    let b := evenWord j
    a ≠ b → coversLeaves {a, b} → ({a, b} : Finset (BitVec 5)) = {0, 3} := by
  decide

set_option maxHeartbeats 4000000 in
-- The common neighbor is the unique odd center. The leaf degree condition
-- then restricts the three even centers to the two sets in the conclusion.
private theorem even_triple_table : ∀ i j k : Fin 16,
    let a := evenWord i
    let b := evenWord j
    let c := evenWord k
    a ≠ b → a ≠ c → b ≠ c →
    neighborhoodMask a &&& neighborhoodMask b &&& neighborhoodMask c ≠ 0 →
    coversLeaves {a, b, c} →
    ({a, b, c} : Finset (BitVec 5)) = {5, 9, 17} ∨
      ({a, b, c} : Finset (BitVec 5)) = {6, 10, 18} := by
  decide

private theorem common_neighbor_of_degree_three {a b c x : BitVec 5}
    (h : degree {a, b, c} x = 3) :
    neighborhoodMask a &&& neighborhoodMask b &&& neighborhoodMask c ≠ 0 := by
  have hcard : ({a, b, c} : Finset (BitVec 5)).card ≤ 3 := by
    exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))
  have he : ({a, b, c} : Finset (BitVec 5)).filter (adjacent x) = {a, b, c} :=
    eq_of_subset_of_card_le (filter_subset _ _) (h.trans_ge hcard)
  have ha (y : BitVec 5) (hy : y ∈ ({a, b, c} : Finset (BitVec 5))) :
      (neighborhoodMask y).getLsbD x.toNat = true := by
    apply (neighborhoodMask_bit _ _).mpr
    rw [← he] at hy
    simpa only [adjacent, BitVec.xor_comm y x] using (mem_filter.mp hy).2
  intro hz
  have hh := congrArg (fun m : BitVec 32 => m.getLsbD x.toNat) hz
  simp [BitVec.getLsbD_and, ha a (by simp), ha b (by simp), ha c (by simp)] at hh

private theorem degree_odd_center {S : Finset (BitVec 5)}
    (hF : leaves ⊆ S) (hdeg : ∀ x ∈ S, degree S x = if x ∈ leaves then 1 else 3)
    (hO : (side S true).card = 7) :
    ∃ x : BitVec 5, degree (side S false) x = 3 := by
  have hFO : leaves ⊆ side S true := fun x hx => mem_filter.mpr ⟨hF hx, leaves_odd x hx⟩
  have hdiff := card_sdiff_add_card_eq_card hFO
  rw [hO, leaves_card] at hdiff
  have hd : ((side S true) \ leaves).card = 1 := by omega
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < ((side S true) \ leaves).card)
  obtain ⟨hxO, hxF⟩ := mem_sdiff.mp hx
  refine ⟨x, ?_⟩
  unfold degree
  rw [show (side S false).filter (adjacent x) = _ from
    neighbors_on_opposite_side (mem_filter.mp hxO).2]
  exact (hdeg x (mem_filter.mp hxO).1).trans (ite_eq_right hxF)

private theorem carrier_eq_of_even_side {S E : Finset (BitVec 5)}
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) (hE : side S false = E) :
    S = E ∪ oddNeighborImage E := by
  rw [← hE, ← side_eq_oddNeighborImage hpar false]
  exact (union_sides S).symm

/-- A parity-fixed eight-vertex carrier with the prescribed six leaves adds the two
centers of the parallel stars. A ten-vertex carrier adds a center and its three
neighbors, along one of the two remaining axes. -/
theorem classify_normalized_carrier {S : Finset (BitVec 5)}
    (hF : leaves ⊆ S)
    (hdeg : ∀ x ∈ S, degree S x = if x ∈ leaves then 1 else 3)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    (S.card = 8 → S \ leaves = {0, 3}) ∧
    (S.card = 10 → S \ leaves = {1, 5, 9, 17} ∨ S \ leaves = {2, 6, 10, 18}) := by
  have hFO : leaves ⊆ side S true := fun x hx => mem_filter.mpr ⟨hF hx, leaves_odd x hx⟩
  have hO := card_le_card hFO
  rw [leaves_card] at hO
  have hsum := card_sides S
  have hbalance := normalized_card_even hF hdeg
  have hcover := coversLeaves_even hF hdeg
  constructor
  · intro h8
    obtain ⟨a, b, hab, hE⟩ := card_eq_two.mp (by omega : (side S false).card = 2)
    have ha := evenWord_decode a ((mem_filter.mp (show a ∈ side S false by simp [hE])).2)
    have hb := evenWord_decode b ((mem_filter.mp (show b ∈ side S false by simp [hE])).2)
    have he : ({a, b} : Finset (BitVec 5)) = {0, 3} := by
      simpa only [ha, hb] using even_pair_table (a.setWidth 4).toFin (b.setWidth 4).toFin
        (by rwa [ha, hb]) (by simpa only [ha, hb, ← hE] using hcover)
    rw [carrier_eq_of_even_side hpar (hE.trans he)]
    decide
  · intro h10
    obtain ⟨a, b, c, hab, hac, hbc, hE⟩ :=
      card_eq_three.mp (by omega : (side S false).card = 3)
    obtain ⟨x, hx⟩ := degree_odd_center hF hdeg (by omega)
    rw [hE] at hx hcover
    have ha := evenWord_decode a ((mem_filter.mp (show a ∈ side S false by simp [hE])).2)
    have hb := evenWord_decode b ((mem_filter.mp (show b ∈ side S false by simp [hE])).2)
    have hc := evenWord_decode c ((mem_filter.mp (show c ∈ side S false by simp [hE])).2)
    have he := even_triple_table (a.setWidth 4).toFin (b.setWidth 4).toFin (c.setWidth 4).toFin
      (by rwa [ha, hb]) (by rwa [ha, hc]) (by rwa [hb, hc])
      (by simpa only [ha, hb, hc] using common_neighbor_of_degree_three hx)
      (by simpa only [ha, hb, hc] using hcover)
    simp only [ha, hb, hc] at he
    rcases he with he | he
    · left
      rw [carrier_eq_of_even_side hpar (hE.trans he)]
      decide
    · right
      rw [carrier_eq_of_even_side hpar (hE.trans he)]
      decide

#print axioms classify_normalized_carrier

private theorem sum_degrees {S L T : Finset (BitVec 5)}
    (hdeg : ∀ x ∈ S, degree S x = if x ∈ L then 1 else 3) (hTS : T ⊆ S) :
    (∑ x ∈ T, degree S x) = T.card + 2 * (T \ L).card := by
  have hsub : T ∩ L ⊆ T := inter_subset_left
  have hdiff : T \ (T ∩ L) = T \ L := by
    ext x
    simp only [mem_sdiff, mem_inter]
    tauto
  have hsum := sum_sdiff (f := degree S) hsub
  have hcard := card_sdiff_add_card_eq_card hsub
  have h1 : (∑ x ∈ T ∩ L, degree S x) = (T ∩ L).card * 1 :=
    sum_const_nat fun x hx => (hdeg x (hTS (mem_inter.mp hx).1)).trans
      (ite_eq_left (mem_inter.mp hx).2)
  have h3 : (∑ x ∈ T \ L, degree S x) = (T \ L).card * 3 :=
    sum_const_nat fun x hx => (hdeg x (hTS (mem_sdiff.mp hx).1)).trans
      (ite_eq_right (mem_sdiff.mp hx).2)
  rw [hdiff, h1, h3] at hsum
  rw [hdiff] at hcard
  omega

private theorem adjacent_iff_flip (x y : BitVec 5) :
    adjacent x y ↔ ∃ i : Fin 5, x ^^^ BitVec.twoPow 5 i.val = y := by
  have h : ∀ i j : Fin 32, adjacent (BitVec.ofFin i) (BitVec.ofFin j) ↔
      ∃ k : Fin 5, BitVec.ofFin i ^^^ BitVec.twoPow 5 k.val = BitVec.ofFin j := by decide
  exact h x.toFin y.toFin

private theorem degree_eq_card_flips (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree S x = ((univ : Finset (Fin 5)).filter fun i =>
      x ^^^ BitVec.twoPow 5 i.val ∈ S).card := by
  let flip : Fin 5 ↪ BitVec 5 := ⟨fun i => x ^^^ BitVec.twoPow 5 i.val, by
    have hinj : ∀ i j : Fin 5, BitVec.twoPow 5 i.val = BitVec.twoPow 5 j.val → i = j := by decide
    intro i j hij
    exact hinj i j ((BitVec.xor_right_inj x).mp hij)⟩
  let D := (univ : Finset (Fin 5)).filter (fun i => flip i ∈ S)
  have hmap : S.filter (adjacent x) = D.map flip := by
    ext y
    simp only [mem_filter, mem_map, adjacent_iff_flip, D, mem_univ, true_and]
    constructor
    · rintro ⟨hy, i, rfl⟩
      exact ⟨i, hy, rfl⟩
    · rintro ⟨i, hy, rfl⟩
      exact ⟨hy, i, rfl⟩
  unfold degree
  rw [hmap, card_map]
  rfl

private theorem small_side_of_six_leaves {S L : Finset (BitVec 5)}
    (hS : S.card = 8) (hL : L.card = 6) (hLS : L ⊆ S)
    (hdeg : ∀ x ∈ S, degree S x = if x ∈ L then 1 else 3)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    ∃ p : Bool, (side S p).card = 2 ∧ (side S (!p)).card = 6 := by
  have hdis : Disjoint (side S false) (side S true) := by
    apply disjoint_left.mpr
    intro x hx hy
    have he := (mem_filter.mp hx).2
    have ho := (mem_filter.mp hy).2
    rw [he] at ho
    contradiction
  have hsum := sum_union (f := degree S) hdis
  rw [union_sides S] at hsum
  have htotal := sum_degrees hdeg (Subset.refl S)
  have hcenters := card_sdiff_add_card_eq_card hLS
  rw [hS, hL] at hcenters
  have hbalance := sum_degrees_sides S
  have he := sum_degrees (T := side S false) hdeg (filter_subset _ S)
  have ho := sum_degrees (T := side S true) hdeg (filter_subset _ S)
  have hle0 := card_le_card (sdiff_subset (s := side S false) (t := L))
  have hle1 := card_le_card (sdiff_subset (s := side S true) (t := L))
  have hc := card_sides S
  have hcases : (side S false).card = 2 ∨ (side S true).card = 2 ∨
      ((side S false).card = 4 ∧ (side S true).card = 4) := by omega
  rcases hcases with h | h | ⟨hE, hO⟩
  · exact ⟨false, h, by change (side S true).card = 6; omega⟩
  · exact ⟨true, h, by change (side S false).card = 6; omega⟩
  · obtain ⟨d, _, hd⟩ := parallel_of_neighborParity_of_card_four_four hpar hE hO
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < (S \ L).card)
    obtain ⟨hxS, hxL⟩ := mem_sdiff.mp hx
    have hf : ((univ : Finset (Fin 5)).filter fun i =>
        x ^^^ BitVec.twoPow 5 i.val ∈ S) = {d} := by
      ext i
      simp [hd x hxS i]
    have h := hdeg x hxS
    rw [ite_eq_right hxL, degree_eq_card_flips, hf, card_singleton] at h
    omega

private theorem leaves_eq_larger_side {S L : Finset (BitVec 5)} {p : Bool}
    (hL : L.card = 6) (hdeg : ∀ x ∈ S, degree S x = if x ∈ L then 1 else 3)
    (hp : (side S p).card = 2) (hq : (side S (!p)).card = 6) :
    L = side S (!p) := by
  symm
  apply eq_of_subset_of_card_le _ (by omega)
  intro x hx
  by_contra hn
  have h := (hdeg x (mem_filter.mp hx).1).trans (ite_eq_right hn)
  have he : (side S p).filter (adjacent x) = S.filter (adjacent x) := by
    simpa only [Bool.not_not] using neighbors_on_opposite_side (mem_filter.mp hx).2
  unfold degree at h
  rw [← he] at h
  have hle := card_le_card (filter_subset (adjacent x) (side S p))
  omega

private theorem mem_image_xor {A : Finset (BitVec 5)} {x a : BitVec 5} :
    x ∈ A.image (fun y => y ^^^ a) ↔ x ^^^ a ∈ A := by
  simp only [mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [BitVec.xor_assoc] using hy
  · intro hx
    exact ⟨x ^^^ a, hx, by simp [BitVec.xor_assoc]⟩

private theorem oddNeighborImage_image_xor (a : BitVec 5) (A : Finset (BitVec 5)) :
    oddNeighborImage (A.image (fun y => y ^^^ a)) =
      (oddNeighborImage A).image (fun y => y ^^^ a) := by
  ext x
  have commute (k : BitVec 5) : x ^^^ k ^^^ a = x ^^^ a ^^^ k := by
    simp only [BitVec.xor_assoc, BitVec.xor_comm k a]
  simp only [mem_image_xor, mem_oddNeighborImage, neighborParity, commute]

private def pairPermutation (v : BitVec 5) : Equiv.Perm (Fin 5) :=
  let axes := (List.finRange 5).filter (fun i => v.getLsbD i.val)
  let i := axes[0]?.getD 0
  let j := axes[1]?.getD 1
  let q := Equiv.swap (0 : Fin 5) i
  q.trans (Equiv.swap (q 1) j)

set_option maxHeartbeats 2000000 in
-- Translate one center to zero, then check the sixteen possible displacements.
private theorem pair_geometry : ∀ i : Fin 16,
    let v := evenWord i
    (oddNeighborImage {0, v}).card = 6 →
    (v.cpop.toNat = 2 ∧ oddNeighborImage {0, v} =
      leaves.image (Q7FourStarParallel.permuteBits (pairPermutation v))) := by
  decide

/-- In an eight-vertex parity-fixed carrier with six leaves, the two degree-three
vertices differ in two coordinates. Translating by one center and permuting the
coordinates takes the leaf set to the six leaves of the normalized stars. -/
theorem normalize_eight_carrier {S L : Finset (BitVec 5)}
    (hS : S.card = 8) (hL : L.card = 6) (hLS : L ⊆ S)
    (hdeg : ∀ x ∈ S, degree S x = if x ∈ L then 1 else 3)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    ∃ a b : BitVec 5, ∃ p : Equiv.Perm (Fin 5),
      S \ L = {a, b} ∧ (a ^^^ b).cpop.toNat = 2 ∧
      L.image (fun x => x ^^^ a) = leaves.image (Q7FourStarParallel.permuteBits p) := by
  obtain ⟨sideParity, hp, hq⟩ := small_side_of_six_leaves hS hL hLS hdeg hpar
  have hleaf := leaves_eq_larger_side hL hdeg hp hq
  obtain ⟨a, b, _, hpair⟩ := card_eq_two.mp hp
  have ha := (mem_filter.mp (show a ∈ side S sideParity by simp [hpair])).2
  have hb := (mem_filter.mp (show b ∈ side S sideParity by simp [hpair])).2
  have hdisjoint : side S sideParity = S \ L := by
    ext x
    rw [hleaf]
    cases sideParity <;> cases hx : bitParity x <;> simp [side, hx]
  have htranslate : L.image (fun x => x ^^^ a) = oddNeighborImage {0, b ^^^ a} := by
    rw [hleaf, side_eq_oddNeighborImage hpar sideParity, ← oddNeighborImage_image_xor, hpair]
    simp
  have hcard : (oddNeighborImage {0, b ^^^ a}).card = 6 := by
    rw [← htranslate, card_image_of_injective _ (fun _ _ h => (BitVec.xor_left_inj a).mp h), hL]
  have hba : bitParity (b ^^^ a) = false := by rw [bitParity_xor, ha, hb, Bool.xor_self]
  have hdecode := evenWord_decode _ hba
  have hg := pair_geometry ((b ^^^ a).setWidth 4).toFin
  simp only [hdecode] at hg
  obtain ⟨hdist, hperm⟩ := hg hcard
  exact ⟨a, b, pairPermutation (b ^^^ a), hdisjoint.symm.trans hpair,
    by simpa only [BitVec.xor_comm a b] using hdist, htranslate.trans hperm⟩

#print axioms normalize_eight_carrier

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves
