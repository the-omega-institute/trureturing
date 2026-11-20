/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarOccupancy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q7FourStarOccupancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Occupation parity forces parallelism for four separated seven-cube stars. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParallel
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Pairwise

/-! The occupation version of the four-star parallelism step in the missing-pair cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarOccupancy

open Q7FourStarParity (starDefect separatedFromRoot)
open Q7FourStarParallel (four_star_parallel)
open private axisChoices starMask rootClosedNeighborhood mem_axisChoices centerInBlock
  exists_centerInBlock from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParity
open private axisBit axis_bit axis_unused axisList vertex_bit fold_or_bit eq_of_vertex_bits
  defect_bit defect_translate translate permute_vertex_bit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParallel

/-- The center and its neighbors in the selected directions. -/
def star (c a : BitVec 7) : Finset (BitVec 7) :=
  insert c ((Finset.univ.filter fun i : Fin 7 => a.getLsbD i.val).image
    fun i => c ^^^ BitVec.twoPow 7 i.val)

/-- The coordinate directions from a vertex to occupied neighbors. -/
def occupiedDirections (S : Finset (BitVec 7)) (x : BitVec 7) : Finset (Fin 7) :=
  Finset.univ.filter fun i => x ^^^ BitVec.twoPow 7 i.val ∈ S

/-- True exactly when an odd number of neighbors of the vertex are occupied. -/
def neighborParity (S : Finset (BitVec 7)) (x : BitVec 7) : Bool :=
  decide ((occupiedDirections S x).card % 2 = 1)

/-- Occupation at the vertex plus occupation at its neighbors, modulo two. -/
def defect (S : Finset (BitVec 7)) (x : BitVec 7) : Bool :=
  decide (x ∈ S) ^^ neighborParity S x

private theorem twoPow_eq_axisBit (i : Fin 7) : BitVec.twoPow 7 i.val = axisBit i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_twoPow, BitVec.toNat_ofNat]

private theorem mem_star {c a x : BitVec 7} :
    x ∈ star c a ↔ x = c ∨ ∃ i : Fin 7, a.getLsbD i.val = true ∧ x = c ^^^ axisBit i := by
  simp only [star, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, twoPow_eq_axisBit, eq_comm (a := _ ^^^ _) (b := x)]

private theorem center_mem_star (c a : BitVec 7) : c ∈ star c a :=
  mem_star.mpr (Or.inl rfl)

/-- Two occupied sets are disjoint and have no cube edge between them. -/
def Separated (A B : Finset (BitVec 7)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x ≠ y ∧ ∀ i : Fin 7, x ^^^ BitVec.twoPow 7 i.val ≠ y

private theorem Separated.disjoint {A B : Finset (BitVec 7)} (h : Separated A B) :
    Disjoint A B :=
  Finset.disjoint_left.mpr fun x hx hy => (h x hx x hy).1 rfl

private theorem Separated.centers_ne {c a d b : BitVec 7} (h : Separated (star c a) (star d b)) :
    c ≠ d :=
  (h c (center_mem_star c a) d (center_mem_star d b)).1

private theorem starMask_bit (c a x : BitVec 7) :
    (starMask c a).getLsbD x.toNat = true ↔ x ∈ star c a := by
  change (axisList.foldl (fun acc i =>
    if a &&& axisBit i = 0 then acc else acc ||| (1 : BitVec 128) <<< (c ^^^ axisBit i).toNat)
    ((1 : BitVec 128) <<< c.toNat)).getLsbD x.toNat = true ↔ _
  rw [fold_or_bit, mem_star]
  simp only [vertex_bit, List.mem_finRange, true_and, axis_unused, Bool.not_eq_false]

private theorem rootClosedNeighborhood_bit (x : BitVec 7) :
    rootClosedNeighborhood.getLsbD x.toNat = true ↔
      x ∈ star 0 7 ∨ ∃ i : Fin 7, x ∈ star (axisBit i) 7 := by
  change (axisList.foldl (fun acc i => if False then acc else acc ||| starMask (axisBit i) 7)
    (starMask 0 7)).getLsbD x.toNat = true ↔ _
  rw [fold_or_bit]
  simp only [List.mem_finRange, true_and, not_false_eq_true, starMask_bit]

private theorem mem_star_translate (c a x : BitVec 7) :
    (c ^^^ x) ∈ star c a ↔ x ∈ star 0#7 a := by
  have hc : c ^^^ x = c ↔ x = 0#7 := by
    simpa only [BitVec.xor_zero] using (BitVec.xor_right_inj (x := x) (y := 0#7) c)
  simp only [mem_star, hc, BitVec.xor_right_inj, BitVec.zero_xor]

private theorem separatedFromRoot_of_separated {c a : BitVec 7}
    (h : Separated (star 0 7) (star c a)) : separatedFromRoot c a = true := by
  apply decide_eq_true
  apply eq_of_vertex_bits
  intro x
  change (starMask c a &&& rootClosedNeighborhood).getLsbD x.toNat = (0#128).getLsbD x.toNat
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  apply Bool.eq_false_iff.mpr
  intro hx
  obtain ⟨hxS, hxN⟩ := Bool.and_eq_true_iff.mp hx
  have hxS := (starMask_bit c a x).mp hxS
  rcases (rootClosedNeighborhood_bit x).mp hxN with hxR | ⟨i, hi⟩
  · exact (h x hxR x hxS).1 rfl
  · let y := axisBit i ^^^ x
    have hx' : axisBit i ^^^ y = x := (translate (axisBit i)).left_inv x
    have hy : y ∈ star 0 7 := by
      apply (mem_star_translate (axisBit i) 7 y).mp
      simpa only [hx'] using hi
    exact (h y hy x hxS).2 i (by rw [twoPow_eq_axisBit, BitVec.xor_comm, hx'])

private theorem occupiedDirections_translate (c a x : BitVec 7) :
    occupiedDirections (star c a) (c ^^^ x) = occupiedDirections (star 0#7 a) x := by
  ext i
  simp only [occupiedDirections, Finset.mem_filter, Finset.mem_univ, true_and,
    BitVec.xor_assoc, mem_star_translate]

private theorem defect_translate_occupation (c a x : BitVec 7) :
    defect (star c a) (c ^^^ x) = defect (star 0#7 a) x := by
  simp only [defect, neighborParity, mem_star_translate, occupiedDirections_translate]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each block checks eight vertices against all 35 three-axis masks.
private theorem defect_origin_block (block : Fin 16) :
    (List.finRange 8).all (fun offset => axisChoices.all fun a =>
      let x := centerInBlock block offset
      decide (defect (star 0 a) x = (starDefect 0 a).getLsbD x.toNat)) = true := by
  fin_cases block <;> decide +kernel

/-- The parity defect of a three-axis star is the bit of the existing defect mask. -/
theorem defect_star (c a x : BitVec 7) (ha : a.cpop = 3) :
    defect (star c a) x = (starDefect c a).getLsbD x.toNat := by
  obtain ⟨y, rfl⟩ := (translate c).surjective x
  rw [← defect_translate c a, permute_vertex_bit]
  change defect (star c a) (c ^^^ y) = (starDefect 0 a).getLsbD y.toNat
  rw [defect_translate_occupation]
  obtain ⟨block, offset, rfl⟩ := exists_centerInBlock y
  have h := List.all_eq_true.mp (defect_origin_block block) offset (List.mem_finRange _)
  exact of_decide_eq_true (List.all_eq_true.mp h a (mem_axisChoices ha))

private theorem unused_translate_bit {c a x : BitVec 7} {i j : Fin 7}
    (hj : a.getLsbD j.val = false) (hx : x ∈ star (c ^^^ axisBit i) a) :
    x.getLsbD j.val = (c.getLsbD j.val ^^ decide (j = i)) := by
  rcases mem_star.mp hx with rfl | ⟨k, hk, rfl⟩
  · rw [BitVec.getLsbD_xor, axis_bit]
  · have hjk : j ≠ k := fun h => by simp_all
    simp only [BitVec.getLsbD_xor, axis_bit, hjk, decide_false, Bool.xor_false]

/-- The support of the defect mask is the union of the star's translates in unused
directions, and those translates are disjoint. -/
theorem starDefect_unused_translates (c a : BitVec 7) :
    (∀ x : BitVec 7, (starDefect c a).getLsbD x.toNat = true ↔
      ∃ i : Fin 7, a.getLsbD i.val = false ∧ x ∈ star (c ^^^ BitVec.twoPow 7 i.val) a) ∧
    ∀ i j : Fin 7, i ≠ j → a.getLsbD i.val = false → a.getLsbD j.val = false →
      Disjoint (star (c ^^^ BitVec.twoPow 7 i.val) a) (star (c ^^^ BitVec.twoPow 7 j.val) a) := by
  constructor
  · intro x
    simp only [defect_bit, twoPow_eq_axisBit, mem_star]
  · intro i j hij hi _
    simp only [twoPow_eq_axisBit]
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have h := (unused_translate_bit hi hxi).symm.trans (unused_translate_bit hi hxj)
    simp [hij] at h

private theorem occupiedDirections_union (A B : Finset (BitVec 7)) (x : BitVec 7) :
    occupiedDirections (A ∪ B) x = occupiedDirections A x ∪ occupiedDirections B x := by
  ext i
  simp [occupiedDirections]

private theorem neighborParity_union {A B : Finset (BitVec 7)} (h : Disjoint A B)
    (x : BitVec 7) :
    neighborParity (A ∪ B) x = (neighborParity A x ^^ neighborParity B x) := by
  have hd : Disjoint (occupiedDirections A x) (occupiedDirections B x) := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact Finset.disjoint_left.mp h (Finset.mem_filter.mp hiA).2 (Finset.mem_filter.mp hiB).2
  unfold neighborParity
  rw [occupiedDirections_union, Finset.card_union_of_disjoint hd]
  let m := (occupiedDirections A x).card
  let n := (occupiedDirections B x).card
  change decide ((m + n) % 2 = 1) = (decide (m % 2 = 1) ^^ decide (n % 2 = 1))
  by_cases hm : m % 2 = 1 <;> by_cases hn : n % 2 = 1 <;> simp [hm, hn] <;> omega

/-- Parity defects add by XOR on disjoint unions. -/
theorem defect_disjoint_union {A B : Finset (BitVec 7)} (h : Disjoint A B) (x : BitVec 7) :
    defect (A ∪ B) x = (defect A x ^^ defect B x) := by
  have hm : decide (x ∈ A ∪ B) = (decide (x ∈ A) ^^ decide (x ∈ B)) := by
    by_cases ha : x ∈ A
    · simp [ha, Finset.disjoint_left.mp h ha]
    · by_cases hb : x ∈ B <;> simp [ha, hb]
  simp only [defect, neighborParity_union h, hm, Bool.xor_assoc, Bool.xor_left_comm]

/-- A normalized occupation consisting of four separated three-axis stars. -/
structure FourStarDecomposition (S : Finset (BitVec 7))
    (c₁ c₂ c₃ a₁ a₂ a₃ : BitVec 7) : Prop where
  occupation : S = star 0 7 ∪ star c₁ a₁ ∪ star c₂ a₂ ∪ star c₃ a₃
  axes₁ : a₁.cpop = 3
  axes₂ : a₂.cpop = 3
  axes₃ : a₃.cpop = 3
  sep₀₁ : Separated (star 0 7) (star c₁ a₁)
  sep₀₂ : Separated (star 0 7) (star c₂ a₂)
  sep₀₃ : Separated (star 0 7) (star c₃ a₃)
  sep₁₂ : Separated (star c₁ a₁) (star c₂ a₂)
  sep₁₃ : Separated (star c₁ a₁) (star c₃ a₃)
  sep₂₃ : Separated (star c₂ a₂) (star c₃ a₃)

/-- Pointwise occupation parity on the four stars implies cancellation of their masks. -/
theorem defect_masks_cancel {S : Finset (BitVec 7)} {c₁ c₂ c₃ a₁ a₂ a₃ : BitVec 7}
    (h : FourStarDecomposition S c₁ c₂ c₃ a₁ a₂ a₃)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    starDefect 0 7 ^^^ starDefect c₁ a₁ ^^^ starDefect c₂ a₂ ^^^ starDefect c₃ a₃ = 0 := by
  apply eq_of_vertex_bits
  intro x
  have hx : defect S x = false := by simp [defect, hpar x]
  rw [h.occupation,
    defect_disjoint_union (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨h.sep₀₃.disjoint, h.sep₁₃.disjoint⟩, h.sep₂₃.disjoint⟩),
    defect_disjoint_union (Finset.disjoint_union_left.mpr ⟨h.sep₀₂.disjoint, h.sep₁₂.disjoint⟩),
    defect_disjoint_union h.sep₀₁.disjoint, defect_star 0 7 x (by decide),
    defect_star c₁ a₁ x h.axes₁, defect_star c₂ a₂ x h.axes₂, defect_star c₃ a₃ x h.axes₃] at hx
  change _ = (0#128).getLsbD x.toNat
  simpa only [BitVec.getLsbD_xor, BitVec.getLsbD_zero] using hx

/-- Pointwise occupation parity forces parallel stars and zero center bits on the root axes. -/
theorem four_star_parallel_of_occupancy
    {S : Finset (BitVec 7)} {c₁ c₂ c₃ a₁ a₂ a₃ : BitVec 7}
    (h : FourStarDecomposition S c₁ c₂ c₃ a₁ a₂ a₃)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    (a₁ = 7 ∧ c₁ &&& 7 = 0) ∧ (a₂ = 7 ∧ c₂ &&& 7 = 0) ∧ (a₃ = 7 ∧ c₃ &&& 7 = 0) :=
  four_star_parallel h.axes₁ h.axes₂ h.axes₃
    (separatedFromRoot_of_separated h.sep₀₁) (separatedFromRoot_of_separated h.sep₀₂)
    (separatedFromRoot_of_separated h.sep₀₃)
    h.sep₀₁.centers_ne.symm h.sep₀₂.centers_ne.symm h.sep₀₃.centers_ne.symm
    h.sep₁₂.centers_ne h.sep₁₃.centers_ne h.sep₂₃.centers_ne (defect_masks_cancel h hpar)

/-- The three-cube star in coordinates 0, 1 and 2. -/
def leadingStar : Finset (BitVec 3) := {0, 1, 2, 4}

private theorem center_append (c : BitVec 7) (hc : c &&& 7 = 0) :
    c.extractLsb' 3 4 ++ (0 : BitVec 3) = c := by
  have check : ∀ i : Fin 128,
      let v : BitVec 7 := BitVec.ofFin i
      v &&& 7 = 0 → v.extractLsb' 3 4 ++ (0 : BitVec 3) = v := by decide +kernel
  exact check c.toFin hc

private theorem translated_star_eq (p : BitVec 4) :
    star (p ++ 0#3) 7 = leadingStar.image (fun low => p ++ low) := by
  have hroot : star 0#7 7 = leadingStar.image (fun low => 0#4 ++ low) := by
    decide +kernel
  ext x
  obtain ⟨y, rfl⟩ := (translate (p ++ 0#3)).surjective x
  change ((p ++ 0#3) ^^^ y) ∈ star (p ++ 0#3) 7 ↔ _
  rw [mem_star_translate, hroot]
  simp only [Finset.mem_image]
  apply exists_congr
  intro low
  rw [← show (p ++ 0#3) ^^^ (0#4 ++ low) = p ++ low by
    simp only [BitVec.xor_append, BitVec.xor_zero, BitVec.zero_xor]]
  exact and_congr_right fun _ => (BitVec.xor_right_inj _).symm

private theorem product_image_singleton (p : BitVec 4) :
    (leadingStar ×ˢ {p}).image (fun v => v.2 ++ v.1) =
      leadingStar.image (fun low => p ++ low) := by
  ext x
  simp

private theorem separated_upper_centers {p q : BitVec 4}
    (h : Separated (star (p ++ 0#3) 7) (star (q ++ 0#3) 7)) :
    p ≠ q ∧ ∀ i : Fin 4, p ^^^ BitVec.twoPow 4 i.val ≠ q := by
  refine ⟨fun he => h.centers_ne (congrArg (fun u : BitVec 4 => u ++ (0 : BitVec 3)) he), ?_⟩
  intro i hi
  have hflip (j : Fin 4) :
      BitVec.twoPow 7 (j.natAdd 3).val = BitVec.twoPow 4 j.val ++ 0#3 := by
    fin_cases j <;> decide +kernel
  exact (h _ (center_mem_star _ _) _ (center_mem_star _ _)).2 (i.natAdd 3)
    (by rw [hflip, BitVec.xor_append, hi, BitVec.xor_zero])

/-- The occupation is the product of the leading three-cube star and four
independent center coordinates in the complementary four-cube. -/
theorem four_star_occupancy_product
    {S : Finset (BitVec 7)} {c₁ c₂ c₃ a₁ a₂ a₃ : BitVec 7}
    (h : FourStarDecomposition S c₁ c₂ c₃ a₁ a₂ a₃)
    (hpar : ∀ x, decide (x ∈ S) = neighborParity S x) :
    ∃ T : Finset (BitVec 4), T.card = 4 ∧ 0 ∈ T ∧
      (T : Set (BitVec 4)).Pairwise (fun p q => ∀ i : Fin 4, p ^^^ BitVec.twoPow 4 i.val ≠ q) ∧
      S = (leadingStar ×ˢ T).image (fun v => v.2 ++ v.1) := by
  obtain ⟨⟨rfl, hc₁⟩, ⟨rfl, hc₂⟩, ⟨rfl, hc₃⟩⟩ := four_star_parallel_of_occupancy h hpar
  let p₁ := c₁.extractLsb' 3 4
  let p₂ := c₂.extractLsb' 3 4
  let p₃ := c₃.extractLsb' 3 4
  have h₁ : p₁ ++ 0#3 = c₁ := center_append c₁ hc₁
  have h₂ : p₂ ++ 0#3 = c₂ := center_append c₂ hc₂
  have h₃ : p₃ ++ 0#3 = c₃ := center_append c₃ hc₃
  let L : List (BitVec 4) := [0, p₁, p₂, p₃]
  let T := L.toFinset
  let R (p q : BitVec 4) := ∀ i : Fin 4, p ^^^ BitVec.twoPow 4 i.val ≠ q
  have h0 : (0 : BitVec 4) ++ 0#3 = (0 : BitVec 7) := rfl
  have h01 := separated_upper_centers (p := 0) (q := p₁) (by simpa only [h0, h₁] using h.sep₀₁)
  have h02 := separated_upper_centers (p := 0) (q := p₂) (by simpa only [h0, h₂] using h.sep₀₂)
  have h03 := separated_upper_centers (p := 0) (q := p₃) (by simpa only [h0, h₃] using h.sep₀₃)
  have h12 := separated_upper_centers (p := p₁) (q := p₂) (by simpa only [h₁, h₂] using h.sep₁₂)
  have h13 := separated_upper_centers (p := p₁) (q := p₃) (by simpa only [h₁, h₃] using h.sep₁₃)
  have h23 := separated_upper_centers (p := p₂) (q := p₃) (by simpa only [h₂, h₃] using h.sep₂₃)
  have hL : L.Pairwise (fun p q => p ≠ q ∧ R p q) := by
    change List.Pairwise _ [0, p₁, p₂, p₃]
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies]
    exact ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, fun _ => trivial⟩
  have hnodup : L.Nodup := hL.imp (fun hr => hr.1)
  refine ⟨T, List.toFinset_card_of_nodup hnodup, by simp [T, L], ?_, ?_⟩
  · let : Std.Symm R := ⟨fun _ _ hr i he =>
      hr i (by simpa [BitVec.xor_assoc] using congrArg (· ^^^ BitVec.twoPow 4 i.val) he.symm)⟩
    have hind : L.Pairwise R := hL.imp (fun hr => hr.2)
    intro p hp q hq hpq
    exact hind.forall (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq) hpq
  · have hT : T = {0} ∪ {p₁} ∪ {p₂} ∪ {p₃} := by
      ext p
      simp only [T, L, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
        Finset.mem_union, Finset.mem_singleton, or_assoc]
    rw [h.occupation, ← h₁, ← h₂, ← h₃, hT]
    change star ((0 : BitVec 4) ++ 0#3) 7 ∪ _ ∪ _ ∪ _ = _
    simp only [translated_star_eq, Finset.product_union, Finset.image_union,
      product_image_singleton]

#print axioms defect_star
#print axioms starDefect_unused_translates
#print axioms defect_disjoint_union
#print axioms defect_masks_cancel
#print axioms four_star_parallel_of_occupancy
#print axioms four_star_occupancy_product

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarOccupancy
