/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSecondSharedLeaves
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSecondSharedLeaves
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A coordinate half has at most 27 vertices for the second ten-pattern projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSharedLeaves

/-! The exact ten-pattern case of Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2.
The first coordinate is the least significant bit of the projection code. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSecondSharedLeaves

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges)
open BalancedCubeComponentBoundary (regular_directions)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9ThetaProjection (leftCode)
open Q9SignedProjection (join fiber signedRow leftParitySign q9_signed_row_split
  q9_signed_row_eq_zero_outside_projection)
open Q5SmallParitySupport (neighborParity eight_le_card_of_neighborParity)
open Q7FourStarParallel (permuteBits)
open private normalized_leaves normalized_true_half suffixHalf from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSharedLeaves
open Q5SharedSixLeaves (degree leaves normalize_eight_carrier)
open private pattern rightBlock leftCode_join join_blocks flipCode signed_row_four occupation
  degree_split from D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private column fiber_occupied signedRow_pairing_symmetric fiber_admissible admissible
  unitOrZero ternary exists_ternary from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
open private carrier mem_carrier card_carrier mem_encoded flip_cubeBitVec encoded_neighborParity
  carrier_false_endpoints twelve_direction_edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection
open private degree_eq_card_flips sum_degrees sum_degrees_sides side from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves

/-- The normalized four-coordinate projection. -/
def tenShadowSecond : Finset (BitVec 4) := {0, 1, 2, 3, 4, 7, 8, 12, 13, 15}

private def fiberLabels (a b c d : ℤ) (k : BitVec 4) : ℤ :=
  match k.toNat with
  | 0 => a
  | 1 => b - c
  | 2 => b
  | 3 => -d
  | 4 => b - c
  | 7 => c
  | 8 => b
  | 12 => -d
  | 13 => c
  | 15 => d
  | _ => 0

private theorem column_apply (z : Q 9 → ℤ) (k : BitVec 4) (y : Q 5) :
    column z k y = fiber z y (pattern k) := rfl

private theorem reconstruction {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hproj : S.image leftCode = tenShadowSecond)
    (hzero : ∀ u ∉ S, z u = 0) (hrow : ∀ u, signedRow z u = 3 * z u)
    (y : Q 5) (k : BitVec 4) :
    column z k y = fiberLabels (column z 0 y) (column z 2 y)
      (column z 7 y) (column z 15 y) k := by
  have zero (l : BitVec 4) (hl : l ∉ tenShadowSecond) (v : Q 5) :
      column z l v = 0 := by
    apply hzero
    intro hv
    exact hl (by simpa only [leftCode_join, hproj] using mem_image_of_mem leftCode hv)
  have outside (l : BitVec 4) (hl : l ∉ tenShadowSecond) :
      signedRow (fiber z y) (pattern l) = 0 :=
    q9_signed_row_eq_zero_outside_projection hrow (zero l hl) y
  have e5 := signed_row_four (fiber z y) 5 4 7 1 13 1 (-1) (-1) 1 (by decide) (by decide)
  have e6 := signed_row_four (fiber z y) 6 7 4 2 14 1 1 (-1) 1 (by decide) (by decide)
  have e9 := signed_row_four (fiber z y) 9 8 11 13 1 1 (-1) (-1) (-1) (by decide) (by decide)
  have e10 := signed_row_four (fiber z y) 10 11 8 14 2 1 1 (-1) (-1) (by decide) (by decide)
  have e11 := signed_row_four (fiber z y) 11 10 9 15 3 1 (-1) 1 1 (by decide) (by decide)
  have e14 := signed_row_four (fiber z y) 14 15 12 10 6 1 1 (-1) 1 (by decide) (by decide)
  have n5 : (5 : BitVec 4) ∉ tenShadowSecond := by decide
  have n6 : (6 : BitVec 4) ∉ tenShadowSecond := by decide
  have n9 : (9 : BitVec 4) ∉ tenShadowSecond := by decide
  have n10 : (10 : BitVec 4) ∉ tenShadowSecond := by decide
  have n11 : (11 : BitVec 4) ∉ tenShadowSecond := by decide
  have n14 : (14 : BitVec 4) ∉ tenShadowSecond := by decide
  simp only [outside 5 n5, outside 6 n6, outside 9 n9, outside 10 n10,
    outside 11 n11, outside 14 n14, ← column_apply, zero 6 n6, zero 9 n9,
    zero 10 n10, zero 11 n11, zero 14 n14, one_mul, neg_one_mul, neg_zero, zero_add]
    at e5 e6 e9 e10 e11 e14
  obtain ⟨k⟩ := k
  fin_cases k <;> try (first | rfl | exact zero _ (by decide) _)
  case «1» => change column z 1 y = column z 2 y - column z 7 y; omega
  case «3» => change column z 3 y = -column z 15 y; omega
  case «4» => change column z 4 y = column z 2 y - column z 7 y; omega
  case «8» => change column z 8 y = column z 2 y; omega
  case «12» => change column z 12 y = -column z 15 y; omega
  case «13» => change column z 13 y = column z 7 y; omega

private theorem suffix_equations {z : Q 9 → ℤ}
    (hform : ∀ y k, column z k y = fiberLabels (column z 0 y) (column z 2 y)
      (column z 7 y) (column z 15 y) k)
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5) :
    let a := column z 0 y
    let b := column z 2 y
    let c := column z 7 y
    let d := column z 15 y
    signedRow (column z 0) y = 3 * a - 4 * b + 2 * c ∧
    signedRow (column z 2) y = a - 3 * b - d ∧
    signedRow (column z 7) y = -3 * c - 2 * d ∧
    signedRow (column z 15) y = 2 * c + 3 * d := by
  have split (k : BitVec 4) :
      3 * column z k y = signedRow (fiber z y) (pattern k) +
        leftParitySign (pattern k) * signedRow (column z k) y :=
    q9_signed_row_split hrow (pattern k) y
  have r0 := split 0
  have r2 := split 2
  have r7 := split 7
  have r15 := split 15
  rw [signed_row_four _ 0 1 2 4 8 1 1 1 1 (by decide) (by decide)] at r0
  rw [signed_row_four _ 2 3 0 6 10 1 1 (-1) (-1) (by decide) (by decide)] at r2
  rw [signed_row_four _ 7 6 5 3 15 1 (-1) 1 (-1) (by decide) (by decide)] at r7
  rw [signed_row_four _ 15 14 13 11 7 1 (-1) 1 (-1) (by decide) (by decide)] at r15
  simp only [← column_apply, hform y 1, hform y 3, hform y 4, hform y 5,
    hform y 6, hform y 8, hform y 10, hform y 11, hform y 13, hform y 14] at r0 r2 r7 r15
  change 3 * column z 0 y = 1 * (column z 2 y - column z 7 y) +
    (1 * column z 2 y + (1 * (column z 2 y - column z 7 y) + 1 * column z 2 y)) +
    1 * signedRow (column z 0) y at r0
  change 3 * column z 2 y = 1 * (-column z 15 y) + (1 * column z 0 y +
    ((-1) * 0 + (-1) * 0)) + (-1) * signedRow (column z 2) y at r2
  change 3 * column z 7 y = 1 * 0 + ((-1) * 0 + (1 * (-column z 15 y) +
    (-1) * column z 15 y)) + (-1) * signedRow (column z 7) y at r7
  change 3 * column z 15 y = 1 * 0 + ((-1) * column z 7 y + (1 * 0 +
    (-1) * column z 7 y)) + 1 * signedRow (column z 15) y at r15
  exact ⟨by omega, by omega, by omega, by omega⟩

private def indicator (x : ℤ) : ℕ := if x ≠ 0 then 1 else 0

private def horizontalDegree (f : BitVec 4 → ℤ) (k : BitVec 4) : ℕ :=
  ∑ i : Fin 4, indicator (f (flipCode k i))

private def horizontalEdge (f : BitVec 4 → ℤ) (k : BitVec 4) (i : Fin 4) : ℕ :=
  if pattern k i = false then indicator (f k) * indicator (f (flipCode k i)) else 0

private def fiberCounts (a b c d : ℤ) : Prop :=
  let f := fiberLabels a b c d
  let n := if c = 0 then indicator b else 0
  (∑ k ∈ tenShadowSecond, indicator (f k)) =
    indicator a + 3 * indicator d + 4 * indicator c + 4 * n ∧
  (∑ k ∈ tenShadowSecond, ∑ i : Fin 4, horizontalEdge f k i) =
    2 * (indicator a * indicator c) + 6 * (indicator d * indicator c) ∧
  (a ≠ 0 → horizontalDegree f 0 = 2 * indicator c) ∧
  (d ≠ 0 → horizontalDegree f 15 = 2 * indicator c) ∧
  (c ≠ 0 → horizontalDegree f 7 = 2 * indicator d) ∧
  c * d = -((indicator d * indicator c : ℕ) : ℤ) ∧
  c * c = (indicator c : ℤ) ∧ d * d = (indicator d : ℤ)
  deriving Decidable

private theorem fiberCounts_table : ∀ a b c d : Fin 3,
    admissible (fiberLabels (ternary a) (ternary b) (ternary c) (ternary d)) →
    fiberCounts (ternary a) (ternary b) (ternary c) (ternary d) := by
  decide

private theorem fiberCounts_of_admissible {a b c d : ℤ}
    (h : admissible (fiberLabels a b c d)) : fiberCounts a b c d := by
  obtain ⟨i, rfl⟩ := exists_ternary (show unitOrZero a from h.1 0)
  obtain ⟨j, rfl⟩ := exists_ternary (show unitOrZero b from h.1 2)
  obtain ⟨k, rfl⟩ := exists_ternary (show unitOrZero c from h.1 7)
  obtain ⟨l, rfl⟩ := exists_ternary (show unitOrZero d from h.1 15)
  exact fiberCounts_table i j k l h

private theorem card_by_prefix {S T : Finset (Q 9)} (hsub : T ⊆ S)
    (hproj : S.image leftCode = tenShadowSecond) :
    T.card = ∑ k ∈ tenShadowSecond, (carrier T k).card := by
  simpa only [card_carrier] using
    (card_eq_sum_card_fiberwise (f := leftCode) (s := T) (t := tenShadowSecond)
      (fun u hu => hproj ▸ mem_image_of_mem leftCode (hsub hu)))

private theorem occupation_eq_indicator {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (k : BitVec 4) (y : Q 5) :
    occupation S k y = indicator (column z k y) := by
  classical
  unfold occupation indicator
  exact if_congr (fiber_occupied hunit hzero k y) rfl rfl

private theorem card_carrier_restrict (S : Finset (Q 9)) (U : Finset (Q 5)) (k : BitVec 4) :
    (carrier (S.filter fun u => rightBlock u ∈ U) k).card = ∑ y ∈ U, occupation S k y := by
  classical
  have he : carrier (S.filter fun u => rightBlock u ∈ U) k =
      U.filter fun y => join (pattern k) y ∈ S := by
    ext y
    have hy : rightBlock (join (pattern k) y) = y := by
      funext i
      simp only [rightBlock, join, Fin.append_right]
    rw [mem_carrier, mem_filter, mem_filter, hy, and_comm]
  rw [he, card_filter]
  rfl

private theorem card_from_occupations (T U : Finset (Q 5)) :
    (∑ y ∈ U, if y ∈ T then 1 else 0) = (T ∩ U).card := by
  classical
  rw [← card_filter]
  congr 1
  ext y
  simp [and_comm]

private theorem restricted_vertex_count {S : Finset (Q 9)}
    {A B C N : Finset (Q 5)} (U : Finset (Q 5))
    (hproj : S.image leftCode = tenShadowSecond)
    (hcount : ∀ y, (∑ k ∈ tenShadowSecond, occupation S k y) =
      (if y ∈ A then 1 else 0) + 3 * (if y ∈ B then 1 else 0) +
        4 * (if y ∈ C then 1 else 0) + 4 * (if y ∈ N then 1 else 0)) :
    (S.filter fun u => rightBlock u ∈ U).card =
      (A ∩ U).card + 3 * (B ∩ U).card + 4 * (C ∩ U).card + 4 * (N ∩ U).card := by
  rw [card_by_prefix (filter_subset _ _) hproj]
  simp only [card_carrier_restrict]
  rw [sum_comm]
  simp_rw [hcount, sum_add_distrib, ← mul_sum, card_from_occupations]

private theorem card_carrier_edges (S : Finset (Q 9)) (k : BitVec 4) (i : Fin 4) :
    (carrier (S.filter fun u => u (i.castAdd 5) = false ∧ flip u (i.castAdd 5) ∈ S) k).card =
      ∑ y : Q 5, if pattern k i = false then
        occupation S k y * occupation S (flipCode k i) y else 0 := by
  classical
  rw [carrier_false_endpoints]
  cases pattern k i
  · have he : carrier S k ∩ carrier S (flipCode k i) =
        univ.filter (fun y => join (pattern k) y ∈ S ∧
          join (pattern (flipCode k i)) y ∈ S) := by
      ext y
      simp only [mem_inter, mem_carrier, mem_filter, mem_univ, true_and]
    simp only [Bool.cond_false, ite_true, he, card_filter]
    apply sum_congr rfl
    intro y _
    by_cases h₁ : join (pattern k) y ∈ S <;>
      by_cases h₂ : join (pattern (flipCode k i)) y ∈ S <;> simp [occupation, h₁, h₂]
  · simp

private theorem horizontal_edge_count {S : Finset (Q 9)} {X Y : Finset (Q 5)}
    (hproj : S.image leftCode = tenShadowSecond)
    (hcount : ∀ y, (∑ k ∈ tenShadowSecond, ∑ i : Fin 4, if pattern k i = false then
      occupation S k y * occupation S (flipCode k i) y else 0) =
      2 * (if y ∈ X then 1 else 0) + 6 * (if y ∈ Y then 1 else 0)) :
    (∑ i : Fin 4, directionEdges S (i.castAdd 5)) = 2 * X.card + 6 * Y.card := by
  classical
  have hdir (i : Fin 4) : directionEdges S (i.castAdd 5) =
      ∑ k ∈ tenShadowSecond, ∑ y : Q 5, if pattern k i = false then
        occupation S k y * occupation S (flipCode k i) y else 0 := by
    unfold directionEdges
    rw [card_by_prefix (filter_subset _ _) hproj]
    exact sum_congr rfl fun k _ => card_carrier_edges S k i
  simp only [hdir]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (Fin 4))) (t := (univ : Finset (Q 5)))]
  rw [sum_comm]
  simp_rw [hcount, sum_add_distrib, ← mul_sum, card_from_occupations, inter_univ]

private noncomputable def encode (A : Finset (Q 5)) : Finset (BitVec 5) :=
  A.image (cubeBitVec 5).symm

private theorem encode_card (A : Finset (Q 5)) : (encode A).card = A.card :=
  card_image_of_injective _ (cubeBitVec 5).symm.injective

private theorem parity_of_column {S : Finset (Q 9)} {z : Q 9 → ℤ} {k : BitVec 4}
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (g : Q 5 → ℤ)
    (hrow : ∀ y, signedRow (column z k) y = 3 * column z k y - 2 * g y) :
    ∀ x, decide (x ∈ encode (carrier S k)) = neighborParity (encode (carrier S k)) x :=
  encoded_neighborParity (a := column z k) (b := g) (c := fun _ => 0)
    (fun y hy => hunit _ ((mem_carrier S k y).mp hy))
    (fun y hy => hzero _ (fun hp => hy ((mem_carrier S k y).mpr hp)))
    (by simpa only [mul_zero, sub_zero] using hrow)

private theorem encoded_nonempty {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSecond)
    {k : BitVec 4} (hk : k ∈ tenShadowSecond) : (encode (carrier S k)).Nonempty := by
  obtain ⟨u, hu, hku⟩ := mem_image.mp (hproj.symm ▸ hk)
  refine ⟨(cubeBitVec 5).symm (rightBlock u), mem_image_of_mem _
    ((mem_carrier S k _).mpr ?_)⟩
  rwa [← hku, join_blocks]

private theorem encode_subset {U V : Finset (Q 5)} (h : U ⊆ V) : encode U ⊆ encode V :=
  image_mono _ h

open Classical in
private theorem encoded_degree_profile {S : Finset (Q 9)} {k : BitVec 4} {L : Finset (Q 5)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hh : ∀ y ∈ carrier S k, (∑ i : Fin 4, occupation S (flipCode k i) y) =
      2 * (if y ∈ L then 1 else 0)) :
    ∀ x ∈ encode (carrier S k), degree (encode (carrier S k)) x =
      if x ∈ encode L then 1 else 3 := by
  classical
  intro x hx
  let y := cubeBitVec 5 x
  have hy : y ∈ carrier S k := (mem_encoded _ _).mp hx
  have h := (degree_split S k y).symm.trans (regular_directions S hr ((mem_carrier S k y).mp hy))
  have he : degree (encode (carrier S k)) x = ∑ j : Fin 5, occupation S k (flip y j) := by
    rw [degree_eq_card_flips, card_filter]
    apply sum_congr rfl
    intro i _
    simp only [encode, mem_encoded, occupation, ← flip_cubeBitVec, y, mem_carrier]
  rw [← he, hh _ hy] at h
  simp only [encode, mem_encoded]
  change degree (encode (carrier S k)) x = if y ∈ L then 1 else 3
  by_cases hm : y ∈ L
  · rw [ite_eq_left hm] at h ⊢
    omega
  · rw [ite_eq_right hm] at h ⊢
    omega

private theorem size_constraints {U L : Finset (BitVec 5)}
    (hne : U.Nonempty)
    (hpar : ∀ x, decide (x ∈ U) = neighborParity U x)
    (hdeg : ∀ x ∈ U, degree U x = if x ∈ L then 1 else 3) :
    8 ≤ U.card ∧ U.card % 2 = 0 := by
  constructor
  · apply eight_le_card_of_neighborParity hne hpar
    intro x hx
    rw [← degree_eq_card_flips, hdeg x hx]
    split <;> omega
  · have htotal := sum_degrees hdeg (Subset.refl U)
    have hsplit : (∑ x ∈ U, degree U x) =
        (∑ x ∈ side U false, degree U x) + ∑ x ∈ side U true, degree U x := by
      rw [← sum_filter_add_sum_filter_not U (fun x => Q5SmallParitySupport.bitParity x = false)
        (degree U)]
      congr 2
      ext x
      cases Q5SmallParitySupport.bitParity x <;> simp
    have hbalance := sum_degrees_sides U
    omega

private theorem common_leaves_count {c d : Q 5 → ℤ} {B C Y : Finset (Q 5)}
    (hc : ∀ y, signedRow c y = -3 * c y - 2 * d y)
    (hd : ∀ y, signedRow d y = 2 * c y + 3 * d y)
    (hcd : ∀ y, c y * d y = -(if y ∈ Y then 1 else 0))
    (hcc : ∀ y, c y * c y = if y ∈ C then 1 else 0)
    (hdd : ∀ y, d y * d y = if y ∈ B then 1 else 0) :
    3 * Y.card = B.card + C.card := by
  classical
  have hleft (y : Q 5) : signedRow c y * d y =
      3 * (if y ∈ Y then 1 else 0) - 2 * (if y ∈ B then 1 else 0) := by
    rw [hc, sub_mul, mul_assoc, mul_assoc, hcd, hdd]
    ring
  have hright (y : Q 5) : c y * signedRow d y =
      2 * (if y ∈ C then 1 else 0) - 3 * (if y ∈ Y then 1 else 0) := by
    rw [hd, mul_add, mul_left_comm _ 2, mul_left_comm _ 3, hcc, hcd]
    ring
  have hsum := signedRow_pairing_symmetric c d
  simp only [hleft, hright, sum_sub_distrib, ← mul_sum] at hsum
  have hcard (T : Finset (Q 5)) : (∑ y : Q 5, if y ∈ T then (1 : ℤ) else 0) = T.card := by
    simp
  rw [hcard Y, hcard B, hcard C] at hsum
  omega

private theorem occupation_eq_carrier (S : Finset (Q 9)) (k : BitVec 4) (y : Q 5) :
    occupation S k y = if y ∈ carrier S k then 1 else 0 := by
  classical
  simp only [occupation, mem_carrier]

private theorem indicator_diff (T U : Finset (Q 5)) (y : Q 5) :
    (if y ∈ U then 0 else if y ∈ T then 1 else 0 : ℕ) =
      if y ∈ T \ U then 1 else 0 := by
  by_cases ht : y ∈ T <;> by_cases hu : y ∈ U <;> simp [ht, hu]

private theorem indicator_inter (T U : Finset (Q 5)) (y : Q 5) :
    (if y ∈ T then 1 else 0 : ℕ) * (if y ∈ U then 1 else 0) =
      if y ∈ T ∩ U then 1 else 0 := by
  by_cases ht : y ∈ T <;> by_cases hu : y ∈ U <;> simp [ht, hu]

private theorem suffixHalf_encode (U : Finset (Q 5)) (i : Fin 5) (b : Bool) :
    suffixHalf (encode U) i b =
      (U ∩ univ.filter (fun y => y i = b)).card := by
  classical
  have he : (encode U).filter (fun x => x.getLsbD i.val = b) =
      encode (U ∩ univ.filter (fun y => y i = b)) := by
    ext x
    simp only [encode, mem_filter, mem_encoded, mem_inter, mem_univ, true_and]
    rfl
  rw [suffixHalf, he, encode_card]

-- The coupled suffix rows give an additional count through self-adjointness.
open Classical in
private theorem carrier_equations {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72) (hproj : S.image leftCode = tenShadowSecond) :
    let A := carrier S 0
    let B := carrier S 15
    let C := carrier S 7
    let N := carrier S 2 \ C
    let X := A ∩ C
    let Y := B ∩ C
    (∀ U : Finset (Q 5), (S.filter fun u => rightBlock u ∈ U).card =
      (A ∩ U).card + 3 * (B ∩ U).card + 4 * (C ∩ U).card + 4 * (N ∩ U).card) ∧
    X.card = 6 ∧ Y.card = 6 ∧
    ((B.card = 8 ∧ C.card = 10) ∨ (B.card = 10 ∧ C.card = 8)) ∧
    (∀ x, decide (x ∈ encode B) = neighborParity (encode B) x) ∧
    (∀ x, decide (x ∈ encode C) = neighborParity (encode C) x) ∧
    (∀ x ∈ encode B, degree (encode B) x = if x ∈ encode Y then 1 else 3) ∧
    (∀ x ∈ encode C, degree (encode C) x = if x ∈ encode Y then 1 else 3) := by
  classical
  dsimp only
  let A := carrier S 0
  let B := carrier S 15
  let C := carrier S 7
  let N := carrier S 2 \ C
  let X := A ∩ C
  let Y := B ∩ C
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hr hb
  have hform := reconstruction hproj hzero hrow
  have hsuf := suffix_equations hform hrow
  have hf (y : Q 5) := fiberCounts_of_admissible
    (show admissible (fiberLabels (column z 0 y) (column z 2 y)
      (column z 7 y) (column z 15 y)) by
      rw [← funext (hform y)]
      exact fiber_admissible hr hunit hzero hsign y)
  have occ (k : BitVec 4) (y : Q 5) :
      indicator (column z k y) = if y ∈ carrier S k then 1 else 0 :=
    (occupation_eq_indicator hunit hzero k y).symm.trans (occupation_eq_carrier S k y)
  have hcz (y : Q 5) : column z 7 y = 0 ↔ y ∉ C :=
    by simpa only [not_not] using
      ((mem_carrier S 7 y).trans (fiber_occupied hunit hzero 7 y)).not.symm
  have hv (U : Finset (Q 5)) := restricted_vertex_count (A := A) (B := B) (C := C) (N := N)
    U hproj (fun y => by
      have h := (hf y).1
      simp only [← hform y, ← occupation_eq_indicator hunit hzero] at h
      simpa only [occupation_eq_carrier S 0, occupation_eq_carrier S 2,
        occupation_eq_carrier S 7, occupation_eq_carrier S 15, hcz, ite_not,
        indicator_diff] using h)
  have hvc := hv (univ : Finset (Q 5))
  simp [hsize] at hvc
  have hedges := horizontal_edge_count (X := X) (Y := Y) hproj (fun y => by
    have h := (hf y).2.1
    simp only [horizontalEdge, ← hform y, ← occupation_eq_indicator hunit hzero] at h
    simpa only [occupation_eq_carrier S 0, occupation_eq_carrier S 7,
      occupation_eq_carrier S 15, indicator_inter] using h)
  have h48 : 48 = 2 * X.card + 6 * Y.card := by
    simpa only [twelve_direction_edges hr hb hsize, sum_const, card_univ,
      Fintype.card_fin, smul_eq_mul] using hedges
  have hdA := encoded_degree_profile (k := 0) (L := X) hr (fun y hy => by
    have h := (hf y).2.2.1 ((fiber_occupied hunit hzero 0 y).mp ((mem_carrier S 0 y).mp hy))
    simpa only [horizontalDegree, ← hform y, ← occupation_eq_indicator hunit hzero,
      occupation_eq_carrier S 7, X, A, mem_inter, hy, true_and] using h)
  have hdB := encoded_degree_profile (k := 15) (L := Y) hr (fun y hy => by
    have h := (hf y).2.2.2.1 ((fiber_occupied hunit hzero 15 y).mp ((mem_carrier S 15 y).mp hy))
    simpa only [horizontalDegree, ← hform y, ← occupation_eq_indicator hunit hzero,
      occupation_eq_carrier S 7, Y, B, mem_inter, hy, true_and] using h)
  have hdC := encoded_degree_profile (k := 7) (L := Y) hr (fun y hy => by
    have h := (hf y).2.2.2.2.1 ((fiber_occupied hunit hzero 7 y).mp ((mem_carrier S 7 y).mp hy))
    simpa only [horizontalDegree, ← hform y, ← occupation_eq_indicator hunit hzero,
      occupation_eq_carrier S 15, Y, C, mem_inter, hy, and_true] using h)
  have hpA := parity_of_column (k := 0) hunit hzero (fun y => 2 * column z 2 y - column z 7 y)
    (fun y => by have h := (hsuf y).1; omega)
  have hpB := parity_of_column (k := 15) hunit hzero (fun y => -column z 7 y)
    (fun y => by have h := (hsuf y).2.2.2; omega)
  have hpC := parity_of_column (k := 7) hunit hzero (fun y => 3 * column z 7 y + column z 15 y)
    (fun y => by have h := (hsuf y).2.2.1; omega)
  have hA := size_constraints (encoded_nonempty hproj (k := 0) (by decide)) hpA hdA
  have hB := size_constraints (encoded_nonempty hproj (k := 15) (by decide)) hpB hdB
  have hC := size_constraints (encoded_nonempty hproj (k := 7) (by decide)) hpC hdC
  simp only [encode_card] at hA hB hC
  have hY : 3 * Y.card = B.card + C.card := common_leaves_count
    (fun y => (hsuf y).2.2.1) (fun y => (hsuf y).2.2.2)
    (fun y => by
      have h := (hf y).2.2.2.2.2.1
      simpa only [occ, indicator_inter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h)
    (fun y => by
      have h := (hf y).2.2.2.2.2.2.1
      simpa only [occ, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h)
    (fun y => by
      have h := (hf y).2.2.2.2.2.2.2
      simpa only [occ, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h)
  change 72 = A.card + 3 * B.card + 4 * C.card + 4 * N.card at hvc
  change 8 ≤ A.card ∧ A.card % 2 = 0 at hA
  change 8 ≤ B.card ∧ B.card % 2 = 0 at hB
  change 8 ≤ C.card ∧ C.card % 2 = 0 at hC
  have hBC : (B.card = 8 ∧ C.card = 10) ∨ (B.card = 10 ∧ C.card = 8) := by omega
  have hY6 : Y.card = 6 := by omega
  have hX6 : X.card = 6 := by omega
  exact ⟨hv, hX6, hY6, hBC, hpB, hpC, hdB, hdC⟩

open Classical in
/-- For the exact projection `{0,1,2,3,4,7,8,12,13,15}`, a Huang-balanced induced cubic
support of order 72 has an ambient coordinate half of size at most 27. -/
theorem tenShadowSecond_half_le_twentySeven {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72) (hproj : S.image leftCode = tenShadowSecond) :
    ∃ (i : Fin 9) (b : Bool), (S.filter fun u => u i = b).card ≤ 27 := by
  classical
  let A := carrier S 0
  let B := carrier S 15
  let C := carrier S 7
  let N := carrier S 2 \ C
  let Y := B ∩ C
  obtain ⟨hv, _, hY, hsizeBC, hpB, hpC, hdB, hdC⟩ := carrier_equations hr hb hsize hproj
  change Y.card = 6 at hY
  change (B.card = 8 ∧ C.card = 10) ∨ (B.card = 10 ∧ C.card = 8) at hsizeBC
  have hYB : encode Y ⊆ encode B := encode_subset inter_subset_left
  have hYC : encode Y ⊆ encode C := encode_subset inter_subset_right
  have hY6 : (encode Y).card = 6 := (encode_card Y).trans hY
  have norm : ∃ a : BitVec 5, ∃ p : Equiv.Perm (Fin 5),
      (encode Y).image (fun x => x ^^^ a) = leaves.image (permuteBits p) := by
    rcases hsizeBC with ⟨hB, _⟩ | ⟨_, hC⟩
    · obtain ⟨a, _, p, _, _, hn⟩ :=
        normalize_eight_carrier ((encode_card B).trans hB) hY6 hYB hdB hpB
      exact ⟨a, p, hn⟩
    · obtain ⟨a, _, p, _, _, hn⟩ :=
        normalize_eight_carrier ((encode_card C).trans hC) hY6 hYC hdC hpC
      exact ⟨a, p, hn⟩
  obtain ⟨a, p, hp⟩ := norm
  have hn := normalized_leaves hp
  let i := p 2
  let b := !(a.getLsbD i.val)
  let U : Finset (Q 5) := univ.filter (fun y => y i = b)
  have hB := normalized_true_half hYB hn hpB hdB 2 (by decide)
  have hC := normalized_true_half hYC hn hpC hdC 2 (by decide)
  simp only [encode_card, suffixHalf_encode] at hB hC
  have hcut := hv U
  have he : (S.filter fun u => rightBlock u ∈ U) = S.filter (fun u => u (i.natAdd 4) = b) := by
    ext u
    simp only [mem_filter, U, mem_univ, true_and, rightBlock]
  rw [he] at hcut
  have htot := hv (univ : Finset (Q 5))
  simp [hsize] at htot
  change 72 = A.card + 3 * B.card + 4 * C.card + 4 * N.card at htot
  have hA := card_le_card (inter_subset_left (s₁ := A) (s₂ := U))
  have hN := card_le_card (inter_subset_left (s₁ := N) (s₂ := U))
  refine ⟨i.natAdd 4, b, ?_⟩
  change (S.filter fun u => u (i.natAdd 4) = b).card =
    (A ∩ U).card + 3 * (B ∩ U).card + 4 * (C ∩ U).card + 4 * (N ∩ U).card at hcut
  rcases hsizeBC with ⟨h8, h10⟩ | ⟨h10, h8⟩
  · have hB2 : (B ∩ U).card = 2 := hB.1 h8
    have hC3 : (C ∩ U).card = 3 := hC.2 h10
    omega
  · have hB3 : (B ∩ U).card = 3 := hB.2 h10
    have hC2 : (C ∩ U).card = 2 := hC.1 h8
    omega

#print axioms reconstruction
#print axioms suffix_equations
#print axioms fiberCounts_of_admissible
#print axioms restricted_vertex_count
#print axioms horizontal_edge_count
#print axioms common_leaves_count
#print axioms carrier_equations
#print axioms tenShadowSecond_half_le_twentySeven

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSecondSharedLeaves
