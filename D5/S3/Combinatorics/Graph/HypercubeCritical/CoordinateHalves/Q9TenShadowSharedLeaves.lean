/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSharedLeaves
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSharedLeaves
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Three suffix axes have a twenty-vertex half in the exact ten-pattern projection. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves

/-! The exact ten-pattern case of Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2.
The first coordinate is the least significant bit of the projection code. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSharedLeaves

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9ThetaProjection (leftCode)
open Q9SignedProjection (join fiber signedRow leftParitySign q9_signed_row_split
  q9_signed_row_eq_zero_outside_projection)
open Q5SmallParitySupport (neighborParity eight_le_card_of_neighborParity)
open Q5SharedSixLeaves (degree leaves classify_normalized_carrier normalize_eight_carrier)
open Q7FourStarParallel (permuteBits)
open private pattern rightBlock leftCode_join join_blocks flipCode flip_pattern
  signed_row_four occupation row_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThetaProjection
open private column fiber_occupied signedRow_pairing_symmetric fiber_admissible
  unitOrZero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSelfAdjoint
open private carrier mem_carrier card_carrier mem_encoded flip_cubeBitVec encoded_neighborParity
  carrier_false_endpoints twelve_direction_edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection
open private degree_eq_card_flips sum_degrees from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves
open private permute_bit permute_injective permute_xor from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q7FourStarParallel

/-- The exact four-coordinate projection for the shared-six-leaves case. -/
def tenShadowSharedLeaves : Finset (BitVec 4) := {0, 1, 2, 3, 4, 11, 12, 13, 14, 15}

private def fiberLabels (a b c d : ℤ) (k : BitVec 4) : ℤ :=
  match k.toNat with
  | 0 => -a
  | 1 => -c
  | 2 => -b
  | 3 => d
  | 4 => -b - c
  | 11 => -b + c
  | 12 => a
  | 13 => b
  | 14 => c
  | 15 => d
  | _ => 0

private theorem column_apply (z : Q 9 → ℤ) (k : BitVec 4) (y : Q 5) :
    column z k y = fiber z y (pattern k) := rfl

private theorem reconstruction {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hproj : S.image leftCode = tenShadowSharedLeaves)
    (hzero : ∀ u ∉ S, z u = 0) (hrow : ∀ u, signedRow z u = 3 * z u)
    (y : Q 5) (k : BitVec 4) :
    column z k y = fiberLabels (column z 12 y) (column z 13 y)
      (column z 14 y) (column z 15 y) k := by
  have zero (l : BitVec 4) (hl : l ∉ tenShadowSharedLeaves) (v : Q 5) :
      column z l v = 0 := by
    apply hzero
    intro hv
    exact hl (by simpa only [leftCode_join, hproj] using mem_image_of_mem leftCode hv)
  have outside (l : BitVec 4) (hl : l ∉ tenShadowSharedLeaves) :
      signedRow (fiber z y) (pattern l) = 0 :=
    q9_signed_row_eq_zero_outside_projection hrow (zero l hl) y
  have e5 := signed_row_four (fiber z y) 5 4 7 1 13 1 (-1) (-1) 1 (by decide) (by decide)
  have e6 := signed_row_four (fiber z y) 6 7 4 2 14 1 1 (-1) 1 (by decide) (by decide)
  have e7 := signed_row_four (fiber z y) 7 6 5 3 15 1 (-1) 1 (-1) (by decide) (by decide)
  have e8 := signed_row_four (fiber z y) 8 9 10 12 0 1 1 1 1 (by decide) (by decide)
  have e9 := signed_row_four (fiber z y) 9 8 11 13 1 1 (-1) (-1) (-1) (by decide) (by decide)
  have e10 := signed_row_four (fiber z y) 10 11 8 14 2 1 1 (-1) (-1) (by decide) (by decide)
  have n5 : (5 : BitVec 4) ∉ tenShadowSharedLeaves := by decide
  have n6 : (6 : BitVec 4) ∉ tenShadowSharedLeaves := by decide
  have n7 : (7 : BitVec 4) ∉ tenShadowSharedLeaves := by decide
  have n8 : (8 : BitVec 4) ∉ tenShadowSharedLeaves := by decide
  have n9 : (9 : BitVec 4) ∉ tenShadowSharedLeaves := by decide
  have n10 : (10 : BitVec 4) ∉ tenShadowSharedLeaves := by decide
  simp only [outside 5 n5, outside 6 n6, outside 7 n7, outside 8 n8, outside 9 n9,
    outside 10 n10, ← column_apply, zero 5 n5, zero 6 n6, zero 7 n7, zero 8 n8,
    zero 9 n9, zero 10 n10, one_mul, neg_one_mul, neg_zero, zero_add]
    at e5 e6 e7 e8 e9 e10
  obtain ⟨k⟩ := k
  fin_cases k <;> try (first | rfl | exact zero _ (by decide) _)
  case «0» => change column z 0 y = -column z 12 y; omega
  case «1» => change column z 1 y = -column z 14 y; omega
  case «2» => change column z 2 y = -column z 13 y; omega
  case «3» => change column z 3 y = column z 15 y; omega
  case «4» => change column z 4 y = -column z 13 y - column z 14 y; omega
  case «11» => change column z 11 y = -column z 13 y + column z 14 y; omega

private theorem suffix_equations {z : Q 9 → ℤ}
    (hform : ∀ y k, column z k y = fiberLabels (column z 12 y) (column z 13 y)
      (column z 14 y) (column z 15 y) k)
    (hrow : ∀ u, signedRow z u = 3 * z u) (y : Q 5) :
    let a := column z 12 y
    let b := column z 13 y
    let c := column z 14 y
    let d := column z 15 y
    signedRow (column z 12) y = 3 * a - 2 * b - 2 * c ∧
    signedRow (column z 13) y = a - 3 * b - d ∧
    signedRow (column z 14) y = a - 3 * c + d ∧
    signedRow (column z 15) y = 2 * b - 2 * c + 3 * d := by
  have split (k : BitVec 4) :
      3 * column z k y = signedRow (fiber z y) (pattern k) +
        leftParitySign (pattern k) * signedRow (column z k) y :=
    q9_signed_row_split hrow (pattern k) y
  have r12 := split 12
  have r13 := split 13
  have r14 := split 14
  have r15 := split 15
  rw [signed_row_four _ 12 13 14 8 4 1 1 1 (-1) (by decide) (by decide)] at r12
  rw [signed_row_four _ 13 12 15 9 5 1 (-1) (-1) 1 (by decide) (by decide)] at r13
  rw [signed_row_four _ 14 15 12 10 6 1 1 (-1) 1 (by decide) (by decide)] at r14
  rw [signed_row_four _ 15 14 13 11 7 1 (-1) 1 (-1) (by decide) (by decide)] at r15
  simp only [← column_apply, hform y 4, hform y 5, hform y 6, hform y 7,
    hform y 8, hform y 9, hform y 10, hform y 11] at r12 r13 r14 r15
  change 3 * column z 12 y =
    1 * column z 13 y + (1 * column z 14 y + (1 * 0 +
    (-1) * (-column z 13 y - column z 14 y))) + 1 * signedRow (column z 12) y at r12
  change 3 * column z 13 y =
    1 * column z 12 y + ((-1) * column z 15 y + ((-1) * 0 +
    1 * 0)) + (-1) * signedRow (column z 13) y at r13
  change 3 * column z 14 y =
    1 * column z 15 y + (1 * column z 12 y + ((-1) * 0 +
    1 * 0)) + (-1) * signedRow (column z 14) y at r14
  change 3 * column z 15 y =
    1 * column z 14 y + ((-1) * column z 13 y + (1 *
    (-column z 13 y + column z 14 y) + (-1) * 0)) + 1 * signedRow (column z 15) y at r15
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem unit_column {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (k : BitVec 4) (y : Q 5) : unitOrZero (column z k y) := by
  by_cases h : join (pattern k) y ∈ S
  · exact Or.inr (hunit _ h)
  · exact Or.inl (hzero _ h)

private theorem disjoint_middle_labels {b c : ℤ}
    (hb : unitOrZero b) (hc : unitOrZero c)
    (h4 : unitOrZero (-b - c)) (h11 : unitOrZero (-b + c)) :
    b = 0 ∨ c = 0 := by
  rcases hb with h | h | h <;> rcases hc with h' | h' | h' <;>
    rcases h4 with p | p | p <;> rcases h11 with q | q | q <;> omega

private structure PrefixCarriers (S : Finset (Q 9)) : Prop where
  zero : carrier S 0 = carrier S 12
  one : carrier S 1 = carrier S 14
  two : carrier S 2 = carrier S 13
  three : carrier S 3 = carrier S 15
  eleven : carrier S 11 = carrier S 4
  middle : carrier S 4 = carrier S 13 ∪ carrier S 14
  disjoint : Disjoint (carrier S 13) (carrier S 14)
  outside : ∀ k ∉ tenShadowSharedLeaves, carrier S k = ∅

private theorem prefix_carriers {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hproj : S.image leftCode = tenShadowSharedLeaves)
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (hform : ∀ y k, column z k y = fiberLabels (column z 12 y) (column z 13 y)
      (column z 14 y) (column z 15 y) k)
    (hbc : ∀ y, column z 13 y = 0 ∨ column z 14 y = 0) :
    PrefixCarriers S := by
  have selected (k : BitVec 4) (y : Q 5) : y ∈ carrier S k ↔ column z k y ≠ 0 :=
    (mem_carrier S k y).trans (fiber_occupied hunit hzero k y)
  have same {k l : BitVec 4} (h : ∀ y, column z k y = column z l y) :
      carrier S k = carrier S l := by
    ext y
    rw [selected, h, selected]
  have neg {k l : BitVec 4} (h : ∀ y, column z k y = -column z l y) :
      carrier S k = carrier S l := by
    ext y
    rw [selected, h, neg_ne_zero, selected]
  have middle (y : Q 5) : column z 4 y ≠ 0 ↔
      column z 13 y ≠ 0 ∨ column z 14 y ≠ 0 := by
    have h4 : column z 4 y = -column z 13 y - column z 14 y := hform y 4
    rw [h4]
    rcases hbc y with h | h <;> rw [h] <;> simp
  have eleven (y : Q 5) : column z 11 y ≠ 0 ↔
      column z 13 y ≠ 0 ∨ column z 14 y ≠ 0 := by
    have h11 : column z 11 y = -column z 13 y + column z 14 y := hform y 11
    rw [h11]
    rcases hbc y with h | h <;> rw [h] <;> simp
  refine ⟨neg (fun y => hform y 0), neg (fun y => hform y 1), neg (fun y => hform y 2),
    same (fun y => hform y 3), ?_, ?_, ?_, ?_⟩
  · ext y
    simp only [selected, eleven, middle]
  · ext y
    simp only [mem_union, selected, middle]
  · exact disjoint_left.mpr (fun y hb hc =>
      (hbc y).elim ((selected 13 y).mp hb) ((selected 14 y).mp hc))
  · intro k hk
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hk (by simpa only [leftCode_join, hproj] using
      mem_image_of_mem leftCode ((mem_carrier S k y).mp hy))


private theorem carrier_occupation (S : Finset (Q 9)) (k : BitVec 4) (y : Q 5) :
    occupation S k y = if y ∈ carrier S k then 1 else 0 := by
  exact if_congr (mem_carrier S k y).symm rfl rfl

private noncomputable abbrev verticalDegree (S : Finset (Q 9)) (k : BitVec 4) (y : Q 5) :=
  ∑ i : Fin 5, occupation S k (flip y i)

open Classical in
private theorem equal_middle_intersections {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (h : PrefixCarriers S) (y : Q 5) (hy : y ∈ carrier S 4) :
    (y ∈ carrier S 12 ↔ y ∈ carrier S 15) ∧
    verticalDegree S 4 y = if y ∈ carrier S 12 then 1 else 3 := by
  have p := row_degree hr (k := 4) (a := 5) (b := 6) (c := 0) (d := 12)
    (by decide) ((mem_carrier _ _ _).mp hy)
  have q := row_degree hr (k := 11) (a := 10) (b := 9) (c := 15) (d := 3)
    (by decide) ((mem_carrier _ _ _).mp (h.eleven ▸ hy))
  have h4 : verticalDegree S 11 y = verticalDegree S 4 y := by
    apply sum_congr rfl
    intro i _
    simp only [carrier_occupation, h.eleven]
  have a (k : BitVec 4) (hk : k ∉ tenShadowSharedLeaves) : occupation S k y = 0 := by
    rw [carrier_occupation, h.outside k hk]
    simp
  have e0 : occupation S 0 y = occupation S 12 y := by
    simp only [carrier_occupation, h.zero]
  have e3 : occupation S 3 y = occupation S 15 y := by
    simp only [carrier_occupation, h.three]
  rw [a 5 (by decide), a 6 (by decide), e0, zero_add, zero_add] at p
  rw [a 10 (by decide), a 9 (by decide), e3, zero_add, zero_add] at q
  change occupation S 12 y + occupation S 12 y + verticalDegree S 4 y = 3 at p
  change occupation S 15 y + occupation S 15 y + verticalDegree S 11 y = 3 at q
  rw [h4] at q
  have equal : occupation S 12 y = occupation S 15 y := by omega
  have occA := carrier_occupation S 12 y
  have occB := carrier_occupation S 15 y
  constructor
  · constructor
    · intro ha
      by_contra hb
      rw [occA, occB, if_pos ha, if_neg hb] at equal
      omega
    · intro hb
      by_contra ha
      rw [occA, occB, if_neg ha, if_pos hb] at equal
      omega
  · by_cases ha : y ∈ carrier S 12
    · rw [occA, if_pos ha] at p
      rw [if_pos ha]
      omega
    · rw [occA, if_neg ha] at p
      rw [if_neg ha]
      omega

open Classical in
private theorem vertical_degree_zero_three {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (h : PrefixCarriers S) (y : Q 5) :
    (y ∈ carrier S 12 → verticalDegree S 0 y = if y ∈ carrier S 4 then 1 else 3) ∧
    (y ∈ carrier S 15 → verticalDegree S 3 y = if y ∈ carrier S 4 then 1 else 3) := by
  have hsum : occupation S 14 y + occupation S 13 y = occupation S 4 y := by
    have hm (y : Q 5) : y ∈ carrier S 4 ↔ y ∈ carrier S 13 ∨ y ∈ carrier S 14 := by
      rw [h.middle, mem_union]
    by_cases hb : y ∈ carrier S 13 <;> by_cases hc : y ∈ carrier S 14
    · exact False.elim (disjoint_left.mp h.disjoint hb hc)
    · have hd := (hm y).mpr (Or.inl hb)
      simp only [carrier_occupation, hd, hb, hc, ite_true, ite_false, zero_add]
    · have hd := (hm y).mpr (Or.inr hc)
      simp only [carrier_occupation, hd, hb, hc, ite_true, ite_false, add_zero]
    · have hd : y ∉ carrier S 4 := fun h4 => ((hm y).mp h4).elim hb hc
      simp only [carrier_occupation, hb, hc, hd, ite_false, add_zero]
  have a (k : BitVec 4) (hk : k ∉ tenShadowSharedLeaves) : occupation S k y = 0 := by
    rw [carrier_occupation, h.outside k hk]
    simp
  have same {k l : BitVec 4} (hkl : carrier S k = carrier S l) :
      occupation S k y = occupation S l y := by
    simp only [carrier_occupation, hkl]
  constructor
  · intro hy
    have p := row_degree hr (k := 0) (a := 1) (b := 2) (c := 4) (d := 8)
      (by decide) ((mem_carrier _ _ _).mp (h.zero ▸ hy))
    rw [same h.one, same h.two, a 8 (by decide), add_zero] at p
    change occupation S 14 y + (occupation S 13 y + occupation S 4 y) +
      verticalDegree S 0 y = 3 at p
    have v : 2 * occupation S 4 y + verticalDegree S 0 y = 3 := by omega
    rw [carrier_occupation] at v
    by_cases hc : y ∈ carrier S 4 <;> simp only [hc, ite_true, ite_false] at v ⊢ <;> omega
  · intro hy
    have p := row_degree hr (k := 3) (a := 2) (b := 1) (c := 7) (d := 11)
      (by decide) ((mem_carrier _ _ _).mp (h.three ▸ hy))
    rw [same h.one, same h.two, same h.eleven, a 7 (by decide), zero_add] at p
    change occupation S 13 y + (occupation S 14 y + occupation S 4 y) +
      verticalDegree S 3 y = 3 at p
    have v : 2 * occupation S 4 y + verticalDegree S 3 y = 3 := by omega
    rw [carrier_occupation] at v
    by_cases hc : y ∈ carrier S 4 <;> simp only [hc, ite_true, ite_false] at v ⊢ <;> omega

open Classical in
private theorem middle_sign {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (h : PrefixCarriers S) (y : Q 5)
    (hform : ∀ k, column z k y = fiberLabels (column z 12 y) (column z 13 y)
      (column z 14 y) (column z 15 y) k)
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (hsign : ∀ u ∈ S, ∀ i : Fin 9, flip u i ∈ S →
      truePrefixSign u i = z u * z (flip u i)) :
    column z 14 y * (column z 15 y - column z 12 y) = 0 := by
  let f := fun k => column z k y
  change f 14 * (f 15 - f 12) = 0
  have e0 : f 0 = -f 12 := hform 0
  have e1 : f 1 = -f 14 := hform 1
  have e3 : f 3 = f 15 := hform 3
  by_cases hc : f 14 = 0
  · rw [hc, zero_mul]
  have hc' : f 1 ≠ 0 := by rwa [e1, neg_ne_zero]
  have hy : y ∈ carrier S 4 := by
    rw [h.middle, mem_union, mem_carrier S 14 y, fiber_occupied hunit hzero]
    exact Or.inr hc
  have hAB := (equal_middle_intersections hr h y hy).1
  by_cases ha : y ∈ carrier S 12
  · have hf0 : f 0 ≠ 0 := (fiber_occupied hunit hzero 0 y).mp
      ((mem_carrier _ _ _).mp (h.zero ▸ ha))
    have hf3 : f 3 ≠ 0 := (fiber_occupied hunit hzero 3 y).mp
      ((mem_carrier _ _ _).mp (h.three ▸ hAB.mp ha))
    have pass := (fiber_admissible hr hunit hzero hsign y).2 (1 : Fin 16) hc'
    have p := pass.2 (0 : Fin 4) hf0
    have r := pass.2 (1 : Fin 4) hf3
    change 0 < (1 : ℤ) * f 1 * f 0 at p
    change 0 < (-1 : ℤ) * f 1 * f 3 at r
    have u0 : unitOrZero (f 0) := unit_column hunit hzero 0 y
    have u3 : unitOrZero (f 3) := unit_column hunit hzero 3 y
    have u1 : unitOrZero (f 1) := unit_column hunit hzero 1 y
    have he : f 0 + f 3 = 0 := by
      rcases u0 with h0 | h0 | h0 <;> rcases u3 with h3 | h3 | h3 <;>
        rcases u1 with h1 | h1 | h1 <;>
        simp only [h0, h1, h3] at p r ⊢ <;> omega
    have : f 15 - f 12 = 0 := by omega
    rw [this, mul_zero]
  · have hb : y ∉ carrier S 15 := fun hb => ha (hAB.mpr hb)
    have hza : f 12 = 0 := hzero _ (fun hn => ha ((mem_carrier _ _ _).mpr hn))
    have hzb : f 15 = 0 := hzero _ (fun hn => hb ((mem_carrier _ _ _).mpr hn))
    rw [hza, hzb, sub_self, mul_zero]

private def alternatingPairing (f g : Q 5 → ℤ) (y : Q 5) : ℤ :=
  signedRow f y * g y - f y * signedRow g y

private theorem sum_alternatingPairing (f g : Q 5 → ℤ) :
    ∑ y, alternatingPairing f g y = 0 := by
  simp only [alternatingPairing, sum_sub_distrib, signedRow_pairing_symmetric f g, sub_self]

private theorem equal_square_sums {a b c d : Q 5 → ℤ}
    (ha : ∀ y, signedRow a y = 3 * a y - 2 * b y - 2 * c y)
    (hc : ∀ y, signedRow c y = a y - 3 * c y + d y)
    (hd : ∀ y, signedRow d y = 2 * b y - 2 * c y + 3 * d y)
    (hbc : ∀ y, b y = 0 ∨ c y = 0) (hcd : ∀ y, c y * (d y - a y) = 0) :
    (∑ y, a y ^ 2) = ∑ y, d y ^ 2 := by
  have pointwise (y : Q 5) :
      -alternatingPairing a c y - alternatingPairing c d y = a y ^ 2 - d y ^ 2 := by
    have zero : b y * c y = 0 := by rcases hbc y with h | h <;> rw [h] <;> simp
    rw [alternatingPairing, alternatingPairing, ha, hc, hd]
    calc
      _ = a y ^ 2 - d y ^ 2 + 6 * (c y * (d y - a y)) + 4 * (b y * c y) := by ring
      _ = _ := by simp [hcd, zero]
  have h := sum_congr rfl (fun y (_ : y ∈ (univ : Finset (Q 5))) => pointwise y)
  simpa only [sum_sub_distrib, sum_neg_distrib, sum_alternatingPairing, neg_zero,
    sub_self, sub_eq_zero] using h.symm

private theorem sum_column_sq {S : Finset (Q 9)} {z : Q 9 → ℤ}
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (k : BitVec 4) :
    (∑ y : Q 5, column z k y ^ 2) = ((carrier S k).card : ℤ) := by
  have h (y : Q 5) : column z k y ^ 2 = if y ∈ carrier S k then 1 else 0 := by
    by_cases hy : y ∈ carrier S k
    · have hs : column z k y = 1 ∨ column z k y = -1 := hunit _ ((mem_carrier _ _ _).mp hy)
      rcases hs with h | h <;> norm_num [hy, h]
    · have hz : column z k y = 0 := hzero _ (fun hn => hy ((mem_carrier _ _ _).mpr hn))
      simp [hy, hz]
  simp only [h, sum_boole, filter_mem_eq_inter, univ_inter]


private theorem card_by_prefix {S T : Finset (Q 9)} (hsub : T ⊆ S)
    (hproj : S.image leftCode = tenShadowSharedLeaves) :
    T.card = ∑ k ∈ tenShadowSharedLeaves, (carrier T k).card := by
  simpa only [card_carrier] using
    (card_eq_sum_card_fiberwise (f := leftCode) (s := T) (t := tenShadowSharedLeaves)
      (fun u hu => hproj ▸ mem_image_of_mem leftCode (hsub hu)))

private theorem sum_projection (f : BitVec 4 → ℕ) :
    (∑ k ∈ tenShadowSharedLeaves, f k) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 11 + (f 12 + (f 13 + (f 14 + f 15)))))))) := by
  let codes : List (BitVec 4) := [0, 1, 2, 3, 4, 11, 12, 13, 14, 15]
  have hcodes : tenShadowSharedLeaves = codes.toFinset := by decide
  have hnodup : codes.Nodup := by decide
  rw [hcodes, List.sum_toFinset f hnodup]
  simp only [codes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem sum_carriers {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSharedLeaves) (h : PrefixCarriers S) :
    S.card = 2 * (carrier S 12).card + 2 * (carrier S 15).card + 4 * (carrier S 4).card := by
  have hcard := card_by_prefix (Subset.refl S) hproj
  rw [sum_projection, h.zero, h.one, h.two, h.three, h.eleven] at hcard
  have hc := card_union_of_disjoint h.disjoint
  rw [← h.middle] at hc
  omega

private def edgeStarts (i : Fin 4) : Finset (BitVec 4) :=
  tenShadowSharedLeaves.filter fun k =>
    pattern k i = false ∧ flipCode k i ∈ tenShadowSharedLeaves

private theorem direction_edges_by_prefix {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSharedLeaves) (h : PrefixCarriers S)
    (i : Fin 4) :
    directionEdges S (i.castAdd 5) =
      ∑ k ∈ edgeStarts i, (carrier S k ∩ carrier S (flipCode k i)).card := by
  unfold directionEdges
  rw [card_by_prefix (filter_subset _ S) hproj, edgeStarts, sum_filter]
  apply sum_congr rfl
  intro k _
  rw [carrier_false_endpoints]
  cases hk : pattern k i
  · by_cases hf : flipCode k i ∈ tenShadowSharedLeaves
    · simp [hf]
    · simp [hf, h.outside _ hf]
  · simp

private theorem direction_edges_shared {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSharedLeaves) (h : PrefixCarriers S)
    (hAB : carrier S 12 ∩ carrier S 4 = carrier S 15 ∩ carrier S 4) (i : Fin 4) :
    directionEdges S (i.castAdd 5) = 2 * (carrier S 12 ∩ carrier S 4).card := by
  let A := carrier S 12
  let B := carrier S 15
  let C := carrier S 4
  let X := carrier S 13
  let Y := carrier S 14
  have card_split (T : Finset (Q 5)) :
      (T ∩ X).card + (T ∩ Y).card = (T ∩ C).card := by
    have hd : Disjoint (T ∩ X) (T ∩ Y) :=
      h.disjoint.mono inter_subset_right inter_subset_right
    rw [← card_union_of_disjoint hd]
    change ((T ∩ carrier S 13) ∪ (T ∩ carrier S 14)).card = _
    rw [← inter_union_distrib_left, ← h.middle]
  have ha := card_split A
  have hb := card_split B
  have hc : (A ∩ C).card = (B ∩ C).card := congrArg Finset.card hAB
  rw [direction_edges_by_prefix hproj h]
  fin_cases i
  · have hs : edgeStarts (0 : Fin 4) = {0, 2, 12, 14} := by decide
    change (∑ k ∈ edgeStarts (0 : Fin 4), (carrier S k ∩ carrier S (flipCode k 0)).card) = _
    rw [hs, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have f0 : flipCode 0 (0 : Fin 4) = 1 := by decide
    have f2 : flipCode 2 (0 : Fin 4) = 3 := by decide
    have f12 : flipCode 12 (0 : Fin 4) = 13 := by decide
    have f14 : flipCode 14 (0 : Fin 4) = 15 := by decide
    rw [f0, f2, f12, f14]
    simp only [h.zero, h.one, h.two, h.three]
    change (A ∩ Y).card + ((X ∩ B).card + ((A ∩ X).card + ((Y ∩ B).card))) = 2 * (A ∩ C).card
    rw [inter_comm X B, inter_comm Y B]
    omega
  · have hs : edgeStarts (1 : Fin 4) = {0, 1, 12, 13} := by decide
    change (∑ k ∈ edgeStarts (1 : Fin 4), (carrier S k ∩ carrier S (flipCode k 1)).card) = _
    rw [hs, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have f0 : flipCode 0 (1 : Fin 4) = 2 := by decide
    have f1 : flipCode 1 (1 : Fin 4) = 3 := by decide
    have f12 : flipCode 12 (1 : Fin 4) = 14 := by decide
    have f13 : flipCode 13 (1 : Fin 4) = 15 := by decide
    rw [f0, f1, f12, f13]
    simp only [h.zero, h.one, h.two, h.three]
    change (A ∩ X).card + ((Y ∩ B).card + ((A ∩ Y).card + ((X ∩ B).card))) = 2 * (A ∩ C).card
    rw [inter_comm Y B, inter_comm X B]
    omega
  · have hs : edgeStarts (2 : Fin 4) = {0, 11} := by decide
    change (∑ k ∈ edgeStarts (2 : Fin 4), (carrier S k ∩ carrier S (flipCode k 2)).card) = _
    rw [hs, sum_insert (by decide), sum_singleton]
    have f0 : flipCode 0 (2 : Fin 4) = 4 := by decide
    have f11 : flipCode 11 (2 : Fin 4) = 15 := by decide
    rw [f0, f11]
    simp only [h.zero, h.eleven]
    change (A ∩ C).card + ((C ∩ B).card) = 2 * (A ∩ C).card
    rw [inter_comm C B]
    omega
  · have hs : edgeStarts (3 : Fin 4) = {3, 4} := by decide
    change (∑ k ∈ edgeStarts (3 : Fin 4), (carrier S k ∩ carrier S (flipCode k 3)).card) = _
    rw [hs, sum_insert (by decide), sum_singleton]
    have f3 : flipCode 3 (3 : Fin 4) = 11 := by decide
    have f4 : flipCode 4 (3 : Fin 4) = 12 := by decide
    rw [f3, f4]
    simp only [h.three, h.eleven]
    change (B ∩ C).card + ((C ∩ A).card) = 2 * (A ∩ C).card
    rw [inter_comm C A]
    omega

open Classical in
private theorem card_shared_leaves {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSharedLeaves) (h : PrefixCarriers S)
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72)
    (hAB : carrier S 12 ∩ carrier S 4 = carrier S 15 ∩ carrier S 4) :
    (carrier S 12 ∩ carrier S 4).card = 6 := by
  have ht (i : Fin 4) := twelve_direction_edges hr hb hsize (i.castAdd 5)
  have hcount := (direction_edges_shared hproj h hAB 0).symm.trans (ht 0)
  omega

private noncomputable def encode (A : Finset (Q 5)) : Finset (BitVec 5) :=
  A.image (cubeBitVec 5).symm

private theorem encode_card (A : Finset (Q 5)) : (encode A).card = A.card :=
  card_image_of_injective _ (cubeBitVec 5).symm.injective

private theorem verticalDegree_eq (S : Finset (Q 9)) (k : BitVec 4) (x : BitVec 5) :
    verticalDegree S k (cubeBitVec 5 x) = degree (encode (carrier S k)) x := by
  classical
  rw [degree_eq_card_flips, Finset.card_filter]
  apply sum_congr rfl
  intro i _
  simp only [carrier_occupation, encode, mem_encoded, flip_cubeBitVec]

private theorem encoded_degree_profile {S : Finset (Q 9)} {k : BitVec 4}
    {A F : Finset (Q 5)}
    (hs : carrier S k = A)
    (h : ∀ y ∈ A, verticalDegree S k y = if y ∈ F then 1 else 3) :
    ∀ x ∈ encode A, degree (encode A) x = if x ∈ encode F then 1 else 3 := by
  intro x hx
  rw [← hs, ← verticalDegree_eq]
  simpa only [encode, mem_encoded] using h (cubeBitVec 5 x)
    ((mem_encoded A x).mp hx)

open Classical in
private theorem parity_of_column {S : Finset (Q 9)} {z : Q 9 → ℤ} {k : BitVec 4}
    (hunit : ∀ u ∈ S, z u = 1 ∨ z u = -1) (hzero : ∀ u ∉ S, z u = 0)
    (g : Q 5 → ℤ)
    (hrow : ∀ y, signedRow (column z k) y = 3 * column z k y - 2 * g y) :
    ∀ x, decide (x ∈ encode (carrier S k)) = neighborParity (encode (carrier S k)) x :=
  encoded_neighborParity (a := column z k) (b := g) (c := fun _ => 0)
    (fun y hy => hunit _ ((mem_carrier S k y).mp hy))
    (fun y hy => hzero _ (fun hp => hy ((mem_carrier S k y).mpr hp)))
    (by simpa only [mul_zero, sub_zero] using hrow)

private theorem signedRow_add (f g : Q 5 → ℤ) (y : Q 5) :
    signedRow (fun x => f x + g x) y = signedRow f y + signedRow g y := by
  simp only [signedRow, mul_add, sum_add_distrib]

private theorem signedRow_neg (f : Q 5 → ℤ) (y : Q 5) :
    signedRow (fun x => -f x) y = -signedRow f y := by
  simp only [signedRow, mul_neg, sum_neg_distrib]

private theorem encoded_nonempty {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSharedLeaves)
    {k : BitVec 4} (hk : k ∈ tenShadowSharedLeaves) : (encode (carrier S k)).Nonempty := by
  obtain ⟨u, hu, hku⟩ := mem_image.mp (hproj.symm ▸ hk)
  refine ⟨(cubeBitVec 5).symm (rightBlock u), mem_image_of_mem _
    ((mem_carrier S k _).mpr ?_)⟩
  rwa [← hku, join_blocks]

open private sum_degrees_sides side from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q5SharedSixLeaves

private theorem size_constraints {A F : Finset (BitVec 5)}
    (hF : F ⊆ A) (hA : A.Nonempty) (h6 : F.card = 6)
    (hpar : ∀ x, decide (x ∈ A) = neighborParity A x)
    (hdeg : ∀ x ∈ A, degree A x = if x ∈ F then 1 else 3) :
    8 ≤ A.card ∧ A.card % 2 = 0 := by
  constructor
  · apply eight_le_card_of_neighborParity hA hpar
    intro x hx
    rw [← degree_eq_card_flips, hdeg x hx]
    split <;> omega
  · have htotal := sum_degrees hdeg (Subset.refl A)
    have hcenters := card_sdiff_add_card_eq_card hF
    have hsplit : (∑ x ∈ A, degree A x) =
        (∑ x ∈ side A false, degree A x) + ∑ x ∈ side A true, degree A x := by
      rw [← sum_filter_add_sum_filter_not A (fun x => Q5SmallParitySupport.bitParity x = false)
        (degree A)]
      congr 2
      ext x
      cases Q5SmallParitySupport.bitParity x <;> simp
    have hbalance := sum_degrees_sides A
    omega


private def denormalize (a : BitVec 5) (p : Equiv.Perm (Fin 5)) :
    BitVec 5 ≃ BitVec 5 where
  toFun x := permuteBits p x ^^^ a
  invFun x := permuteBits p.symm (x ^^^ a)
  left_inv x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 5 := ⟨j, hj⟩
    change (permuteBits p.symm (permuteBits p x ^^^ a ^^^ a)).getLsbD i.val = _
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, permute_bit, permute_bit,
      Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 5 := ⟨j, hj⟩
    change (permuteBits p (permuteBits p.symm (x ^^^ a)) ^^^ a).getLsbD i.val = _
    rw [BitVec.getLsbD_xor, permute_bit, permute_bit, Equiv.symm_symm, Equiv.apply_symm_apply,
      BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

private theorem denormalize_bit (a : BitVec 5) (p : Equiv.Perm (Fin 5))
    (x : BitVec 5) (i : Fin 5) :
    (denormalize a p x).getLsbD (p i).val = (x.getLsbD i.val ^^ a.getLsbD (p i).val) := by
  simp only [denormalize, Equiv.coe_fn_mk, BitVec.getLsbD_xor, permute_bit, Equiv.symm_apply_apply]

private theorem denormalize_flip (a : BitVec 5) (p : Equiv.Perm (Fin 5))
    (x : BitVec 5) (i : Fin 5) :
    denormalize a p (x ^^^ BitVec.twoPow 5 i.val) =
      denormalize a p x ^^^ BitVec.twoPow 5 (p i).val := by
  have axis : permuteBits p (BitVec.twoPow 5 i.val) = BitVec.twoPow 5 (p i).val := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let k : Fin 5 := ⟨j, hj⟩
    change (permuteBits p (BitVec.twoPow 5 i.val)).getLsbD k.val = _
    rw [permute_bit, BitVec.getLsbD_twoPow, BitVec.getLsbD_twoPow]
    simp only [i.isLt, (p i).isLt, decide_true, Bool.true_and]
    congr 1
    rw [← Fin.ext_iff, Equiv.eq_symm_apply]
    exact propext Fin.ext_iff
  change permuteBits p (x ^^^ BitVec.twoPow 5 i.val) ^^^ a =
    (permuteBits p x ^^^ a) ^^^ BitVec.twoPow 5 (p i).val
  rw [permute_xor, axis, BitVec.xor_assoc, BitVec.xor_assoc, BitVec.xor_comm _ a]

private theorem degree_normalized (a : BitVec 5) (p : Equiv.Perm (Fin 5))
    (S : Finset (BitVec 5)) (x : BitVec 5) :
    degree (S.map (denormalize a p).symm.toEmbedding) x = degree S (denormalize a p x) := by
  classical
  simp only [degree_eq_card_flips, Finset.card_filter, mem_map_equiv, Equiv.symm_symm,
    denormalize_flip]
  exact Equiv.sum_comp p (fun i : Fin 5 =>
    if denormalize a p x ^^^ BitVec.twoPow 5 i.val ∈ S then 1 else 0)

open private bitValue bitValue_xor bitValue_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridProjection

private theorem bitValue_neighborParity (S : Finset (BitVec 5)) (x : BitVec 5) :
    bitValue (neighborParity S x) = (degree S x : ZMod 2) := by
  rw [degree_eq_card_flips, card_filter, Nat.cast_sum]
  have hb (i : Fin 5) :
      ((if x ^^^ BitVec.twoPow 5 i.val ∈ S then 1 else 0 : ℕ) : ZMod 2) =
        bitValue (decide (x ^^^ BitVec.twoPow 5 i.val ∈ S)) := by
    by_cases hi : x ^^^ BitVec.twoPow 5 i.val ∈ S
    · simp only [bitValue, hi, ite_true, decide_true, Bool.cond_true, Nat.cast_one]
    · simp only [bitValue, hi, ite_false, decide_false, Bool.cond_false, Nat.cast_zero]
  simp_rw [hb]
  simp only [neighborParity, bitValue_xor, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.reduceSucc, add_zero]
  change _ = bitValue (decide ((x ^^^ 1) ∈ S)) + (bitValue (decide ((x ^^^ 2) ∈ S)) +
    (bitValue (decide ((x ^^^ 4) ∈ S)) +
      (bitValue (decide ((x ^^^ 8) ∈ S)) + bitValue (decide ((x ^^^ 16) ∈ S)))))
  simp only [add_assoc]

private theorem normalized_leaves {F : Finset (BitVec 5)} {a : BitVec 5}
    {p : Equiv.Perm (Fin 5)}
    (hF : F.image (fun x => x ^^^ a) = leaves.image (permuteBits p)) :
    F.map (denormalize a p).symm.toEmbedding = leaves := by
  ext x
  rw [mem_map_equiv, Equiv.symm_symm]
  constructor
  · intro hx
    have hm : permuteBits p x ∈ F.image (fun y => y ^^^ a) := by
      refine mem_image.mpr ⟨denormalize a p x, hx, ?_⟩
      change (permuteBits p x ^^^ a) ^^^ a = permuteBits p x
      simp [BitVec.xor_assoc]
    rw [hF] at hm
    obtain ⟨y, hy, he⟩ := mem_image.mp hm
    rwa [← permute_injective p he]
  · intro hx
    have hm : permuteBits p x ∈ F.image (fun y => y ^^^ a) :=
      hF ▸ mem_image_of_mem (permuteBits p) hx
    obtain ⟨y, hy, he⟩ := mem_image.mp hm
    have hyx : y = denormalize a p x := by
      change y = permuteBits p x ^^^ a
      rw [← he]
      simp [BitVec.xor_assoc]
    exact hyx ▸ hy

private def suffixHalf (A : Finset (BitVec 5)) (i : Fin 5) (b : Bool) : Nat :=
  (A.filter fun x => x.getLsbD i.val = b).card

private theorem normalized_half_table : ∀ i : Fin 5, 2 ≤ i.val →
    suffixHalf (leaves ∪ {0, 3}) i true = 2 ∧
    suffixHalf (leaves ∪ {1, 5, 9, 17}) i true = 3 ∧
    suffixHalf (leaves ∪ {2, 6, 10, 18}) i true = 3 := by
  decide

private theorem normalized_true_half {A F : Finset (BitVec 5)} {a : BitVec 5}
    {p : Equiv.Perm (Fin 5)}
    (hF : F ⊆ A) (hFnorm : F.map (denormalize a p).symm.toEmbedding = leaves)
    (hpar : ∀ x, decide (x ∈ A) = neighborParity A x)
    (hdeg : ∀ x ∈ A, degree A x = if x ∈ F then 1 else 3)
    (i : Fin 5) (hi : 2 ≤ i.val) :
    (A.card = 8 → suffixHalf A (p i) (!(a.getLsbD (p i).val)) = 2) ∧
    (A.card = 10 → suffixHalf A (p i) (!(a.getLsbD (p i).val)) = 3) := by
  let e := denormalize a p
  let T := A.map e.symm.toEmbedding
  have hTcard : T.card = A.card := card_map _
  have hsub : leaves ⊆ T := by
    rw [← hFnorm]
    intro x hx
    exact mem_map_equiv.mpr (hF (mem_map_equiv.mp hx))
  have hTdeg (x : BitVec 5) (hx : x ∈ T) :
      degree T x = if x ∈ leaves then 1 else 3 := by
    rw [degree_normalized, ← hFnorm]
    simpa only [mem_map_equiv, Equiv.symm_symm] using
      hdeg (e x) (mem_map_equiv.mp hx)
  have hTpar (x : BitVec 5) : decide (x ∈ T) = neighborParity T x := by
    apply bitValue_injective
    rw [bitValue_neighborParity, degree_normalized, ← bitValue_neighborParity, ← hpar]
    simp only [T, mem_map_equiv, Equiv.symm_symm, e]
  have hshape := classify_normalized_carrier hsub hTdeg hTpar
  have hhalf : suffixHalf T i true = suffixHalf A (p i) (!(a.getLsbD (p i).val)) := by
    unfold suffixHalf
    have hmap : (T.filter fun x => x.getLsbD i.val = true).map e.toEmbedding =
        A.filter (fun x => x.getLsbD (p i).val = !(a.getLsbD (p i).val)) := by
      apply Finset.ext
      intro x
      obtain ⟨u, rfl⟩ := e.surjective x
      simp only [mem_map_equiv, Equiv.symm_apply_apply, mem_filter, T, Equiv.symm_symm]
      change (_ ∧ _) ↔ (_ ∧ (denormalize a p u).getLsbD (p i).val = _)
      rw [denormalize_bit]
      cases a.getLsbD (p i).val <;> cases u.getLsbD i.val <;> simp
    rw [← hmap, card_map]
  have hsplit : leaves ∪ (T \ leaves) = T := by
    rw [union_comm, sdiff_union_of_subset hsub]
  have ht := normalized_half_table i hi
  constructor
  · intro h8
    have hs := hshape.1 (hTcard.trans h8)
    rw [← hhalf, ← hsplit, hs]
    exact ht.1
  · intro h10
    rcases hshape.2 (hTcard.trans h10) with hs | hs
    · rw [← hhalf, ← hsplit, hs]
      exact ht.2.1
    · rw [← hhalf, ← hsplit, hs]
      exact ht.2.2


private theorem carrier_suffix_cut (S : Finset (Q 9)) (k : BitVec 4) (i : Fin 5) (b : Bool) :
    carrier (S.filter fun u => u (i.natAdd 4) = b) k =
      (carrier S k).filter (fun y => y i = b) := by
  classical
  ext y
  simp only [mem_carrier, mem_filter, join, Fin.append_right]

private theorem suffixHalf_encode (A : Finset (Q 5)) (i : Fin 5) (b : Bool) :
    suffixHalf (encode A) i b = (A.filter fun y => y i = b).card := by
  classical
  have he : (encode A).filter (fun x => x.getLsbD i.val = b) =
      encode (A.filter fun y => y i = b) := by
    ext x
    simp only [encode, mem_filter, mem_encoded]
    rfl
  rw [suffixHalf, he, encode_card]

private theorem sum_suffix_half {S : Finset (Q 9)}
    (hproj : S.image leftCode = tenShadowSharedLeaves) (h : PrefixCarriers S)
    (i : Fin 5) (b : Bool) :
    (S.filter fun u => u (i.natAdd 4) = b).card =
      2 * suffixHalf (encode (carrier S 12)) i b + 2 * suffixHalf (encode (carrier S 15)) i b +
        4 * suffixHalf (encode (carrier S 4)) i b := by
  classical
  have ht := card_by_prefix (filter_subset (fun u : Q 9 => u (i.natAdd 4) = b) S) hproj
  simp only [sum_projection, carrier_suffix_cut, h.zero, h.one, h.two, h.three, h.eleven] at ht
  have hd : Disjoint ((carrier S 13).filter (fun y => y i = b))
      ((carrier S 14).filter (fun y => y i = b)) :=
    h.disjoint.mono (filter_subset _ _) (filter_subset _ _)
  have hc := card_union_of_disjoint hd
  rw [← filter_union, ← h.middle] at hc
  simp only [suffixHalf_encode]
  omega

open Classical in
/-- A Huang-balanced induced cubic support of order 72 with this exact projection
has three distinct suffix coordinates, each with a half of cardinality 20. -/
theorem tenShadowSharedLeaves_three_halves {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (hsize : S.card = 72)
    (hproj : S.image leftCode = tenShadowSharedLeaves) :
    ∃ axes : Fin 3 ↪ Fin 9, ∃ side : Fin 3 → Bool, ∀ j,
      (S.filter fun u => u (axes j) = side j).card = 20 := by
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hr hb
  change ∀ u, signedRow z u = 3 * z u at hrow
  have form := reconstruction hproj hzero hrow
  have disjoint (y : Q 5) : column z 13 y = 0 ∨ column z 14 y = 0 := by
    have h4 : column z 4 y = -column z 13 y - column z 14 y := form y 4
    have h11 : column z 11 y = -column z 13 y + column z 14 y := form y 11
    exact disjoint_middle_labels (unit_column hunit hzero 13 y) (unit_column hunit hzero 14 y)
      (h4 ▸ unit_column hunit hzero 4 y) (h11 ▸ unit_column hunit hzero 11 y)
  have pc := prefix_carriers hproj hunit hzero form disjoint
  let A₀ := carrier S 12
  let B₀ := carrier S 15
  let C₀ := carrier S 4
  let F₀ := A₀ ∩ C₀
  let A := encode A₀
  let B := encode B₀
  let C := encode C₀
  let F := encode F₀
  have shared : F₀ = B₀ ∩ C₀ := by
    ext y
    simp only [F₀, mem_inter]
    constructor
    · rintro ⟨ha, hc⟩
      exact ⟨(equal_middle_intersections hr pc y hc).1.mp ha, hc⟩
    · rintro ⟨hb', hc⟩
      exact ⟨(equal_middle_intersections hr pc y hc).1.mpr hb', hc⟩
  have h6 : F.card = 6 := (encode_card _).trans (card_shared_leaves hproj pc hr hb hsize shared)
  have hFA : F ⊆ A := image_mono _ inter_subset_left
  have hFB : F ⊆ B := by
    change encode F₀ ⊆ _
    rw [shared]
    exact image_mono _ inter_subset_left
  have hFC : F ⊆ C := image_mono _ inter_subset_right
  have dA : ∀ x ∈ A, degree A x = if x ∈ F then 1 else 3 := by
    apply encoded_degree_profile (hs := pc.zero)
    intro y hy
    have hm : y ∈ F₀ ↔ y ∈ C₀ :=
      ⟨fun h => (mem_inter.mp h).2, fun h => mem_inter.mpr ⟨hy, h⟩⟩
    exact ((vertical_degree_zero_three hr pc y).1 hy).trans (if_congr hm.symm rfl rfl)
  have dB : ∀ x ∈ B, degree B x = if x ∈ F then 1 else 3 := by
    apply encoded_degree_profile (hs := pc.three)
    intro y hy
    have hm : y ∈ F₀ ↔ y ∈ C₀ := by
      rw [shared]
      exact ⟨fun h => (mem_inter.mp h).2, fun h => mem_inter.mpr ⟨hy, h⟩⟩
    exact ((vertical_degree_zero_three hr pc y).2 hy).trans (if_congr hm.symm rfl rfl)
  have dC : ∀ x ∈ C, degree C x = if x ∈ F then 1 else 3 := by
    apply encoded_degree_profile (hs := rfl)
    intro y hy
    have hm : y ∈ F₀ ↔ y ∈ A₀ :=
      ⟨fun h => (mem_inter.mp h).1, fun h => mem_inter.mpr ⟨h, hy⟩⟩
    exact (equal_middle_intersections hr pc y hy).2.trans (if_congr hm.symm rfl rfl)
  have rows := suffix_equations form hrow
  have pA : ∀ x, decide (x ∈ A) = neighborParity A x := by
    apply parity_of_column hunit hzero (fun y => column z 13 y + column z 14 y)
    intro y
    have h := (rows y).1
    omega
  have pB : ∀ x, decide (x ∈ B) = neighborParity B x := by
    apply parity_of_column hunit hzero (fun y => column z 14 y - column z 13 y)
    intro y
    have h := (rows y).2.2.2
    omega
  have pC : ∀ x, decide (x ∈ C) = neighborParity C x := by
    let a := column z 12
    let b := column z 13
    let c := column z 14
    have hfun : column z 4 = fun y => -(b y + c y) := by
      funext y
      have h : column z 4 y = -b y - c y := form y 4
      rw [h]
      ring
    apply parity_of_column hunit hzero (k := 4) (fun y => a y + 3 * column z 4 y)
    intro y
    rw [hfun, signedRow_neg, signedRow_add]
    obtain ⟨_, hB, hC, _⟩ := rows y
    change signedRow b y = _ at hB
    change signedRow c y = _ at hC
    change -(signedRow b y + signedRow c y) = 3 * -(b y + c y) - 2 * (a y + 3 * -(b y + c y))
    change _ = a y - 3 * b y - column z 15 y at hB
    change _ = a y - 3 * c y + column z 15 y at hC
    omega
  have heq : A.card = B.card := by
    have hp := equal_square_sums (fun y => (rows y).1) (fun y => (rows y).2.2.1)
      (fun y => (rows y).2.2.2) disjoint (fun y => middle_sign hr pc y (form y) hunit hzero hsign)
    rw [sum_column_sq hunit hzero, sum_column_sq hunit hzero] at hp
    exact (encode_card _).trans (by exact_mod_cast hp) |>.trans (encode_card _).symm
  have total : 72 = 2 * A.card + 2 * B.card + 4 * C.card := by
    simpa only [A, B, C, A₀, B₀, C₀, encode_card, hsize] using sum_carriers hproj pc
  have apos := size_constraints hFA (encoded_nonempty hproj (k := 12) (by decide)) h6 pA dA
  have cpos := size_constraints hFC (encoded_nonempty hproj (k := 4) (by decide)) h6 pC dC
  have sizes : (A.card = 8 ∧ B.card = 8 ∧ C.card = 10) ∨
      (A.card = 10 ∧ B.card = 10 ∧ C.card = 8) := by omega
  obtain ⟨a, p, hnorm⟩ : ∃ a : BitVec 5, ∃ p : Equiv.Perm (Fin 5),
      F.image (fun x => x ^^^ a) = leaves.image (permuteBits p) := by
    rcases sizes with h | h
    · obtain ⟨a, _, p, _, _, hn⟩ := normalize_eight_carrier h.1 h6 hFA dA pA
      exact ⟨a, p, hn⟩
    · obtain ⟨a, _, p, _, _, hn⟩ := normalize_eight_carrier h.2.2 h6 hFC dC pC
      exact ⟨a, p, hn⟩
  have hn := normalized_leaves hnorm
  let axis (j : Fin 3) : Fin 5 := ⟨j.val + 2, by omega⟩
  let axes : Fin 3 ↪ Fin 9 := ⟨fun j => (p (axis j)).natAdd 4, by
    intro i j h
    have he := p.injective ((Fin.natAddEmb 4).injective h)
    apply Fin.ext
    have hv := congrArg Fin.val he
    change i.val + 2 = j.val + 2 at hv
    omega⟩
  refine ⟨axes, fun j => !(a.getLsbD (p (axis j)).val), ?_⟩
  intro j
  let i := axis j
  have hi : 2 ≤ i.val := by
    change 2 ≤ j.val + 2
    omega
  have hA := normalized_true_half hFA hn pA dA i hi
  have hB := normalized_true_half hFB hn pB dB i hi
  have hC := normalized_true_half hFC hn pC dC i hi
  have hcut := sum_suffix_half hproj pc (p i) (!(a.getLsbD (p i).val))
  change _ = 2 * suffixHalf A (p i) _ + 2 * suffixHalf B (p i) _ +
    4 * suffixHalf C (p i) _ at hcut
  change (S.filter fun u => u ((p i).natAdd 4) = !(a.getLsbD (p i).val)).card = 20
  rw [hcut]
  rcases sizes with h | h
  · rw [hA.1 h.1, hB.1 h.2.1, hC.2 h.2.2]
  · rw [hA.2 h.1, hB.2 h.2.1, hC.1 h.2.2]

#print axioms tenShadowSharedLeaves_three_halves

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSharedLeaves
