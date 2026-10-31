/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryWords
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-physical-boundary-words)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical occurrence words for the entire max-plus-one layer. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryAlgebra

/-! Uncompiled preparation source. Labels, rather than source values, are moved.
The ANDs only express physical intersections. On each intended dyadic chamber
the smaller mask is contained in the larger one; proving those equalities is
part of the remaining allocation-to-mass bridge, not an extra hypothesis of
the intended endpoint. All helpers here are private. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private masked_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks

-- The existing occurrence decoder and four-chain inventory theorem are reused.
private def uvWord (a b c d u r p q w : ℕ) : List ℕ :=
  chamberMaskedWord a b c d u (u &&& r) 0 0 p (p &&& q) w

private theorem uv_inventory (a b c d u r p q w : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    (uvWord a b c d u r p q w).Perm (List.range (a+b+c+d)) := by
  apply masked_inventory a b c d u (u &&& r) 0 0 p (p &&& q) w ha hb hc hd
  · intro e _ he
    rw [Nat.testBit_and, Bool.and_eq_true] at he
    exact he.1
  · intro e _ he
    simp at he
  · intro e he _
    simp [Nat.testBit_two_pow_sub_one, he]
  · intro e _ he
    simpa using he
  · intro e _ he
    rw [Nat.testBit_and, Bool.and_eq_true] at he
    exact he.1
  · simp

private def weakPeakWord (a b c : ℕ) : List ℕ :=
  let d := b+1
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let B := 2*y*(x*y+x+1)+1
  let L := 2*y*z*(x+1)+z+1
  let M := 2*y*y*z+y*z+y+1
  let n := if a=b ∧ b=c then 1 else 2*((B-1)/(2*A)).toNat
  let r := if a<c then 1 else 0
  let w := if a=b then 0 else if b=a+1 then 1
    else ((M+1-2*A+2*L-1)/(2*L)).toNat
  uvWord a b c d (n-1) r 0 0 w

private def strictFirstWord (a b c : ℕ) : List ℕ :=
  let d := a+1
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let A := x*y*z+x*y+x+1
  let B := 2*x*(x*y+x+1)+1
  if b<c then
    let n := 2*((B-1)/(2*A)).toNat
    uvWord a b c d (n-1) 0 (2^(c-b-1)) 0 0
  else
    let h : ℕ := 2^(a-b)
    let n := h*((B-1)/((h:ℤ)*A)).toNat
    uvWord a b c d (n-1) (h-1) 0 0 0

private def tiedOuterWord (a b : ℕ) : List ℕ :=
  -- In the dispatcher this is used only when b<a; the equal face is weakPeak.
  uvWord a b a (a+1) 1 1 (2^(a-b-1)-1) 0 0

private def strictRisingWord (a b c : ℕ) : List ℕ :=
  uvWord a b c (c+1) 1 0 (2^(c-b)-1) 0 (2^(b-a-1))

private def swappedRisingWord (a b c : ℕ) : List ℕ :=
  uvWord a b c (c+1) 1 1 (2^(c-b-1)-1) (2^(c-a-1)) 0

-- This chamber changes the negative order to U,W,V,X. In particular it is
-- not obtained from strictRisingWord by interchanging numerical parameters.
private def equalFirstWord (u c : ℕ) : List ℕ :=
  let d := c+1
  let p := if 2*u ≤ c then 2^(c-2*u) else 0
  let q := 2^(c-u-1)
  let P := maskedBlocks u u c d 1 1 0 0 (p ||| q) q 0
  P.first ++ [d-1] ++ P.third ++ [d+c+u-1] ++
    P.second ++ [d+c-1] ++ P.fourth ++ [d+c+u+u-1]

private theorem equal_first_inventory (u c : ℕ) (hu : 2 ≤ u) (hc : 2 ≤ c) :
    (equalFirstWord u c).Perm (List.range (u+u+c+(c+1))) := by
  let d := c+1
  let p := if 2*u ≤ c then 2^(c-2*u) else 0
  let q := 2^(c-u-1)
  let P := maskedBlocks u u c d 1 1 0 0 (p ||| q) q 0
  have hbase := masked_inventory u u c d 1 1 0 0 (p ||| q) q 0
    (by omega) (by omega) (by omega) (by dsimp [d]; omega)
    (by intro e _ he; exact he)
    (by intro e _ he; simp at he)
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    (by intro e _ he; simpa using he)
    (by intro e _ he; simp [Nat.testBit_or,he])
    (by simp)
  change (P.word u u c d).Perm (List.range (u+u+c+d)) at hbase
  change (P.first ++ [d-1] ++ P.third ++ [d+c+u-1] ++
    P.second ++ [d+c-1] ++ P.fourth ++ [d+c+u+u-1]).Perm _
  apply List.Perm.trans ?_ hbase
  apply Multiset.coe_eq_coe.mp
  simp only [Blocks.word, ←Multiset.coe_add]
  ac_rfl

-- The actual domain partition covers equality faces explicitly.
private def boundaryWord (a b c : ℕ) : List ℕ :=
  if a ≤ b ∧ c ≤ b then weakPeakWord a b c
  else if b<a ∧ c<a then strictFirstWord a b c
  else if a=c then tiedOuterWord a b
  else if a=b then equalFirstWord a c
  else if a<b then strictRisingWord a b c
  else swappedRisingWord a b c

set_option maxHeartbeats 1400000 in
private theorem boundary_inventory (a b c : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    (boundaryWord a b c).Perm
      (List.range (a+b+c+(max (max a b) c+1))) := by
  by_cases hp : a≤b ∧ c≤b
  · have hm : max (max a b) c=b := by
      rw [max_eq_right hp.1, max_eq_left hp.2]
    simp only [boundaryWord, if_pos hp, hm]
    dsimp only [weakPeakWord]
    apply uv_inventory <;> omega
  · by_cases hf : b<a ∧ c<a
    · have hm : max (max a b) c=a := by
        rw [max_eq_left hf.1.le, max_eq_left hf.2.le]
      simp only [boundaryWord, if_neg hp, if_pos hf, hm]
      dsimp only [strictFirstWord]
      split_ifs <;> apply uv_inventory <;> omega
    · by_cases he : a=c
      · have hba : b<a := by omega
        have hm : max (max a b) c=a := by
          rw [max_eq_left hba.le, ←he, max_self]
        simp only [boundaryWord, if_neg hp, if_neg hf, if_pos he, hm]
        subst c
        exact uv_inventory a b a (a+1) 1 1 (2^(a-b-1)-1) 0 0
          (by omega) (by omega) (by omega) (by omega)
      · have hac : a<c := by omega
        have hbc : b<c := by omega
        have hm : max (max a b) c=c := by
          exact max_eq_right (max_le hac.le hbc.le)
        by_cases hab : a=b
        · simp only [boundaryWord, if_neg hp, if_neg hf, if_neg he,
            if_pos hab, hm]
          subst b
          exact equal_first_inventory a c ha hc
        · by_cases hlt : a<b
          · simp only [boundaryWord, if_neg hp, if_neg hf, if_neg he,
              if_neg hab, if_pos hlt, hm, strictRisingWord]
            apply uv_inventory <;> omega
          · simp only [boundaryWord, if_neg hp, if_neg hf, if_neg he,
              if_neg hab, if_neg hlt, hm, swappedRisingWord]
            apply uv_inventory <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
