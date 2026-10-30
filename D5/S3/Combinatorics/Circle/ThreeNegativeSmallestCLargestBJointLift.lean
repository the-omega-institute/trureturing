/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Charge-corrected physical joint construction on the full ordered cone c<a<b. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeSmallestCLargestBJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open ThreeNegativeMinimumTwoJointLift

open private Mask Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Ear Plan makePlan Bounded Separate Seams Certificate oldMass newMass cap oldHeight
  newHeight atNegative Order.first Order.middle Order.last
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private realize from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private theorem bit_separate (x i : ℕ) (h : x.testBit i = false) :
    Disjoint x.bitIndices.toFinset (2^i).bitIndices.toFinset := by
  simp only [Nat.bitIndices_two_pow, List.toFinset_cons, List.toFinset_nil,
    Finset.disjoint_singleton_right, List.mem_toFinset, Nat.mem_bitIndices]
  simp [h]

private theorem adjacent_bits (q : ℤ) (hq : 1 ≤ q) :
    Separate (⟨1,16*q-5,0⟩ : Mask) ⟨4*q-2,4,1⟩ := by
  have hx : (((4*q-2).toNat : ℕ) : ℤ) = 4*q-2 := Int.toNat_of_nonneg (by omega)
  have hy : (((16*q-5).toNat : ℕ) : ℤ) = 16*q-5 := Int.toNat_of_nonneg (by omega)
  have hb0 : (4*q-2).toNat.testBit 0 = false := by
    simp only [Nat.testBit_eq_decide_div_mod_eq]; norm_num
    omega
  have hb2 : (16*q-5).toNat.testBit 2 = false := by
    simp only [Nat.testBit_eq_decide_div_mod_eq]; norm_num
    omega
  exact ⟨(bit_separate _ 0 hb0).symm, bit_separate _ 2 hb2, by simp⟩

private theorem split_bits (d : ℕ) (x : ℕ) :
    Disjoint (2^(d+2)*x+2^d).bitIndices.toFinset (2^(d+1)).bitIndices.toFinset := by
  apply bit_separate
  rw [Nat.testBit_two_pow_mul_add x (show 2^d < 2^(d+2) by omega) (d+1)]
  simp only [show d+1<d+2 by omega, ite_true]
  exact Nat.testBit_two_pow_of_ne (by omega)

private theorem adjacent_certificate (q : ℤ) (hq : 1 ≤ q) :
    Certificate (16*q) (32*q) (8*q)
      (makePlan 0 .bga .q ⟨1,16*q-5,0⟩ ⟨4*q-2,4,1⟩) := by
  have hsep := adjacent_bits q hq
  have ht : 8*q/2=4*q := by omega
  have hr : 16*q/2=8*q := by omega
  have hs : 32*q/2=16*q := by omega
  let q0 := q-1
  have hq0 : 0≤q0 := by dsimp [q0]; omega
  have he : q=q0+1 := by dsimp [q0]; ring
  refine ⟨?_,?_,hsep,?_⟩
  · dsimp [Bounded,makePlan]; rw [ht,hr,hs]; omega
  · dsimp [Bounded,makePlan]; rw [ht,hr,hs]; omega
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [ht,hr,hs]
    rw [he]
    repeat' constructor
    all_goals apply sub_nonneg.mp; ring_nf; positivity

private theorem next_certificate (q v : ℤ) (hq : 1≤q) (hv : 1≤v)
    (hsep : Separate (⟨0,32*q*v-3*v,0⟩ : Mask) ⟨4*q-1,2*v,1⟩) :
    Certificate (16*q) (64*q*v) (8*q)
      (makePlan 1 .bga .q ⟨0,32*q*v-3*v,0⟩ ⟨4*q-1,2*v,1⟩) := by
  have ht : 8*q/2=4*q := by omega
  have hr : 16*q/2=8*q := by omega
  have hs : 64*q*v/2=32*q*v := by
    have : 64*q*v=2*(32*q*v) := by ring
    omega
  let q0 := q-1
  let v0 := v-1
  have hq0 : 0≤q0 := by dsimp [q0]; omega
  have hv0 : 0≤v0 := by dsimp [v0]; omega
  have he : q=q0+1 := by dsimp [q0]; ring
  have hf : v=v0+1 := by dsimp [v0]; ring
  refine ⟨?_,?_,hsep,?_⟩
  · dsimp [Bounded,makePlan]; simp only [ht,hr,hs]; rw [he,hf]
    repeat' constructor
    all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | (apply sub_pos.mp; ring_nf; positivity)
  · dsimp [Bounded,makePlan]; simp only [ht,hr,hs]; rw [he,hf]
    repeat' constructor
    all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | (apply sub_pos.mp; ring_nf; positivity)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [ht,hr,hs]
    rw [he,hf]
    repeat' constructor
    all_goals apply sub_nonneg.mp; ring_nf; positivity

private theorem four_certificate (q v : ℤ) (hq : 1≤q) (hv : 1≤v) :
    Certificate (32*q) (64*q*v) (8*q)
      (makePlan 2 .bga .q ⟨0,32*q*v-2*v,0⟩ ⟨4*q-1,0,3⟩) := by
  have ht : 8*q/2=4*q := by omega
  have hr : 32*q/2=16*q := by omega
  have hs : 64*q*v/2=32*q*v := by
    have : 64*q*v=2*(32*q*v) := by ring
    omega
  let q0 := q-1
  let v0 := v-1
  have hq0 : 0≤q0 := by dsimp [q0]; omega
  have hv0 : 0≤v0 := by dsimp [v0]; omega
  have he : q=q0+1 := by dsimp [q0]; ring
  have hf : v=v0+1 := by dsimp [v0]; ring
  refine ⟨?_,?_,by simp [Separate,makePlan],?_⟩
  · dsimp [Bounded,makePlan]; simp only [ht,hr,hs]; rw [he,hf]
    repeat' constructor
    all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | (apply sub_pos.mp; ring_nf; positivity)
  · dsimp [Bounded,makePlan]; simp only [ht,hr,hs]; rw [he,hf]
    repeat' constructor
    all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | (apply sub_pos.mp; ring_nf; positivity)
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [ht,hr,hs]
    rw [he,hf]
    repeat' constructor
    all_goals apply sub_nonneg.mp; ring_nf; positivity

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestCLargestBJointLift
