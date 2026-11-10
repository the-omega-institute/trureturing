/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestALargestBJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestALargestBJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical joint construction in the strict smallest-first largest-second cone. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! One literal ear and one physical order throughout the cone `2 ≤ a < c < b`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeSmallestALargestBJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport

open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.bga Order.first Order.middle Order.last Ear Ear.p Ear.q Ear.t
  Plan Plan.p Plan.t Plan.order Plan.ear makePlan Bounded Separate Seams Certificate
  oldMass newMass cap oldHeight newHeight atNegative disjoint_low_bits
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private ThreeNegativeMinimumTwoJointLift.realize
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

private theorem half_double (x : ℤ) : (2*x)/2=x := by omega

private def farPlan (h z d : ℤ) : Plan :=
  makePlan 0 Order.bga Ear.q (Mask.mk 0 (4*z*d*(2*h-1)) 0)
    (Mask.mk (2*h*z-1) (3*d-1) 0)

private def nextPlan (h z : ℤ) (upper : Bool) : Plan :=
  makePlan 1 Order.bga Ear.q
    (if upper then Mask.mk 0 (2*z) (h-1) else Mask.mk z 0 (h-1))
    (Mask.mk (2*h*z-h) (2*h-2) 0)

private theorem far_arithmetic (h z d : ℤ) (hh : 2≤h) (hz : 1≤z) (hd : 1≤d) :
    Bounded (2*h) (16*h*z*d) (4*h*z) (Plan.p (farPlan h z d)) ∧
    Bounded (2*h) (16*h*z*d) (4*h*z) (Plan.t (farPlan h z d)) ∧
    Seams (2*h) (16*h*z*d) (4*h*z) (farPlan h z d) := by
  have hr : (2*h)/2=h := half_double h
  have hs : (16*h*z*d)/2=8*h*z*d := by
    rw [show 16*h*z*d=2*(8*h*z*d) by ring, half_double]
  have ht : (4*h*z)/2=2*h*z := by
    rw [show 4*h*z=2*(2*h*z) by ring, half_double]
  dsimp [Bounded,Seams,farPlan,makePlan,oldMass,newMass,oldHeight,newHeight,
    cap,Order.first,Order.middle,Order.last,atNegative]
  rw [hr,hs,ht]
  have hh0 : 0≤h-2 := by omega
  have hz0 : 0≤z-1 := by omega
  have hd0 : 0≤d-1 := by omega
  generalize hH : h-2 = H at hh0
  generalize hZ : z-1 = Z at hz0
  generalize hD : d-1 = D at hd0
  have he : h=H+2 := by omega
  have ze : z=Z+1 := by omega
  have de : d=D+1 := by omega
  rw [he,ze,de]
  repeat' constructor
  all_goals first
    | (apply sub_nonneg.mp; ring_nf; positivity)
    | (apply sub_pos.mp; ring_nf; positivity)


private theorem next_arithmetic (h z : ℤ) (hh : 2≤h) (hz : 1≤z) (upper : Bool) :
    Bounded (2*h) (8*h*z) (4*h*z) (Plan.p (nextPlan h z upper)) ∧
    Bounded (2*h) (8*h*z) (4*h*z) (Plan.t (nextPlan h z upper)) ∧
    Seams (2*h) (8*h*z) (4*h*z) (nextPlan h z upper) := by
  have hr : (2*h)/2=h := half_double h
  have hs : (8*h*z)/2=4*h*z := by
    rw [show 8*h*z=2*(4*h*z) by ring, half_double]
  have ht : (4*h*z)/2=2*h*z := by
    rw [show 4*h*z=2*(2*h*z) by ring, half_double]
  have hh0 : 0≤h-2 := by omega
  have hz0 : 0≤z-1 := by omega
  generalize hH : h-2 = H at hh0
  generalize hZ : z-1 = Z at hz0
  have he : h=H+2 := by omega
  have ze : z=Z+1 := by omega
  cases upper <;>
    dsimp [Bounded,Seams,nextPlan,makePlan,oldMass,newMass,oldHeight,newHeight,
      cap,Order.first,Order.middle,Order.last,atNegative] <;>
    rw [hr,hs,ht,he,ze]
  all_goals repeat' constructor
  all_goals first
    | (apply sub_nonneg.mp; ring_nf; positivity)
    | (apply sub_pos.mp; ring_nf; positivity)


private theorem high_low_bits (e : ℕ) (x y : ℤ)
    (hx : 0≤x) (hy : 0≤y) (hbound : x < (2:ℤ)^e) :
    Disjoint (((2:ℤ)^e*y).toNat.bitIndices.toFinset) x.toNat.bitIndices.toFinset := by
  have hxn : (x.toNat:ℤ)=x := Int.toNat_of_nonneg hx
  have hbn : x.toNat < 2^e := by exact_mod_cast (show (x.toNat:ℤ)<(2:ℤ)^e by omega)
  rw [Int.toNat_mul (by positivity) hy,Int.toNat_pow_of_nonneg (by norm_num)]
  exact (disjoint_low_bits e x.toNat y.toNat hbn).symm

private theorem far_separate (a b c : ℕ) (ha : 2≤a) (hac : a<c) (hcb : c+2≤b) :
    let h : ℤ := 2^(a-1)
    let z : ℤ := 2^(c-a-1)
    let d : ℤ := 2^(b-c-2)
    Separate (Plan.p (farPlan h z d)) (Plan.t (farPlan h z d)) := by
  dsimp only
  let h : ℤ := 2^(a-1)
  let z : ℤ := 2^(c-a-1)
  let d : ℤ := 2^(b-c-2)
  have hh : 2≤h := by
    dsimp [h]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 1≤a-1))
  have hz : 1≤z := by dsimp [z]; exact_mod_cast Nat.one_le_two_pow
  have hd : 1≤d := by dsimp [d]; exact_mod_cast Nat.one_le_two_pow
  have hscale : 4*z*d=(2:ℤ)^(b-a-1) := by
    dsimp [z,d]
    rw [show (4:ℤ)=2^2 by norm_num,←pow_add,←pow_add]
    congr 1
    omega
  change Separate (Plan.p (farPlan h z d)) (Plan.t (farPlan h z d))
  dsimp [Separate,farPlan,makePlan]
  refine ⟨by simp,?_,by simp⟩
  rw [hscale]
  apply high_low_bits (b-a-1) (3*d-1) (2*h-1) (by omega) (by omega)
  rw [←hscale]
  have hzmul : 0≤(z-1)*d := mul_nonneg (by omega) (by omega)
  nlinarith only [hzmul,hd]

private theorem next_separate_low (a c : ℕ) (ha : 2≤a) (hac : a<c) (hca : c<2*a) :
    let h : ℤ := 2^(a-1)
    let z : ℤ := 2^(c-a-1)
    Separate (Plan.p (nextPlan h z false)) (Plan.t (nextPlan h z false)) := by
  dsimp only
  let h : ℤ := 2^(a-1)
  let z : ℤ := 2^(c-a-1)
  have hz : 1≤z := by dsimp [z]; exact_mod_cast Nat.one_le_two_pow
  have hzh : z<h := by
    dsimp [z,h]
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) (by omega : c-a-1<a-1))
  change Separate (Plan.p (nextPlan h z false)) (Plan.t (nextPlan h z false))
  dsimp [Separate,nextPlan,makePlan]
  refine ⟨?_,by simp,by simp⟩
  rw [show 2*h*z-h=h*(2*z-1) by ring]
  exact (high_low_bits (a-1) z (2*z-1) (by omega) (by omega) hzh).symm

private theorem next_separate_high (a c : ℕ) (ha : 2≤a) (hac : a<c) (hca : 2*a≤c) :
    let h : ℤ := 2^(a-1)
    let z : ℤ := 2^(c-a-1)
    Separate (Plan.p (nextPlan h z true)) (Plan.t (nextPlan h z true)) := by
  dsimp only
  let h : ℤ := 2^(a-1)
  let z : ℤ := 2^(c-a-1)
  have hh : 2≤h := by
    dsimp [h]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 1≤a-1))
  have hscale : 2*z=(2:ℤ)^(c-a) := by
    dsimp [z]
    rw [←pow_succ']
    congr 1
    omega
  have hr : 2*h=(2:ℤ)^a := by
    dsimp [h]
    rw [←pow_succ']
    congr 1
    omega
  have hlarge : (2:ℤ)^a ≤ 2^(c-a) := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : a≤c-a))
  change Separate (Plan.p (nextPlan h z true)) (Plan.t (nextPlan h z true))
  dsimp [Separate,nextPlan,makePlan]
  refine ⟨by simp,?_,by simp⟩
  rw [hscale]
  simpa only [mul_one] using high_low_bits (c-a) (2*h-2) 1 (by omega) (by norm_num)
    (by rw [hr]; omega)

/-- One physical permutation and one literal fresh-label insertion throughout `2 ≤ a < c < b`. -/
theorem actualSource_three_negative_smallest_a_largest_b_joint_lift
    (a b c : ℕ) (ha : 2≤a) (hac : a<c) (hcb : c<b) :
    ∃ sigma : List (Fin (a+b+c)), ∃ j : ℕ, j≤a+b+c ∧
      OriginalOrder (a+b+c) (1+2^a+2^(a+b)) sigma ∧
      OriginalOrder (a+b+c+1) (2*(1+2^a+2^(a+b))) (earWord (a+b+c) sigma j) := by
  let h : ℤ := 2^(a-1)
  let z : ℤ := 2^(c-a-1)
  have hh : 2≤h := by
    dsimp [h]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 1≤a-1))
  have hz : 1≤z := by dsimp [z]; exact_mod_cast Nat.one_le_two_pow
  have hr : (2:ℤ)^a=2*h := by
    dsimp [h]
    rw [←pow_succ']
    congr 1
    omega
  have ht : (2:ℤ)^c=4*h*z := by
    dsimp [h,z]
    rw [show (4:ℤ)=2^2 by norm_num,←pow_add,←pow_add]
    congr 1
    omega
  by_cases hnext : b=c+1
  · have hs : (2:ℤ)^b=8*h*z := by rw [hnext,pow_succ,ht]; ring
    by_cases hhigh : 2*a≤c
    · have hspt := next_separate_high a c ha hac hhigh
      change Separate (Plan.p (nextPlan h z true)) (Plan.t (nextPlan h z true)) at hspt
      obtain ⟨hp,hT,hseams⟩ := next_arithmetic h z hh hz true
      apply ThreeNegativeMinimumTwoJointLift.realize a b c ha (by omega) (by omega)
        (nextPlan h z true)
      rw [hr,hs,ht]
      exact ⟨hp,hT,hspt,hseams⟩
    · have hspt := next_separate_low a c ha hac (by omega)
      change Separate (Plan.p (nextPlan h z false)) (Plan.t (nextPlan h z false)) at hspt
      obtain ⟨hp,hT,hseams⟩ := next_arithmetic h z hh hz false
      apply ThreeNegativeMinimumTwoJointLift.realize a b c ha (by omega) (by omega)
        (nextPlan h z false)
      rw [hr,hs,ht]
      exact ⟨hp,hT,hspt,hseams⟩
  · let d : ℤ := 2^(b-c-2)
    have hd : 1≤d := by dsimp [d]; exact_mod_cast Nat.one_le_two_pow
    have hs : (2:ℤ)^b=16*h*z*d := by
      dsimp [h,z,d]
      rw [show (16:ℤ)=2^4 by norm_num,←pow_add,←pow_add,←pow_add]
      congr 1
      omega
    have hspt := far_separate a b c ha hac (by omega)
    change Separate (Plan.p (farPlan h z d)) (Plan.t (farPlan h z d)) at hspt
    obtain ⟨hp,hT,hseams⟩ := far_arithmetic h z d hh hz hd
    apply ThreeNegativeMinimumTwoJointLift.realize a b c ha (by omega) (by omega)
      (farPlan h z d)
    rw [hr,hs,ht]
    exact ⟨hp,hT,hspt,hseams⟩

#print axioms actualSource_three_negative_smallest_a_largest_b_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestALargestBJointLift
