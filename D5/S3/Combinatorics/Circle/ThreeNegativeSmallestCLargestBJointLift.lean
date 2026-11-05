/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeSmallestCLargestBJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Charge-corrected physical joint construction on the full ordered cone c<a<b. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! Exact physical charge allocation for the full cone 2<=c<a<b. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeSmallestCLargestBJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open ThreeNegativeMinimumTwoJointLift

open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.bga Ear Ear.q Plan makePlan Bounded Separate Seams Certificate oldMass newMass cap oldHeight
  newHeight atNegative Order.first Order.middle Order.last
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private realize from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private floor_bounds from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoFloors

private theorem bit_separate (x i : ℕ) (h : x.testBit i = false) :
    Disjoint x.bitIndices.toFinset (2^i).bitIndices.toFinset := by
  simp only [Nat.bitIndices_two_pow, List.toFinset_cons, List.toFinset_nil]
  simp [h]

private theorem adjacent_bits (q : ℤ) (hq : 1 ≤ q) :
    Separate ((Mask.mk (1) (16*q-5) (0)) : Mask) (Mask.mk (4*q-2) (4) (1)) := by
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
  rw [Nat.testBit_two_pow_mul_add x (show 2^d < 2^(d+2) by exact Nat.pow_lt_pow_right (by decide) (by omega)) (d+1)]
  simp only [show d+1<d+2 by omega, ite_true]
  exact Nat.testBit_two_pow_of_ne (by omega)

private theorem adjacent_certificate (q : ℤ) (hq : 1 ≤ q) :
    Certificate (16*q) (32*q) (8*q)
      (makePlan 0 Order.bga Ear.q (Mask.mk (1) (16*q-5) (0)) (Mask.mk (4*q-2) (4) (1))) := by
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
    (hsep : Separate ((Mask.mk (0) (32*q*v-3*v) (0)) : Mask) (Mask.mk (4*q-1) (2*v) (1))) :
    Certificate (16*q) (64*q*v) (8*q)
      (makePlan 1 Order.bga Ear.q (Mask.mk (0) (32*q*v-3*v) (0)) (Mask.mk (4*q-1) (2*v) (1))) := by
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
      (makePlan 2 Order.bga Ear.q (Mask.mk (0) (32*q*v-2*v) (0)) (Mask.mk (4*q-1) (0) (3))) := by
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


private theorem next_bits (q : ℤ) (hq : 1≤q) (d : ℕ) :
    Separate ((Mask.mk (0) (32*q*(2:ℤ)^d-3*(2:ℤ)^d) (0)) : Mask)
      (Mask.mk (4*q-1) (2*(2:ℤ)^d) (1)) := by
  let x := (8*q-1).toNat
  have hx : (x:ℤ)=8*q-1 := Int.toNat_of_nonneg (by omega)
  have he : 32*q*(2:ℤ)^d-3*(2:ℤ)^d =
      ((2^(d+2)*x+2^d : ℕ):ℤ) := by
    push_cast
    rw [hx,pow_add]
    norm_num
    ring
  have hz : 2*(2:ℤ)^d = ((2^(d+1):ℕ):ℤ) := by
    push_cast
    rw [pow_succ]
    ring
  dsimp [Separate]
  refine ⟨by simp, ?_, by simp⟩
  rw [he,hz]
  simpa only [Int.toNat_natCast] using split_bits d x

private theorem seam_criterion (r s t : ℤ) (P T : Mask)
    (hqP : 0≤(Mask.v P)+(s+1)*(Mask.w P)) (hqT : 0≤(Mask.v T)+(s+1)*(Mask.w T))
    (he : oldHeight r s t Negative.beta ≤ oldMass r s t P)
    (hex : oldMass r s t P ≤ cap r s t)
    (hd : 0≤oldHeight r s t Negative.alpha-oldMass r s t T)
    (hA : newHeight r s t Negative.beta ≤ newMass r s t P)
    (hD : 2*(oldHeight r s t Negative.alpha-oldMass r s t T)+(Mask.v T)+(s+1)*(Mask.w T)+1
      ≤ (s+1)*(r/2)) :
    Seams r s t (makePlan 3 Order.bga Ear.q P T) := by
  have hp : newMass r s t P = 2*oldMass r s t P-((Mask.v P)+(s+1)*(Mask.w P)) := by
    dsimp [oldMass,newMass]; ring
  have ht : newMass r s t T = 2*oldMass r s t T-((Mask.v T)+(s+1)*(Mask.w T)) := by
    dsimp [oldMass,newMass]; ring
  have hG : oldHeight r s t Negative.gamma = cap r s t-(s+1)*(r/2) := rfl
  dsimp only [Seams,makePlan,Order.first,Order.middle,Order.last,
    newHeight,atNegative]
  simp only [reduceCtorEq,ite_false,add_zero]
  change oldHeight r s t Negative.beta ≤ oldMass r s t P ∧
    oldMass r s t P ≤ cap r s t ∧
    oldMass r s t T ≤ oldHeight r s t Negative.alpha ∧
    oldHeight r s t Negative.gamma+oldHeight r s t Negative.alpha-oldMass r s t T ≤ cap r s t ∧
    2*oldHeight r s t Negative.beta+(s/2+1) ≤ newMass r s t P ∧
    newMass r s t P ≤ 2*cap r s t+1 ∧
    newMass r s t T ≤ 2*oldHeight r s t Negative.alpha+1 ∧
    (2*oldHeight r s t Negative.gamma+((s+1)*(r/2)+1))+
      (2*oldHeight r s t Negative.alpha+1)-newMass r s t T ≤ 2*cap r s t+1
  change 2*oldHeight r s t Negative.beta+(s/2+1)≤newMass r s t P at hA
  refine ⟨he,hex,by omega,?_,hA,?_,?_,?_⟩ <;> nlinarith only [hp,ht,hG,hqP,hqT,hd,hD,hex]

private theorem far_front (R T v : ℤ) (hT : 4≤T) (hR : 8*T≤R) (hv : 1≤v) :
    let P : Mask := (Mask.mk (0) (2*R*v-2*v) (0))
    Bounded (2*R) (4*R*v) (2*T) P ∧
    oldHeight (2*R) (4*R*v) (2*T) Negative.beta ≤ oldMass (2*R) (4*R*v) (2*T) P ∧
    oldMass (2*R) (4*R*v) (2*T) P ≤ cap (2*R) (4*R*v) (2*T) ∧
    newHeight (2*R) (4*R*v) (2*T) Negative.beta ≤ newMass (2*R) (4*R*v) (2*T) P := by
  have ht : 2*T/2=T := by omega
  have hr : 2*R/2=R := by omega
  have hs : 4*R*v/2=2*R*v := by
    have : 4*R*v=2*(2*R*v) := by ring
    omega
  let T0 := T-4
  let R0 := R-8*T
  let v0 := v-1
  have hT0 : 0≤T0 := by dsimp [T0]; omega
  have hR0 : 0≤R0 := by dsimp [R0]; omega
  have hv0 : 0≤v0 := by dsimp [v0]; omega
  have htE : T=T0+4 := by dsimp [T0]; ring
  have hrE : R=8*T+R0 := by dsimp [R0]; ring
  have hvE : v=v0+1 := by dsimp [v0]; ring
  dsimp [Bounded,oldHeight,newHeight,oldMass,newMass,cap,atNegative]
  simp only [ht,hr,hs]
  rw [hrE,htE,hvE]
  repeat' constructor
  all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | (apply sub_pos.mp; ring_nf; positivity)

set_option maxHeartbeats 800000 in
-- The floor budget combines nonlinear products before cancelling the positive physical scale.
private theorem far_certificate (R T v : ℤ) (hT : 4≤T) (hR : 8*T≤R) (hv : 1≤v) :
    let F := 8*R^2*v-4*R*T+2*R-2*T
    let L := 1+4*R*v+8*R*v*T
    Certificate (2*R) (4*R*v) (2*T)
      (makePlan 3 Order.bga Ear.q (Mask.mk (0) (2*R*v-2*v) (0)) (Mask.mk (T-1) (0) (F/L))) := by
  dsimp only
  let F := 8*R^2*v-4*R*T+2*R-2*T
  let L := 1+4*R*v+8*R*v*T
  let m := F/L
  change Certificate (2*R) (4*R*v) (2*T)
    (makePlan 3 Order.bga Ear.q (Mask.mk (0) (2*R*v-2*v) (0)) (Mask.mk (T-1) (0) (m)))
  have hRp : 0<R := by omega
  have hTp : 0<T := by omega
  have hvp : 0<v := by omega
  have hRv : R≤R*v := by nlinarith [mul_nonneg hRp.le (show 0≤v-1 by omega)]
  have hL : 0<L := by dsimp [L]; positivity
  have hF : 0≤F := by
    dsimp [F]
    nlinarith [mul_nonneg hRp.le (show 0≤4*R*v-2*T by nlinarith)]
  have hFlt : F<8*R^2*v := by
    dsimp [F]
    nlinarith [mul_nonneg hRp.le (show 0≤T-1 by omega)]
  have hfloor := floor_bounds F L hL
  change L*m≤F ∧ F<L*(m+1) at hfloor
  have hm : 0≤m := Int.ediv_nonneg hF hL.le
  have hrem : 0≤F-L*m ∧ F-L*m≤L-1 := by
    constructor <;> nlinarith only [hfloor.1,hfloor.2]
  have hsp : 0<4*R*v := by positivity
  have hsmall : (2*T+1)*m<2*R := by
    have hmul : (4*R*v)*((2*T+1)*m)<(4*R*v)*(2*R) := by
      dsimp [L] at hfloor
      nlinarith only [hfloor.1,hFlt,hm]
    exact lt_of_mul_lt_mul_left hmul hsp.le
  have hmR : m<R := by
    nlinarith [mul_nonneg hm (show 0≤2*T-1 by omega)]
  have hbudget0 : 2*(2*T+1)^2≤R*(2*T-1) := by
    nlinarith [mul_nonneg (show 0≤R-8*T by omega) (show 0≤2*T-1 by omega),
      mul_nonneg (show 0≤T-4 by omega) (show 0≤T+1 by omega)]
  have hbudget : 2*(2*T+1)+m≤R := by
    have hmul : (2*T+1)*(2*(2*T+1)+m)≤(2*T+1)*R := by
      nlinarith only [hsmall.le,hbudget0]
    exact le_of_mul_le_mul_left hmul (by omega : 0<2*T+1)
  have hD : 2*(F-L*m)+(4*R*v+1)*m+1≤(4*R*v+1)*R := by
    have hp := mul_nonneg hsp.le (show 0≤R-(2*(2*T+1)+m) by omega)
    dsimp [L] at hrem
    nlinarith only [hrem.2,hp,show m+1≤R by omega]
  have ht : 2*T/2=T := by omega
  have hr : 2*R/2=R := by omega
  have hs : 4*R*v/2=2*R*v := by
    have : 4*R*v=2*(2*R*v) := by ring
    omega
  obtain ⟨hpB,hpe,hpx,hpA⟩ := far_front R T v hT hR hv
  have hz : oldHeight (2*R) (4*R*v) (2*T) Negative.alpha-
      oldMass (2*R) (4*R*v) (2*T) (Mask.mk (T-1) (0) (m)) = F-L*m := by
    dsimp [oldHeight,oldMass,cap,atNegative,F,L]
    rw [ht]
    ring
  refine ⟨hpB,?_,by simp [Separate,makePlan],?_⟩
  · dsimp [Bounded,makePlan]
    rw [ht,hr,hs]
    exact ⟨by omega,by omega,by omega,by nlinarith,hm,hmR⟩
  · apply seam_criterion
    · dsimp only [Mask.v,Mask.w]
      simp only [mul_zero,add_zero]
      nlinarith [mul_nonneg (show 0≤R-1 by omega) (show 0≤v by omega)]
    · change 0≤0+(4*R*v+1)*m
      positivity
    · exact hpe
    · exact hpx
    · rw [hz]; exact hrem.1
    · exact hpA
    · change 2*(oldHeight (2*R) (4*R*v) (2*T) Negative.alpha-
        oldMass (2*R) (4*R*v) (2*T) (Mask.mk (T-1) (0) (m)))+0+(4*R*v+1)*m+1≤_
      rw [hz,hr]
      simpa only [add_zero] using hD

private theorem factor (x m : ℕ) (hm : m≤x) :
    (2:ℤ)^x=2^m*2^(x-m) := by
  rw [←pow_add]
  congr 1
  omega

/-- A common physical permutation and a literal identity-embedded ear on the complete cone. -/
theorem actualSource_three_negative_smallest_c_largest_b_joint_lift (a b c : ℕ)
    (hc : 2≤c) (hca : c<a) (hab : a<b) :
    ∃ sigma : List (Fin (a+b+c)), ∃ j : ℕ, j≤a+b+c ∧
      OriginalOrder (a+b+c) (1+2^a+2^(a+b)) sigma ∧
      OriginalOrder (a+b+c+1) (2*(1+2^a+2^(a+b)))
        (earWord (a+b+c) sigma j) := by
  have ha : 2≤a := by omega
  have hb : 2≤b := by omega
  by_cases hc2 : c=2
  · exact actualSource_three_negative_minimum_two_joint_lift a b c ha hb hc
      (by omega)
  have hc3 : 3≤c := by omega
  let q : ℤ := 2^(c-3)
  have hq : 1≤q := by dsimp [q]; exact_mod_cast Nat.one_le_two_pow
  have ht : (2:ℤ)^c=8*q := by simpa [q] using factor c 3 hc3
  by_cases hnear : a=c+1
  · have hr : (2:ℤ)^a=16*q := by rw [hnear,pow_succ,ht]; ring
    by_cases hnext : b=a+1
    · have hs : (2:ℤ)^b=32*q := by rw [hnext,pow_succ,hr]; ring
      apply realize a b c ha hb hc (makePlan 0 Order.bga Ear.q (Mask.mk (1) (16*q-5) (0)) (Mask.mk (4*q-2) (4) (1)))
      rw [hr,hs,ht]
      exact adjacent_certificate q hq
    · let d := b-a-2
      let v : ℤ := 2^d
      have hv : 1≤v := by dsimp [v]; exact_mod_cast Nat.one_le_two_pow
      have hs : (2:ℤ)^b=64*q*v := by
        have he : b=a+2+d := by dsimp [d]; omega
        rw [he,pow_add,pow_add,hr]
        dsimp [v]
        norm_num
        ring
      apply realize a b c ha hb hc
        (makePlan 1 Order.bga Ear.q (Mask.mk (0) (32*q*v-3*v) (0)) (Mask.mk (4*q-1) (2*v) (1)))
      rw [hr,hs,ht]
      exact next_certificate q v hq hv (next_bits q hq d)
  · by_cases hfour : a=c+2
    · let d := b-a-1
      let v : ℤ := 2^d
      have hv : 1≤v := by dsimp [v]; exact_mod_cast Nat.one_le_two_pow
      have hr : (2:ℤ)^a=32*q := by rw [hfour,pow_add,ht]; norm_num; ring
      have hs : (2:ℤ)^b=64*q*v := by
        have he : b=a+1+d := by dsimp [d]; omega
        rw [he,pow_add,pow_succ,hr]
        dsimp [v]
        ring
      apply realize a b c ha hb hc
        (makePlan 2 Order.bga Ear.q (Mask.mk (0) (32*q*v-2*v) (0)) (Mask.mk (4*q-1) (0) (3)))
      rw [hr,hs,ht]
      exact four_certificate q v hq hv
    · let R : ℤ := 2^(a-1)
      let T : ℤ := 2^(c-1)
      let v : ℤ := 2^(b-a-1)
      have hR : (2:ℤ)^a=2*R := by simpa [R] using factor a 1 (by omega)
      have hT : (2:ℤ)^c=2*T := by simpa [T] using factor c 1 (by omega)
      have hs : (2:ℤ)^b=4*R*v := by
        have he : b=(a-1)+(b-a-1)+2 := by omega
        rw [he,pow_add,pow_add]
        change (R*v)*(2:ℤ)^2=_
        norm_num
        ring
      have hTb : 4≤T := by
        change (2:ℤ)^2≤2^(c-1)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hRb : 8*T≤R := by
        have he : (2:ℤ)^(c+2)=8*T := by
          dsimp [T]
          have he : c+2=(c-1)+3 := by omega
          rw [he,pow_add]
          norm_num
          ring
        rw [←he]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hv : 1≤v := by dsimp [v]; exact_mod_cast Nat.one_le_two_pow
      let F := 8*R^2*v-4*R*T+2*R-2*T
      let L := 1+4*R*v+8*R*v*T
      apply realize a b c ha hb hc
        (makePlan 3 Order.bga Ear.q (Mask.mk (0) (2*R*v-2*v) (0)) (Mask.mk (T-1) (0) (F/L)))
      rw [hR,hs,hT]
      exact far_certificate R T v hTb hRb hv

#print axioms actualSource_three_negative_smallest_c_largest_b_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeSmallestCLargestBJointLift
