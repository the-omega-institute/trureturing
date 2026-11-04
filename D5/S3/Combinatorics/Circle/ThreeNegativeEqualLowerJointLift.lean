/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualLowerJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualLowerJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Two complete physical mask constructions for every equal lower gap. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! Two exhaustive dyadic physical-mask constructions for the equal lower gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualLowerJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open ThreeNegativeMinimumTwoJointLift

open private Mask Mask.mk Mask.u Mask.v Mask.w Negative Negative.alpha Negative.beta Negative.gamma
  Order Order.bga Order.agb Ear Ear.p Ear.q Ear.t Plan Plan.p Plan.t Plan.order Plan.ear
  Order.first Order.middle Order.last atNegative oldMass newMass cap oldHeight newHeight
  makePlan Bounded Separate Seams Certificate disjoint_low_bits
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoMasks
open private realize
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

private theorem near_certificate (m h : ℤ) (hm : 4 ≤ m) (hh : 2 ≤ h) (hhm : h ≤ m) :
    Certificate (2*h*m) (2*m) (2*m)
      (makePlan 0 Order.bga Ear.q (Mask.mk 0 (m-1) (h-1)) (Mask.mk (m-1) 0 0)) := by
  have hs : 2*m/2=m := by omega
  have hr : 2*h*m/2=h*m := by rw [mul_assoc]; omega
  have hm4 : 0 ≤ m-4 := by omega
  have hh2 : 0 ≤ h-2 := by omega
  have hmh : 0 ≤ m-h := by omega
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs,hr]
    have : h ≤ h*m := by nlinarith
    omega
  · dsimp [Bounded,makePlan]; rw [hs,hr]
    have : 0 < h*m := by positivity
    omega
  · simp [Separate,makePlan]
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hs,hr]
    simp only [reduceCtorEq, ite_false, add_zero, zero_mul, mul_zero, zero_add, mul_one, one_mul]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 2*(m-4)*(h-2)+2*(m-4)+9*(h-2)+9 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 2*(m-h)^2+2*(m-h)*(h-2)+7*(m-h)+2*(h-2)+5 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 2*(m-4)*(h-2)+2*(m-4)+8*(h-2)+8 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 2*(m-4)^2*(h-2)+4*(m-4)^2+15*(m-4)*(h-2)+32*(m-4)+28*(h-2)+64 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 2*(m-4)*(h-2)+9*(h-2)+1 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-h)^2+6*(m-h)*(h-2)+17*(m-h)+2*(h-2)^2+12*(h-2)+17 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-4)*(h-2)+4*(m-4)+16*(h-2)+17 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 2*(m-4)^2*(h-2)+4*(m-4)^2+13*(m-4)*(h-2)+30*(m-4)+20*(h-2)+55 by positivity) using 1 <;> ring

private theorem far_certificate (e d : ℕ) (he : 2 ≤ e)
    (hmd : (2 : ℤ)^e ≤ 2^d) :
    let m : ℤ := 2^e
    let H : ℤ := 2^d
    Certificate (4*H*m) (2*m) (2*m)
      (makePlan 1 Order.agb Ear.q (Mask.mk 1 (m-2) (H-1)) (Mask.mk (m-2) 1 H)) := by
  dsimp only
  let m : ℤ := 2^e
  let H : ℤ := 2^d
  change Certificate (4*H*m) (2*m) (2*m)
    (makePlan 1 Order.agb Ear.q (Mask.mk 1 (m-2) (H-1)) (Mask.mk (m-2) 1 H))
  have hm : 4 ≤ m := by
    simpa [m] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he
  have hH : m ≤ H := hmd
  have hs : 2*m/2=m := by omega
  have hr : 4*H*m/2=2*H*m := by
    rw [show 4*H*m=2*(2*H*m) by ring]; omega
  have hm4 : 0 ≤ m-4 := by omega
  have hHm : 0 ≤ H-m := by omega
  have hbits : Disjoint (1 : ℕ).bitIndices.toFinset (m-2).toNat.bitIndices.toFinset := by
    have hp : m=2*(2 : ℤ)^(e-1) := by
      dsimp [m]
      conv_lhs => rw [show e=(e-1)+1 by omega]
      rw [pow_succ]; ring
    have hp0 : (1 : ℤ) ≤ 2^(e-1) := one_le_pow₀ (by norm_num)
    have hn : (m-2).toNat=2*(2^(e-1)-1) := by
      have hc : ((2^(e-1)-1 : ℕ) : ℤ)=(2 : ℤ)^(e-1)-1 := by
        rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; rfl
      have hc' := Int.toNat_of_nonneg (show 0 ≤ m-2 by omega)
      exact_mod_cast (show ((m-2).toNat : ℤ)=2*((2^(e-1)-1 : ℕ) : ℤ) by omega)
    rw [hn]
    simp [Nat.bitIndices_two_mul]
  have hwbits : Disjoint (H-1).toNat.bitIndices.toFinset H.toNat.bitIndices.toFinset := by
    have hHnat : H.toNat=2^d := by
      dsimp [H]; rw [Int.toNat_pow_of_nonneg (by norm_num)]; rfl
    have hh : (H-1).toNat < 2^d := by
      have hc := Int.toNat_of_nonneg (show 0 ≤ H-1 by omega)
      exact_mod_cast (show ((H-1).toNat : ℤ)<(2 : ℤ)^d by change _ < H; omega)
    rw [hHnat]
    simpa only [mul_one] using disjoint_low_bits d (H-1).toNat 1 hh
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [Bounded,makePlan]; rw [hs,hr]
    have : H ≤ 2*H*m := by nlinarith
    omega
  · dsimp [Bounded,makePlan]; rw [hs,hr]
    have : H < 2*H*m := by nlinarith
    omega
  · exact ⟨by simpa [makePlan] using hbits, by simpa [makePlan] using hbits.symm,
      by simpa [makePlan] using hwbits⟩
  · dsimp [Seams,makePlan,oldMass,newMass,oldHeight,newHeight,cap,
      Order.first,Order.middle,Order.last,atNegative]
    simp only [hs,hr]
    simp only [reduceCtorEq, ite_false, add_zero, zero_mul, mul_zero, zero_add, mul_one, one_mul]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-4)^2+6*(m-4)*(H-m)+29*(m-4)+25*(H-m)+51 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-4)^3+4*(m-4)^2*(H-m)+44*(m-4)^2+26*(m-4)*(H-m)+164*(m-4)+39*(H-m)+209 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-4)^2+6*(m-4)*(H-m)+27*(m-4)+23*(H-m)+44 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-4)^3+4*(m-4)^2*(H-m)+46*(m-4)^2+28*(m-4)*(H-m)+181*(m-4)+49*(H-m)+244 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 6*(m-4)^2+10*(m-4)*(H-m)+42*(m-4)+41*(H-m)+72 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 8*(m-4)^3+8*(m-4)^2*(H-m)+90*(m-4)^2+54*(m-4)*(H-m)+344*(m-4)+87*(H-m)+448 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 10*(m-4)^2+14*(m-4)*(H-m)+72*(m-4)+55*(H-m)+130 by positivity) using 1 <;> ring
    · apply sub_nonneg.mp
      convert (show (0 : ℤ) ≤ 4*(m-4)^3+4*(m-4)^2*(H-m)+40*(m-4)^2+20*(m-4)*(H-m)+136*(m-4)+17*(H-m)+158 by positivity) using 1 <;> ring

/-- Every equal lower pair admits one complete physical order and its literal ear. -/
theorem actualSource_three_negative_equal_lower_joint_lift (a b c : ℕ)
    (hb : 2 ≤ b) (hbc : b = c) (hba : b < a) :
    ∃ sigma : List (Fin (a+b+c)), ∃ j : ℕ, j≤a+b+c ∧
      OriginalOrder (a+b+c) (1+2^a+2^(a+b)) sigma ∧
      OriginalOrder (a+b+c+1) (2*(1+2^a+2^(a+b))) (earWord (a+b+c) sigma j) := by
  subst c
  by_cases hb2 : b=2
  · exact actualSource_three_negative_minimum_two_joint_lift a b b (by omega) hb hb
      (by omega)
  have hb3 : 3 ≤ b := by omega
  have hs : (2 : ℤ)^b=2*2^(b-1) := by
    conv_lhs => rw [show b=(b-1)+1 by omega]
    rw [pow_succ]; ring
  by_cases hnear : a ≤ 2*b-1
  · let h : ℤ := 2^(a-b)
    let m : ℤ := 2^(b-1)
    have hm : 4 ≤ m := by
      simpa [m] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show 2 ≤ b-1 by omega)
    have hh : 2 ≤ h := by
      simpa [h] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show 1 ≤ a-b by omega)
    have hhm : h ≤ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have hr : (2 : ℤ)^a=2*h*m := by
      dsimp [h,m]
      calc
        (2 : ℤ)^a=2^((a-b)+(b-1)+1) := by congr 1; omega
        _ = 2*2^(a-b)*2^(b-1) := by rw [pow_succ,pow_add]; ring
    apply realize a b b (by omega) hb hb
      (makePlan 0 Order.bga Ear.q (Mask.mk 0 (m-1) (h-1)) (Mask.mk (m-1) 0 0))
    rw [hr,hs]
    exact near_certificate m h hm hh hhm
  · let H : ℤ := 2^(a-b-1)
    let m : ℤ := 2^(b-1)
    have hmd : (2 : ℤ)^(b-1) ≤ 2^(a-b-1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hr : (2 : ℤ)^a=4*H*m := by
      dsimp [H,m]
      calc
        (2 : ℤ)^a=2^((a-b-1)+(b-1)+2) := by congr 1; omega
        _ = 4*2^(a-b-1)*2^(b-1) := by rw [pow_add,pow_add]; norm_num; ring
    apply realize a b b (by omega) hb hb
      (makePlan 1 Order.agb Ear.q (Mask.mk 1 (m-2) (H-1)) (Mask.mk (m-2) 1 H))
    rw [hr,hs]
    exact far_certificate (b-1) (a-b-1) (by omega) hmd

#print axioms actualSource_three_negative_equal_lower_joint_lift

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualLowerJointLift
