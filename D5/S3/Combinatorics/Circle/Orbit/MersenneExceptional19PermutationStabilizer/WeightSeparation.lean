/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/WeightSeparation
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: All-r arithmetic separation of the original exceptional19 physical weights. -/
/- Arithmetic proof adapted from the supplied direct-carry candidate, SHA256
99fa9de0158c00f8f4f296949e08bc384480aef20569cf6dcd659995969415b7.
Its consumed lemmas exclude collisions and opposite pairs on all original labels. -/
module
public import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Physical
import all D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace
import all D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer
public import Mathlib.GroupTheory.OrderOfElement

/-! # Arithmetic separation of all physical exceptional19 weights -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
open scoped BigOperators
open SourceWidth ZeroSumSubsets
open MersenneExceptional19Stabilizer
  (degree base seed base_facts Qmask Q_exact centered_parameters modulus_factor)
open private seed_cast
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer.Basic
open private centered_scaled
  from D5.S3.Combinatorics.Circle.Orbit.MersennePhaseThreeTrace

private theorem aa_Q_bezout (r : ℕ) :
    4*(Qmask r : ℤ) - aa r*(2*(base r : ℤ)+5) = 1 := by
  have hq := Q_exact r
  have hc := (parameter_exact r).1
  have he : 19*(4*(Qmask r : ℤ)-aa r*(2*(base r : ℤ)+5)-1)=0 := by
    linear_combination 4*hq-(2*(base r : ℤ)+5)*hc
  nlinarith only [he]

private theorem Q_gt_half_power (r : ℕ) :
    (2 : ℤ)^(3*degree r/2)+1 < (Qmask r : ℤ) := by
  let h : ℕ := 9*r+6
  let x : ℤ := 2^h
  have hx : (64 : ℤ)≤x := by
    change (2 : ℤ)^6≤2^h
    exact pow_le_pow_right₀ (by norm_num) (by dsimp [h]; omega)
  have hb : (base r : ℤ)=x^2 := by
    dsimp [base,x]
    norm_cast
    rw [← pow_mul]
    congr 1
    dsimp [degree,h]
    omega
  have hp : (2 : ℤ)^(3*degree r/2)=x^3 := by
    dsimp [x]
    rw [← pow_mul]
    congr 1
    dsimp [degree,h]
    omega
  have he := Q_exact r
  rw [hb] at he
  have hpos : 0<(x-19)*x^3 := mul_pos (by omega) (by positivity)
  have hx2 : 19≤x^2 := by nlinarith [sq_nonneg (x-64)]
  rw [hp]
  nlinarith only [he,hpos,hx2]

private theorem Q_not_dvd_short_binomial (r a : ℕ)
    (ha : 0<a) (hshort : a≤3*degree r/2) :
    ¬(Qmask r : ℤ) ∣ (2 : ℤ)^a-1 ∧ ¬(Qmask r : ℤ) ∣ (2 : ℤ)^a+1 := by
  have h2 : (2 : ℤ)≤2^a := by
    calc
      (2 : ℤ)=2^1 := by norm_num
      _≤2^a := pow_le_pow_right₀ (by norm_num) ha
  have hp : (2 : ℤ)^a≤2^(3*degree r/2) :=
    pow_le_pow_right₀ (by norm_num) hshort
  have hQ := Q_gt_half_power r
  constructor
  · intro h
    have hle := Int.le_of_dvd (show 0<(2 : ℤ)^a-1 by omega) h
    omega
  · intro h
    have hle := Int.le_of_dvd (show 0<(2 : ℤ)^a+1 by positivity) h
    omega

private theorem Q_positive_odd (r : ℕ) : 0<(Qmask r : ℤ) ∧ (Qmask r : ℤ)%2=1 := by
  have hsize := Q_gt_half_power r
  have hB : (base r : ℤ)%2=0 := by exact_mod_cast (base_facts r).2.2
  have hB2 : ((base r : ℤ)^2)%2=0 := by
    rw [pow_two,Int.mul_emod,hB]
    norm_num
  have he := Q_exact r
  have hp : (0 : ℤ)≤2^(3*degree r/2) := by positivity
  exact ⟨by omega,by omega⟩

private theorem two_period_mod_Q (r : ℕ) :
    (2 : ZMod (Qmask r))^(3*degree r)=1 := by
  have hfac : (2 : ℤ)^(3*degree r)-1 =
      (Qmask r : ℤ)*(19*((base r : ℤ)-1)) := by
    change modulus (3*degree r) = _
    rw [modulus_factor,← Q_exact]
    ring
  have hdvd : (Qmask r : ℤ) ∣ (2 : ℤ)^(3*degree r)-1 :=
    ⟨19*((base r : ℤ)-1),hfac⟩
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
    ((2 : ℤ)^(3*degree r)-1) (Qmask r)).mpr hdvd
  have hz' : (2 : ZMod (Qmask r))^(3*degree r)-1=0 := by
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_one] using hz
  exact sub_eq_zero.mp hz'

private theorem two_finite_order (r : ℕ) : IsOfFinOrder (2 : ZMod (Qmask r)) :=
  isOfFinOrder_iff_pow_eq_one.mpr
    ⟨3*degree r,by dsimp [degree]; omega,two_period_mod_Q r⟩

private theorem two_order_mod_Q (r : ℕ) :
    orderOf (2 : ZMod (Qmask r))=3*degree r := by
  let h := orderOf (2 : ZMod (Qmask r))
  have hh : 0<h := (two_finite_order r).orderOf_pos
  have hdvd : h ∣ 3*degree r := orderOf_dvd_of_pow_eq_one (two_period_mod_Q r)
  have hle : h≤3*degree r := orderOf_le_of_pow_eq_one
    (by dsimp [degree]; omega) (two_period_mod_Q r)
  by_contra hne
  have hlt : h<3*degree r := by dsimp [h] at *; omega
  obtain ⟨k,hk⟩ := hdvd
  have hk2 : 2≤k := by
    by_contra hsmall
    have hk01 : k=0 ∨ k=1 := by omega
    rcases hk01 with rfl | rfl <;> simp_all
  have htwice : 2*h≤3*degree r := by nlinarith only [hk,hh,hk2]
  have hshort : h≤3*degree r/2 := by omega
  have hpow : (2 : ZMod (Qmask r))^h=1 := pow_orderOf_eq_one _
  have hdiv : (Qmask r : ℤ) ∣ (2 : ℤ)^h-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_one,hpow,sub_self]
  exact (Q_not_dvd_short_binomial r h hh hshort).1 hdiv

private theorem two_power_ne_neg_one (r a : ℕ) (ha : a<3*degree r) :
    (2 : ZMod (Qmask r))^a ≠ -1 := by
  intro h
  have hsquare : (2 : ZMod (Qmask r))^(2*a)=1 := by
    rw [show 2*a=a*2 by omega,pow_mul,h]
    norm_num
  have hdvd : 3*degree r ∣ 2*a := by
    rw [← two_order_mod_Q r]
    exact orderOf_dvd_of_pow_eq_one hsquare
  obtain ⟨k,hk⟩ := hdvd
  have hn : 0<3*degree r := by dsimp [degree]; omega
  have hk1 : k≤1 := by nlinarith only [hk,ha,hn]
  have hshort : a≤3*degree r/2 := by
    have hk01 : k=0 ∨ k=1 := by omega
    rcases hk01 with rfl | rfl <;> simp_all <;> omega
  have hdiv : (Qmask r : ℤ) ∣ (2 : ℤ)^a+1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_add,Int.cast_pow,Int.cast_ofNat,Int.cast_one,h,neg_add_cancel]
  have hbound : (2 : ℤ)^a≤2^(3*degree r/2) :=
    pow_le_pow_right₀ (by norm_num) hshort
  have hle := Int.le_of_dvd (show 0<(2 : ℤ)^a+1 by positivity) hdiv
  have hsize := Q_gt_half_power r
  omega

private theorem two_powers_not_opposite (r a b : ℕ)
    (ha : a<3*degree r) (hb : b<3*degree r) :
    (2 : ZMod (Qmask r))^a ≠ -(2 : ZMod (Qmask r))^b := by
  have aux (s t : ℕ) (hs : s<3*degree r) (hts : t≤s) :
      (2 : ZMod (Qmask r))^s ≠ -(2 : ZMod (Qmask r))^t := by
    intro he
    have hp : (2 : ZMod (Qmask r))^t * 2^(s-t) =
        (2 : ZMod (Qmask r))^t * (-1) := by
      rw [← pow_add,Nat.add_sub_of_le hts]
      simpa only [mul_neg_one] using he
    have hneg := ((two_finite_order r).isUnit.pow t).mul_right_inj.mp hp
    exact two_power_ne_neg_one r (s-t) (by omega) hneg
  intro he
  rcases le_total b a with hba | hab
  · exact aux a b ha hba he
  · apply aux b a hb hab
    simpa only [neg_neg] using (congrArg Neg.neg he).symm

private theorem source_full_scale (r : ℕ) (i : Fin (3*degree r)) :
    actualSource (3*degree r) (seed r) i =
      (19*((base r : ℤ)-1))*centered (Qmask r) (aa r*2^i.val) := by
  let g : ℤ := 19*((base r : ℤ)-1)
  let q : ℤ := Qmask r
  let z : ℤ := aa r*2^i.val
  have hg : 0<g := by
    have hB : (4096 : ℤ)≤base r := by exact_mod_cast (base_facts r).1
    dsimp [g]
    omega
  have hq : 0<q := (Q_positive_odd r).1
  have hqodd : q%2=1 := (Q_positive_odd r).2
  have hN : modulus (3*degree r)=g*q := by
    dsimp [g,q]
    rw [modulus_factor,← Q_exact]
    ring
  have hodd : (g*q)%2=1 := by rw [← hN,modulus_factor]; exact (centered_parameters r).2.2
  have ht : (seed r : ℤ)=g*aa r := by
    rw [seed_cast]
    dsimp [g]
    rw [show 19*((base r : ℤ)-1)*aa r=((base r : ℤ)-1)*(19*aa r) by ring,
      (parameter_exact r).1]
  have hb := centered_bounds hq hqodd z
  have hhalf := Int.emod_add_mul_ediv q 2
  have hr : -q<2*centered q z ∧ 2*centered q z<q := by omega
  have hz : z=centered q z+q*((z+q/2)/q) := by
    have he := Int.emod_add_mul_ediv (z+q/2) q
    dsimp [centered]
    omega
  have hs := centered_scaled hg hq hodd hz hr
  change centered (modulus (3*degree r)) (2^i.val*(seed r : ℤ)) = _
  rw [hN,ht,show (2 : ℤ)^i.val*(g*aa r)=g*z by dsimp [z]; ring]
  exact hs

private theorem centered_cast_Q (r : ℕ) (z : ℤ) :
    ((centered (Qmask r) z : ℤ) : ZMod (Qmask r)) = (z : ZMod (Qmask r)) :=
  (ZMod.intCast_eq_intCast_iff' _ _ _).mpr (centered_mod _ _)

private theorem aa_unit (r : ℕ) : IsUnit (aa r : ZMod (Qmask r)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨((-(2*(base r : ℤ)+5) : ℤ) : ZMod (Qmask r)),?_⟩
  have he := congrArg (fun z : ℤ => (z : ZMod (Qmask r))) (aa_Q_bezout r)
  have hq : ((Qmask r : ℤ) : ZMod (Qmask r))=0 := by simp
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_add,Int.cast_one,hq,
    mul_zero,zero_sub] at he
  simpa only [Int.cast_neg,Int.cast_add,Int.cast_mul,Int.cast_ofNat,mul_neg] using he

private theorem actual_weights_injective (r : ℕ) :
    Function.Injective (actualSource (3*degree r) (seed r)) := by
  intro i j he
  rw [source_full_scale,source_full_scale] at he
  have hg : (19*((base r : ℤ)-1))≠0 := by
    have hB : (4096 : ℤ)≤base r := by exact_mod_cast (base_facts r).1
    omega
  have hc := mul_left_cancel₀ hg he
  have hz := congrArg (fun z : ℤ => (z : ZMod (Qmask r))) hc
  simp only [centered_cast_Q,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] at hz
  have hp := (aa_unit r).mul_right_inj.mp hz
  have hm := (two_finite_order r).pow_inj_mod.mp hp
  rw [two_order_mod_Q,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at hm
  exact Fin.ext hm

private theorem actual_weights_no_negative_pair (r : ℕ) (i j : Fin (3*degree r)) :
    actualSource (3*degree r) (seed r) i ≠ -actualSource (3*degree r) (seed r) j := by
  intro he
  rw [source_full_scale,source_full_scale,← mul_neg] at he
  have hg : (19*((base r : ℤ)-1))≠0 := by
    have hB : (4096 : ℤ)≤base r := by exact_mod_cast (base_facts r).1
    omega
  have hc := mul_left_cancel₀ hg he
  have hz := congrArg (fun z : ℤ => (z : ZMod (Qmask r))) hc
  simp only [Int.cast_neg,centered_cast_Q,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] at hz
  rw [← mul_neg] at hz
  have hp := (aa_unit r).mul_right_inj.mp hz
  exact two_powers_not_opposite r i.val j.val i.isLt j.isLt hp

end D5.S3.Combinatorics.Circle.MersenneExceptional19PermutationStabilizer
