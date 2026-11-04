/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/SelectorMasks
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Unbounded dyadic selectors have genuine sparse containment and full stock bounds. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.BitSupports

/-! Every selected mask is physical; numeric capacity never substitutes for sparse containment. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open private Submask full_submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private shift_submask small_less_submask small_ge_submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.BitSupports

private structure MaskBounds (a c alpha m0 v j0 : ℕ) : Prop where
  alpha_cap : alpha < 2^(a-1)
  m0_cap : m0 < 2^c
  v_cap : v < 2^(c-1)
  nested : Submask j0 m0

private theorem large_masks (a r : ℕ) (ha : 2 ≤ a) (hr : a ≤ r) :
    MaskBounds a (a+r) 0 (2^r-1) (2^(a-2)) (2^(a-1)) := by
  have hp : 1 ≤ 2^r := Nat.one_le_two_pow
  have hq := Nat.two_pow_pos a
  have hq2 : 2^(a-2) < 2^(a+r-1) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  refine ⟨Nat.two_pow_pos _,?_,hq2,?_⟩
  · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show r ≤ a+r by omega)
    omega
  · exact full_submask r _ (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))

private theorem middle_masks (a : ℕ) (ha : 3 ≤ a) :
    MaskBounds a (a+(a-1)) 0 (2^a-2) (2^(a-2)+1) (2^(a-1)+2) := by
  have hq : 2 ≤ 2^(a-2) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ a-2 by omega)
    norm_num at h ⊢
    exact h
  have half : 2^(a-1)=2*2^(a-2) := by
    rw [show a-1=(a-2)+1 by omega,pow_succ,Nat.mul_comm]
  have full : 2^a=2*2^(a-1) := by
    calc
      2^a=2^((a-1)+1) := by congr 1; omega
      _=2*2^(a-1) := by rw [pow_succ]; ring
  have vc : 2^(a-2)+1 < 2^(a-1) := by omega
  have vp := Nat.pow_le_pow_right (by decide : 0 < 2) (show a-1 ≤ a+(a-1)-1 by omega)
  have mp := Nat.pow_le_pow_right (by decide : 0 < 2) (show a ≤ a+(a-1) by omega)
  refine ⟨Nat.two_pow_pos _,by omega,by omega,?_⟩
  have hj := shift_submask 1 _ _ (full_submask (a-1) (2^(a-2)+1) vc)
  have hm : 2*(2^(a-1)-1)=2^a-2 := by omega
  have he : 2*(2^(a-2)+1)=2^(a-1)+2 := by omega
  simpa only [pow_one,hm,he] using hj

private theorem small_caps (p ell h : ℕ) (hp : 2 ≤ p) (he : 1 ≤ ell) (hh : h ≤ ell) :
    ell+h < 2*p*ell ∧
      2*p*(ell+h+1)-2 < 4*p^2*ell ∧ ell*(p+1) < 2*p^2*ell := by
  have hpell := Nat.mul_le_mul_right ell hp
  have hppell := Nat.mul_le_mul_right (p*ell) hp
  have hmul := Nat.mul_le_mul_left (2*p) (show ell+h+1 ≤ 3*ell by omega)
  have hsub : 2*p*(ell+h+1)-2 ≤ 2*p*(ell+h+1) := Nat.sub_le _ _
  have hpe : 0 < p*ell := Nat.mul_pos (by omega) (by omega)
  constructor
  · nlinarith only [hpell,he,hh]
  constructor
  · nlinarith only [hmul,hsub,hppell,hpe]
  · nlinarith only [hppell,hpell,he]

private theorem small_less_masks (r l : ℕ) (hr : 1 ≤ r) (hl : l < r) :
    MaskBounds (r+l+2) (r+l+2+r)
      (2^l) (2*2^r*(2^l+1)-2) (2^l*(2^r+1)) (2^(r+l+1)+2^(l+1)) := by
  have hp : 2 ≤ 2^r := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    norm_num at h ⊢
    exact h
  have he : 1 ≤ 2^l := Nat.one_le_two_pow
  have caps := small_caps (2^r) (2^l) 0 hp he (by omega)
  have alphaeq : 2^(r+l+2-1)=2*2^r*2^l := by
    rw [show r+l+2-1=(r+l)+1 by omega,pow_succ,pow_add]
    ring
  have meq : 2^(r+l+2+r)=4*(2^r)^2*2^l := by
    rw [show r+l+2+r=(r+r+l)+2 by omega,pow_add,pow_add,pow_add]
    norm_num
    ring
  have veq : 2^(r+l+2+r-1)=2*(2^r)^2*2^l := by
    rw [show r+l+2+r-1=(r+r+l)+1 by omega,pow_succ,pow_add,pow_add]
    ring
  have mdecomp : 2*2^r*(2^l+1)-2=2^(r+l+1)+2*(2^r-1) := by
    have heq : 2*2^r*(2^l+1)=2^r*2^l*2+2*2^r := by ring
    rw [pow_succ,pow_add,heq,Nat.mul_sub,Nat.mul_one]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [alphaeq]
    simpa only [Nat.add_zero] using caps.1
  · rw [meq]
    simpa only [Nat.add_zero] using caps.2.1
  · rw [veq]
    exact caps.2.2
  · rw [mdecomp]
    exact small_less_submask r l hr hl

private theorem small_ge_masks (r l : ℕ) (hr : 1 ≤ r) (hl : r ≤ l) :
    MaskBounds (r+l+2) (r+l+2+r)
      (2^l+2^(l-r)) (2*2^r*(2^l+2^(l-r)+1)-2)
      (2^l*(2^r+1)) (2^(r+l+1)+2^(l+1)) := by
  have hp : 2 ≤ 2^r := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    norm_num at h ⊢
    exact h
  have he : 1 ≤ 2^l := Nat.one_le_two_pow
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show l-r ≤ l by omega)
  have caps := small_caps (2^r) (2^l) (2^(l-r)) hp he hh
  have alphaeq : 2^(r+l+2-1)=2*2^r*2^l := by
    rw [show r+l+2-1=(r+l)+1 by omega,pow_succ,pow_add]
    ring
  have meq : 2^(r+l+2+r)=4*(2^r)^2*2^l := by
    rw [show r+l+2+r=(r+r+l)+2 by omega,pow_add,pow_add,pow_add]
    norm_num
    ring
  have veq : 2^(r+l+2+r-1)=2*(2^r)^2*2^l := by
    rw [show r+l+2+r-1=(r+r+l)+1 by omega,pow_succ,pow_add,pow_add]
    ring
  have ellrel : 2^r*2^(l-r)=2^l := by
    rw [←pow_add]
    congr 1
    omega
  have mdecomp : 2*2^r*(2^l+2^(l-r)+1)-2=
      2^(r+l+1)+(2^(l+1)+2*(2^r-1)) := by
    have heq : 2*2^r*(2^l+2^(l-r)+1)=
        2^r*2^l*2+2^l*2+2*2^r := by nlinarith only [ellrel]
    rw [pow_succ,pow_add,pow_succ,heq,Nat.mul_sub,Nat.mul_one]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [alphaeq]; exact caps.1
  · rw [meq]; exact caps.2.1
  · rw [veq]; exact caps.2.2
  · rw [mdecomp]
    exact small_ge_submask r l hr hl

private theorem special_high_masks : MaskBounds 2 3 0 2 1 2 := by
  constructor <;> norm_num [Submask]
private theorem special_point_masks : MaskBounds 2 3 1 6 2 4 := by
  constructor
  · decide
  · decide
  · decide
  · unfold Submask
    decide

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
