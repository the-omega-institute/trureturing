/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/PhysicalSelection
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Full-domain parity-tail physical source construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.IntegerSelector

/-!
Private dyadic arithmetic supplies the physical bank selector.
The strict U-mask capacities follow from the exact integer selector identity
on the full four-gap domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail

open private integer_tail_selector
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.IntegerSelector

private def physicalDomain (a b c d : ℕ) : Prop :=
  4 ≤ c ∧ c + 2 ≤ a ∧ a + c + 1 ≤ d ∧ d + 1 ≤ b

-- The selector does not itself assert the two strict U-mask capacities.
-- A coarse alpha < u*h bound suffices because z >= 16 supplies ample room.
private theorem selector_capacities (u z h alpha S delta B : ℤ)
    (hu : 4 ≤ u) (hz : 16 ≤ z) (hh : 2*z ≤ h)
    (heven : (2 : ℤ) ∣ h)
    (hS : 2 ≤ S) (hS4 : 4*S ≤ 7*z)
    (hd0 : 0 ≤ delta) (hdJ : delta ≤ 2*(u-1))
    (hB : 8*B = 15*u*z)
    (hid : 2*u*(z+1)*alpha =
      (u^2*z+1)*h + (u*z+1)*S - B + delta) :
    0 < alpha ∧ alpha < u*z*h/2-1 := by
  have hu0 : 0 < u := by omega
  have hz0 : 0 < z := by omega
  have hh1 : 1 ≤ h := by omega
  have hM : 0 < 2*u*(z+1) := by positivity
  have huz : 0 < u*z := mul_pos hu0 hz0
  have huh : 4 ≤ u*h := by
    have hm := mul_nonneg hu0.le (show 0 ≤ h-1 by omega)
    nlinarith only [hm,hu]
  have hAS : 0 ≤ (u*z+1)*S := mul_nonneg (by positivity) (by omega)
  have hB0 : 0 ≤ B := by nlinarith only [hB,huz]
  have hlow : 0 < (u^2*z+1)*h-B := by
    have hm : 0 < (u*z)*(8*u*h-15) := mul_pos huz (by nlinarith only [huh])
    nlinarith only [hm,hB,hh1]
  have ha0 : 0 < alpha := by
    by_contra ha
    have hm := mul_nonpos_of_nonneg_of_nonpos hM.le (le_of_not_gt ha)
    nlinarith only [hm,hid,hlow,hAS,hd0]
  have hSh : S ≤ h := by omega
  have hASh := mul_le_mul_of_nonneg_left hSh (show 0 ≤ u*z+1 by positivity)
  have hterm0 : 0 ≤ u*(u-1)*z*h :=
    mul_nonneg (mul_nonneg (mul_nonneg hu0.le (by omega)) hz0.le) (by omega)
  have husq : u+1 ≤ u^2 := by nlinarith only [sq_nonneg (u-2),hu]
  have hterm1 : 0 ≤ (u^2-1)*(h-1) := mul_nonneg (by nlinarith only [husq,hu]) (by omega)
  have hauh : alpha < u*h := by
    by_contra ha
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt ha) hM.le
    nlinarith only [hm,hid,hASh,hB0,hdJ,hterm0,hterm1,husq]
  have hhalf : 2*(u*z*h/2) = u*z*h := by
    apply Int.mul_ediv_cancel'
    obtain ⟨v,hv⟩ := heven
    refine ⟨u*z*v,?_⟩
    rw [hv]
    ring
  have hspread : 0 ≤ (u*h)*(z-4) := mul_nonneg (by omega) (by omega)
  have hroom : u*h+1 < u*z*h/2 := by nlinarith only [hhalf,hspread,huh]
  exact ⟨ha0,by omega⟩

private theorem dyadic_lower (n m : ℕ) (hmn : m ≤ n) :
    (2 : ℤ)^m ≤ 2^n := by
  exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hmn)

private theorem dyadic_dvd (n m : ℕ) (hmn : m ≤ n) :
    (2 : ℤ)^m ∣ 2^n := by
  refine ⟨(2 : ℤ)^(n-m),?_⟩
  rw [←pow_add,Nat.add_sub_of_le hmn]

-- These identities also identify every mask in PhysicalBanks with the caller's
-- u,z,h,t coordinates. In particular q has exponent b-a-1, not b-a.
private theorem physical_coordinates (a b c d : ℕ) (hd : physicalDomain a b c d) :
    let u := (2 : ℤ)^(a-c)
    let z := (2 : ℤ)^c
    let h := (2 : ℤ)^(d-a)
    let t := (2 : ℤ)^(b-d-1)
    u*z = 2^a ∧ u*z*h = 2^d ∧ h*t = 2^(b-a-1) ∧
      z/2 = 2^(c-1) ∧ u*z*h/2 = 2^(d-1) ∧
      u*(z/2-1) = 2^(a-1)-u := by
  rcases hd with ⟨hc,ha,hd,hb⟩
  dsimp only
  have hx : (2 : ℤ)^(a-c)*2^c = 2^a := by
    rw [←pow_add,Nat.sub_add_cancel (by omega : c ≤ a)]
  have hw : (2 : ℤ)^(a-c)*2^c*2^(d-a) = 2^d := by
    rw [hx,←pow_add,Nat.add_sub_of_le (by omega : a ≤ d)]
  have hq : (2 : ℤ)^(d-a)*2^(b-d-1) = 2^(b-a-1) := by
    rw [←pow_add]
    congr 1
    omega
  have hz2 : 2*(2 : ℤ)^(c-1) = 2^c := by
    rw [←pow_succ']
    congr 1
    omega
  have hw2 : 2*(2 : ℤ)^(d-1) = 2^d := by
    rw [←pow_succ']
    congr 1
    omega
  have hzhalf : (2 : ℤ)^c/2 = 2^(c-1) := by omega
  refine ⟨hx,hw,hq,hzhalf,?_,?_⟩
  · rw [hw]
    omega
  · rw [hzhalf]
    have hux : (2 : ℤ)^(a-c)*2^(c-1) = 2^(a-1) := by
      rw [←pow_add]
      congr 1
      omega
    nlinarith only [hux]

/-- Integral choice with strict physical U capacities, without a certificate
hypothesis. S remains the very selector reserve; it is not re-rounded. -/
private theorem selected_arithmetic (a b c d : ℕ) (hd : physicalDomain a b c d) :
    ∃ alpha S : ℕ, ∃ delta : ℤ,
      0 < alpha ∧ alpha < 2^(d-1)-1 ∧
      2 ≤ S ∧ 4*S ≤ 7*2^c ∧ S < 2^(d-a) ∧
      0 ≤ delta ∧ delta ≤ 2*((2 : ℤ)^(a-c)-1) ∧
      2*(2 : ℤ)^(a-c)*(2^c+1)*(alpha : ℤ) =
        (((2 : ℤ)^(a-c))^2*2^c+1)*2^(d-a) +
        ((2 : ℤ)^(a-c)*2^c+1)*(S : ℤ) -
        15*(2 : ℤ)^(a-c)*2^c/8 + delta ∧
      8*(15*(2 : ℤ)^(a-c)*2^c/8) = 15*(2 : ℤ)^(a-c)*2^c := by
  have hc := hd.1
  have ha := hd.2.1
  have hda := hd.2.2.1
  let u := (2 : ℤ)^(a-c)
  let z := (2 : ℤ)^c
  let h := (2 : ℤ)^(d-a)
  have hu : 4 ≤ u := by
    simpa only [show (2 : ℤ)^2=4 by norm_num] using
      (dyadic_lower (a-c) 2 (by omega))
  have hz : 16 ≤ z := by
    simpa only [show (2 : ℤ)^4=16 by norm_num] using (dyadic_lower c 4 hc)
  have hh : 2*z ≤ h := by
    have hm := dyadic_lower (d-a) (c+1) (by omega)
    simpa only [pow_succ',z] using hm
  have hue : (2 : ℤ) ∣ u := by simpa only [pow_one, u] using dyadic_dvd (a-c) 1 (by omega)
  have hze : (8 : ℤ) ∣ z := by
    simpa only [show (2 : ℤ)^3=8 by norm_num] using dyadic_dvd c 3 (by omega)
  have hhe : (2 : ℤ) ∣ h := by simpa only [pow_one, h] using dyadic_dvd (d-a) 1 (by omega)
  obtain ⟨hB,alpha,S,delta,p,K,r,hp,hK,hmin,hr,hS,hAlpha,hDelta,
    hgap0,hgapWidth,hzero,hS2,hS4,hSdiv,hR0,hRh,hd0,hdJ,hstrict,hid⟩ :=
    integer_tail_selector u z h hu hz hh hue hze hhe
  obtain ⟨ha0,hacap⟩ := selector_capacities u z h alpha S delta (15*u*z/8)
    hu hz hh hhe hS2 hS4 hd0 hdJ hB hid
  have haCast : (alpha.toNat : ℤ) = alpha := Int.toNat_of_nonneg ha0.le
  have hSCast : (S.toNat : ℤ) = S := Int.toNat_of_nonneg (by omega)
  obtain ⟨_,_,_,_,hcap,_⟩ := physical_coordinates a b c d hd
  change u*z*h/2 = (2 : ℤ)^(d-1) at hcap
  have haNat : 0 < alpha.toNat := by exact_mod_cast (show (0 : ℤ) < (alpha.toNat : ℤ) by omega)
  have haBound : alpha.toNat < 2^(d-1)-1 := by
    have hb : alpha.toNat+1 < 2^(d-1) := by
      exact_mod_cast (show (alpha.toNat : ℤ)+1 < (2 : ℤ)^(d-1) by omega)
    omega
  refine ⟨alpha.toNat,S.toNat,delta,haNat,haBound,?_,?_,?_,hd0,hdJ,?_,hB⟩
  · exact_mod_cast (show (2 : ℤ) ≤ (S.toNat : ℤ) by omega)
  · have hh' : (4 : ℤ)*(S.toNat : ℤ) ≤ 7*2^c := by rw [hSCast]; exact hS4
    exact_mod_cast hh'
  · have hh' : (S.toNat : ℤ) < (2 : ℤ)^(d-a) := by rw [hSCast]; exact sub_pos.mp hR0
    exact_mod_cast hh'
  · simpa only [haCast,hSCast] using hid

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
