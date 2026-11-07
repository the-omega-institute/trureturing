/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/LowerArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-polynomial-certificates)
   mirror-E: none(waiver:private-consumed-polynomial-certificates)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twenty-two universal lower-sector polynomial certificates. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

/-! Twenty-two universal lower-sector polynomial certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open private A B L H K SU SV SW
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

-- Delta>=1; in fact Delta is even
private theorem cert_delta_positive (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 1≤h) :
    0≤-1 + 1*s*z - 2*s*z*h - 2*s*z^2*h + 2*s^2*z^2*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- 2 E1 <= K-1
private theorem cert_E1_upper (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 1≤h) :
    0≤-1*s*z + 4*s*z*h + 4*s*z^2*h - 2*s^2*z^2*h + 2*s^2*z^3*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- 2 F1 >= 0
private theorem cert_F1_lower (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 1≤h) :
    0≤2 + 3*s*z - 2*s*z*h - 2*s*z^2*h + 6*s^2*z^2*h + 2*s^2*z^3*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- 2 F1 <= SW-1
private theorem cert_F1_upper (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 1≤h) :
    0≤-2 - 3*s*z + 4*s*z*h + 4*s*z^2*h - 6*s^2*z^2*h + 2*s^2*z^3*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- r>=1
private theorem cert_K_above_L (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 1≤h) :
    0≤-1 - 1*z + 2*s*z*h - 1*s*z^2 + 2*s*z^2*h - 1*s^2*z^3 + 2*s^2*z^3*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- r<=y/2-1
private theorem cert_N_above_L (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 1≤h) :
    0≤-2 - 1*z - 1*s*z^2 - 1*s^2*z^3 + 2*s^3*z^4*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- r=h when h=1 or h=2
private theorem cert_r_h_for_h_one_two (s z : ℤ) (hs : 2≤s) (hz : 4≤z) :
    0≤4 + 5*z - 4*s*z + 1*s*z^2 + 1*s^2*z^3 := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  rw [he_s,he_z]
  ring_nf
  positivity

-- 2 F3 <= A-1 for r=h
private theorem cert_F3_upper_h_1 (s z : ℤ) (hs : 2≤s) (hz : 4≤z) :
    0≤-2 - 3*z + 3*s*z - 4*s*z^2 + 2*s^2*z^2 := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  rw [he_s,he_z]
  ring_nf
  positivity

-- 2 F3 <= A-1 for r=h
private theorem cert_F3_upper_h_2 (s z : ℤ) (hs : 2≤s) (hz : 4≤z) :
    0≤-4 - 5*z + 5*s*z - 6*s*z^2 + 4*s^2*z^2 + 2*s^2*z^3 := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  rw [he_s,he_z]
  ring_nf
  positivity

-- 2 F3 <= bound <= A-1
private theorem cert_F3_upper_h_ge_four (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 4≤h) :
    0≤2*h - 3*z + 2*z*h + 1*s*z - 2*s*z*h - 4*s*z^2 - 2*s*z^2*h + 2*s^2*z^2*h - 4*s^2*z^3 + 2*s^2*z^3*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-4
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+4 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- 2 E3 <= A-1
private theorem cert_E3_upper_h_ge_four (s z h : ℤ) (hs : 2≤s) (hz : 4≤z) (hh : 4≤h) :
    0≤-2*z + 1*s*z - 2*s*z^2 + 2*s^2*z^2*h - 2*s^2*z^3 + 2*s^2*z^3*h := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-4
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+4 := by dsimp [v_h]; ring
  rw [he_s,he_z,he_h]
  ring_nf
  positivity

-- 2 E3 <= A-1
private theorem cert_E3_upper_h_1 (s z : ℤ) (hs : 2≤s) (hz : 4≤z) :
    0≤-2 - 3*z + 3*s*z - 1*s*z^2 + 2*s^2*z^2 + 1*s^2*z^3 := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  rw [he_s,he_z]
  ring_nf
  positivity

-- 2 E3 <= A-1
private theorem cert_E3_upper_h_2 (s z : ℤ) (hs : 2≤s) (hz : 4≤z) :
    0≤-4 - 5*z + 5*s*z - 1*s*z^2 + 4*s^2*z^2 + 3*s^2*z^3 := by
  let v_s := s-2
  have hv_s : 0≤v_s := by dsimp [v_s]; omega
  have he_s : s=v_s+2 := by dsimp [v_s]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  rw [he_s,he_z]
  ring_nf
  positivity

-- 2 E2<=B-1 using E3<=L-1
private theorem cert_s2_E2_upper (z h : ℤ) (hz : 4≤z) (hh : 1≤h) :
    0≤2 + 3*z - 6*z^2 + 24*z^2*h - 4*z^3 + 8*z^3*h := by
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_z,he_h]
  ring_nf
  positivity

-- F2>=0 using F3>=0
private theorem cert_s2_F2_lower (z h : ℤ) (hz : 4≤z) (hh : 1≤h) :
    0≤-4 - 3*z + 12*z^2 - 40*z^2*h - 8*z^3 + 24*z^3*h := by
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_z,he_h]
  ring_nf
  positivity

-- 2 F2<=SU-1 using 2 F3<=A-1
private theorem cert_s2_F2_upper (z h : ℤ) (hz : 4≤z) (hh : 1≤h) :
    0≤4 + 5*z - 4*z^2 + 32*z^2*h + 8*z^3 := by
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_z,he_h]
  ring_nf
  positivity

-- E2>=0 using E3>=0 for h>=2
private theorem cert_s2_E2_lower_h_ge_two (z h : ℤ) (hz : 4≤z) (hh : 2≤h) :
    0≤-2 - 3*z + 6*z^2 - 24*z^2*h - 4*z^3 + 8*z^3*h := by
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-2
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+2 := by dsimp [v_h]; ring
  rw [he_z,he_h]
  ring_nf
  positivity

-- 2 E2>=0 with r=1 at h=1
private theorem cert_s2_E2_lower_h_one (z : ℤ) (hz : 4≤z) :
    0≤-4*z - 16*z^2 + 8*z^3 := by
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  rw [he_z]
  ring_nf
  positivity

-- 2 E2>=0
private theorem cert_s4q_E2_lower (q z h : ℤ) (hq : 1≤q) (hz : 4≤z) (hh : 1≤h) :
    0≤2 - 6*q + 12*q*z - 8*q*z*h - 8*q*z^2*h - 24*q^2*z + 32*q^2*z^2 + 32*q^2*z^2*h - 192*q^3*z^2*h + 64*q^3*z^3*h := by
  let v_q := q-1
  have hv_q : 0≤v_q := by dsimp [v_q]; omega
  have he_q : q=v_q+1 := by dsimp [v_q]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_q,he_z,he_h]
  ring_nf
  positivity

-- 2 E2<=B-1
private theorem cert_s4q_E2_upper (q z h : ℤ) (hq : 1≤q) (hz : 4≤z) (hh : 1≤h) :
    0≤-2 + 6*q - 8*q*z + 8*q*z*h + 8*q*z^2*h + 24*q^2*z - 16*q^2*z^2 - 32*q^2*z^2*h + 192*q^3*z^2*h + 64*q^3*z^3*h := by
  let v_q := q-1
  have hv_q : 0≤v_q := by dsimp [v_q]; omega
  have he_q : q=v_q+1 := by dsimp [v_q]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_q,he_z,he_h]
  ring_nf
  positivity

-- 2 F2>=0
private theorem cert_s4q_F2_lower (q z h : ℤ) (hq : 1≤q) (hz : 4≤z) (hh : 1≤h) :
    0≤4 - 12*q + 28*q*z - 8*q*z*h - 8*q*z^2*h - 48*q^2*z + 64*q^2*z^2 + 96*q^2*z^2*h + 32*q^2*z^3*h - 384*q^3*z^2*h + 128*q^3*z^3*h := by
  let v_q := q-1
  have hv_q : 0≤v_q := by dsimp [v_q]; omega
  have he_q : q=v_q+1 := by dsimp [v_q]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_q,he_z,he_h]
  ring_nf
  positivity

-- 2 F2<=SU-1
private theorem cert_s4q_F2_upper (q z h : ℤ) (hq : 1≤q) (hz : 4≤z) (hh : 1≤h) :
    0≤-4 + 12*q - 20*q*z + 8*q*z*h + 8*q*z^2*h + 48*q^2*z - 32*q^2*z^2 - 96*q^2*z^2*h - 32*q^2*z^3*h + 384*q^3*z^2*h + 128*q^3*z^3*h := by
  let v_q := q-1
  have hv_q : 0≤v_q := by dsimp [v_q]; omega
  have he_q : q=v_q+1 := by dsimp [v_q]; ring
  let v_z := z-4
  have hv_z : 0≤v_z := by dsimp [v_z]; omega
  have he_z : z=v_z+4 := by dsimp [v_z]; ring
  let v_h := h-1
  have hv_h : 0≤v_h := by dsimp [v_h]; omega
  have he_h : h=v_h+1 := by dsimp [v_h]; ring
  rw [he_q,he_z,he_h]
  ring_nf
  positivity

set_option maxHeartbeats 2400000 in
private theorem lower_windows (s z h r t : ℤ)
    (hs : 2≤s) (hz : 4≤z) (hh : 1≤h)
    (hze : ∃ z0 : ℤ, z=2*z0)
    (ht : (s=2 ∧ t=2) ∨ ∃ q : ℤ, 1≤q ∧ s=4*q ∧ t=3*q)
    (hhd : h=1 ∨ h=2 ∨ 4≤h)
    (hr : 1≤r)
    (hceil : K (s*z) (2*s*z*h) z-L (s*z) z≤2*r*L (s*z) z ∧
      2*r*L (s*z) z<K (s*z) (2*s*z*h) z+L (s*z) z) :
    let x:=s*z
    let y:=2*s*z*h
    let u:=if s=2 then r else 0
    (0≤A x y z-K x y z ∧ A x y z-K x y z≤K x y z-1) ∧
    (0≤3*A x y z-SW x y z ∧ 3*A x y z-SW x y z≤SW x y z-1) ∧
    (0≤A x y z-K x y z+2*B x y-2*t*A x y z+2*u*L x z ∧
      A x y z-K x y z+2*B x y-2*t*A x y z+2*u*L x z≤B x y-1) ∧
    (0≤(3-4*t)*A x y z-SW x y z+2*SU x y+2*u*SV x z ∧
      (3-4*t)*A x y z-SW x y z+2*SU x y+2*u*SV x z≤SU x y-1) ∧
    (0≤(2*r+1)*L x z-K x y z ∧ (2*r+1)*L x z-K x y z≤A x y z-1) ∧
    (0≤(2*r+1)*SV x z-SW x y z ∧ (2*r+1)*SV x z-SW x y z≤A x y z-1) := by
  let x:=s*z
  let y:=2*s*z*h
  let E:=x-z-1
  have hL : 1≤L x z := by
    have hs0 : 0≤s := by omega
    have hz0 : 0≤z := by omega
    have hpos : 0≤L x z-1 := by dsimp [L,x]; ring_nf; positivity
    omega
  have hE : 1≤E := by dsimp [E,x]; nlinarith
  have hid : K x y z=2*h*L x z+2*h*E+1 := by dsimp [K,H,L,E,x,y]; ring
  have hsmall : 4*E+1≤L x z := by
    have hp:=cert_r_h_for_h_one_two s z hs hz
    dsimp [L,E,x] at *
    nlinarith only [hp]
  have hrh : h≤r := by
    by_contra hn
    have hm:=mul_le_mul_of_nonneg_right (show r≤h-1 by omega) (show 0≤L x z by omega)
    have he:=mul_nonneg (show 0≤h by omega) (show 0≤E by omega)
    dsimp only [x,y] at hid hm hL he
    nlinarith only [hceil.1,hid,hm,hL,he]
  have hrexact (hh2 : h≤2) : r=h := by
    have hmul:=mul_le_mul_of_nonneg_right hh2 (show 0≤E by omega)
    by_contra hn
    have hm:=mul_le_mul_of_nonneg_right (show h+1≤r by omega) (show 0≤L x z by omega)
    dsimp only [x,y] at hid hm hsmall hmul
    nlinarith only [hceil.2,hid,hm,hsmall,hmul]
  have cap : r≤x*h-1 := by
    have hp:=cert_N_above_L s z h hs hz hh
    have hyL : y*L x z=x^2*y*z-1+K x y z := by dsimp [L,K,H]; ring
    have hNL : L x z≤x^2*y*z-1 := by dsimp [L,x,y] at *; nlinarith only [hp]
    by_contra hn
    have hm:=mul_le_mul_of_nonneg_right (show x*h≤r by omega) (show 0≤L x z by omega)
    dsimp [y] at hyL
    dsimp only [x,y] at hm hNL hyL
    nlinarith only [hceil.2,hm,hNL,hyL]
  let e:=(2*r+1)*L x z-K x y z
  let f:=(2*r+1)*SV x z-SW x y z
  obtain ⟨z0,hz0⟩:=hze
  have eparity : e%2=0 := by
    have ep : e=2*(r*L x z+z0*(1+x+x^2)-s*z*h*(1+z+x*z)) := by
      dsimp [e,K,H,L,y]
      rw [hz0]
      ring
    rw [ep]
    omega
  have he : 0≤e ∧ e≤2*L x z-2 := by
    have eh : 0≤e ∧ e<2*L x z := by
      dsimp [e]
      dsimp only [x,y] at *
      constructor <;> nlinarith only [hceil.1,hceil.2]
    exact ⟨eh.1,by omega⟩
  have hfidentity : f=2*e+1+(y-2*r-1)*(z+1) := by
    dsimp [f,e,SV,SW,K,H,L]; ring
  have hf0 : 0≤f := by
    have hz1 : 0≤z+1 := by omega
    have hc : 0≤y-2*r-1 := by
      dsimp [y]
      dsimp only [x] at cap
      nlinarith only [cap]
    nlinarith only [hfidentity,he.1,mul_nonneg hc hz1]
  have hthird : e≤A x y z-1 ∧ f≤A x y z-1 := by
    rcases hhd with h1|h2|h4
    · have rr:=hrexact (by omega : h≤2)
      subst h
      subst r
      have pe:=cert_E3_upper_h_1 s z hs hz
      have pf:=cert_F3_upper_h_1 s z hs hz
      dsimp [e,f,A,K,H,L,SV,SW,x,y] at *
      constructor <;> nlinarith only [pe,pf]
    · have rr:=hrexact (by omega : h≤2)
      subst h
      subst r
      have pe:=cert_E3_upper_h_2 s z hs hz
      have pf:=cert_F3_upper_h_2 s z hs hz
      dsimp [e,f,A,K,H,L,SV,SW,x,y] at *
      constructor <;> nlinarith only [pe,pf]
    · have pe:=cert_E3_upper_h_ge_four s z h hs hz h4
      have pf:=cert_F3_upper_h_ge_four s z h hs hz h4
      have hm:=mul_le_mul_of_nonneg_right hrh (show 0≤z+1 by omega)
      have ecap : 2*L x z-2≤A x y z-1 := by
        dsimp [A,L,x,y] at *
        nlinarith only [pe]
      have fcap : 4*L x z-3+(2*h*(x-1)-1)*(z+1)≤A x y z-1 := by
        dsimp [A,L,x,y] at *
        nlinarith only [pf]
      exact ⟨le_trans he.2 ecap,by
        rw [show y=2*x*h by dsimp [y,x]; ring] at hfidentity
        nlinarith only [hfidentity,he.2,hm,fcap]⟩
  have hfirst : (0≤A x y z-K x y z ∧ A x y z-K x y z≤K x y z-1) ∧
      (0≤3*A x y z-SW x y z ∧ 3*A x y z-SW x y z≤SW x y z-1) := by
    have p0:=cert_delta_positive s z h hs hz hh
    have p1:=cert_E1_upper s z h hs hz hh
    have p2:=cert_F1_lower s z h hs hz hh
    have p3:=cert_F1_upper s z h hs hz hh
    dsimp [A,K,H,SW,x,y]
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> nlinarith only [p0,p1,p2,p3]
  dsimp only
  refine ⟨hfirst.1,hfirst.2,?_,?_,⟨he.1,hthird.1⟩,⟨hf0,hthird.2⟩⟩
  all_goals rcases ht with ⟨hs2,ht2⟩|⟨q,hq,hsq,htq⟩
  · subst s; subst t
    simp only [ite_true]
    have pl:=cert_s2_E2_lower_h_one z hz
    have pg:=cert_s2_E2_lower_h_ge_two z h hz
    have pu:=cert_s2_E2_upper z h hz hh
    constructor
    · by_cases hh1 : h=1
      · have rr:=hrexact (by omega : h≤2)
        subst h; subst r
        dsimp [A,B,K,H,L,x,y] at *
        nlinarith only [pl]
      · have hh2 : 2≤h := by omega
        have hp:=pg hh2
        dsimp [A,B,K,H,L,e,x,y] at *
        nlinarith only [hp,he.1]
    · dsimp [A,B,K,H,L,e,x,y] at *
      nlinarith only [pu,he.2]
  · subst s; subst t
    have hsne : (4*q:ℤ)≠2 := by omega
    simp only [if_neg hsne]
    have pl:=cert_s4q_E2_lower q z h hq hz hh
    have pu:=cert_s4q_E2_upper q z h hq hz hh
    dsimp [A,B,K,H,L,x,y]
    constructor <;> nlinarith only [pl,pu]
  · subst s; subst t
    simp only [ite_true]
    have pl:=cert_s2_F2_lower z h hz hh
    have pu:=cert_s2_F2_upper z h hz hh
    dsimp [A,B,K,H,L,SU,SV,SW,f,x,y] at *
    constructor <;> nlinarith only [pl,pu,hf0,hthird.2]
  · subst s; subst t
    have hsne : (4*q:ℤ)≠2 := by omega
    simp only [if_neg hsne]
    have pl:=cert_s4q_F2_lower q z h hq hz hh
    have pu:=cert_s4q_F2_upper q z h hq hz hh
    dsimp [A,B,K,H,L,SU,SV,SW,x,y]
    constructor <;> nlinarith only [pl,pu]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
