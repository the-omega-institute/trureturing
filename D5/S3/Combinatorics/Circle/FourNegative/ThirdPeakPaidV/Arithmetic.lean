/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-paid-V-arithmetic)
   mirror-E: none(waiver:private-consumed-paid-V-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact quotient and all endpoint windows for paid low V and one W tail. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import Mathlib.Data.Int.DivMod

/-! Exact unbounded arithmetic for the physical paid-V construction.
The integer hypotheses below are derived from the original exponent inequalities
in Allocation; no allocation, window or quotient feasibility is assumed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y t : ℤ) : ℤ := 1+t+x*t+x*y*t
private def L (x z t : ℤ) : ℤ := 1+z+z*t+x*z*t
private def K (y z t : ℤ) : ℤ := 1+y+y*z+y*z*t
private def H (y z : ℤ) : ℤ := 1+y+y*z
private def SU (x y t : ℤ) : ℤ := 2*B x y t-1
private def SV (x z t : ℤ) : ℤ := 2*L x z t-1-z
private def SW (y z t : ℤ) : ℤ := 2*K y z t-H y z
private def window (e T : ℤ) : Prop := 0≤2*e ∧ 2*e≤T-1
private def quotient (x y z t m : ℤ) : ℤ := (L x z t-A x y z)/(m*B x y t)
private def E (x y z t m : ℤ) : ℤ := m*B x y t-A x y z
private def Ep (x y z t m : ℤ) : ℤ := 2*E x y z t m-m
private def R (x y z t m : ℤ) : ℤ := L x z t-A x y z-quotient x y z t m*(m*B x y t)
private def Rp (x y z t m : ℤ) : ℤ := 2*R x y z t m-z-1+m*quotient x y z t m
private def G (x y z t w : ℤ) : ℤ := K y z t-A x y z-w*L x z t
private def Gp (x y z t w : ℤ) : ℤ := 2*G x y z t w-H y z+w*(z+1)

private theorem basic_margins (x y z t : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (ht : y≤t) (htx : 4*x≤t) (hz : 2*t≤z) :
    z+1<A x y z ∧ z+1≤L x z t-A x y z ∧
    2*A x y z≤SV x z t-1 ∧ L x z t<x*y*z*t-1 := by
  have hx0 : 0<x := by omega
  have hy8 : 8≤y := by omega
  have ht16 : 16≤t := by omega
  have hz32 : 32≤z := by omega
  have hy0 : 0<y := by omega
  have ht0 : 0<t := by omega
  have hz0 : 0<z := by omega
  have hxy2:=mul_le_mul_of_nonneg_left (show 2≤y by omega) hx0.le
  have hxy : 1≤x*y-1 := by nlinarith only [hxy2,hx]
  have hA : z+1<A x y z := by
    have hp:=mul_nonneg (show 0≤z by omega) (show 0≤x*y-1 by omega)
    dsimp [A]
    nlinarith only [hp,hx,hxy]
  have hgap : 0≤L x z t-A x y z-(z-t)*(1+t) := by
    have he : L x z t-A x y z-(z-t)*(1+t)=
        x*(z+1)*(t-y)+(t-x)*(t+1) := by dsimp [L,A];ring
    rw [he]
    have h0 : 0≤x*(z+1)*(t-y) := mul_nonneg (by positivity) (by omega)
    have h1 : 0≤(t-x)*(t+1) := mul_nonneg (by omega) (by omega)
    omega
  have hfar : z+1<(z-t)*(1+t) := by
    have hp:=mul_le_mul_of_nonneg_left (show 1≤z-t-1 by omega) (show 0≤t by omega)
    nlinarith only [hp,ht16]
  have hLA : z+1≤L x z t-A x y z := by omega
  have hSV : 2*A x y z≤SV x z t-1 := by dsimp [SV];omega
  have hc : 1≤x*y-x-1 := by nlinarith only [hx,hxy2]
  have hp:=mul_le_mul_of_nonneg_left hc (show 0≤z*t by positivity)
  have hzt:=mul_le_mul_of_nonneg_left (show 4≤t by omega) (show 0≤z by omega)
  have hN : L x z t<x*y*z*t-1 := by
    dsimp [L]
    nlinarith only [hp,hzt,hz32]
  exact ⟨hA,hLA,hSV,hN⟩

private theorem first_windows (x y z t m : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (ht : y≤t) (hz : 2*t≤z)
    (hm : 2≤m) (hmy : 4*m≤y) (hzt : z=m*t) :
    window (E x y z t m) (B x y t) ∧ window (Ep x y z t m) (SU x y t) := by
  have hy8 : 8≤y := by omega
  have hx0 : 0<x := by omega
  have hy0 : 0<y := by omega
  have ht0 : 0<t := by omega
  have hz0 : 0<z := by omega
  have hm0 : 0<m := by omega
  have hxm : 0≤x-1 := by omega
  have h8xm : 0≤8*x-2 := by omega
  have he : E x y z t m=m-1+x*(z-y)+z-x := by
    rw [hzt];dsimp [E,A,B];ring
  have hep : Ep x y z t m=m-2+2*x*(z-y)+2*z-2*x := by
    dsimp only [Ep];rw [he];ring
  have hE : 0<E x y z t m := by
    have hp:=mul_nonneg (show 0≤x by omega) (show 0≤z-y by omega)
    rw [he];nlinarith only [hp,hm,hx,hy,hz,ht]
  have hEp : 0<Ep x y z t m := by
    have hp:=mul_nonneg (show 0≤x by omega) (show 0≤z-y by omega)
    rw [hep];nlinarith only [hp,hm,hx,hy,hz,ht]
  let beta:=y-4*m
  have hb : 0≤beta := by dsimp [beta];omega
  have hs : B x y t-1-2*E x y z t m=
      t*(2*m*(x-1)+x*beta+1+x)+2*x+2*x*beta+(8*x-2)*m+2 := by
    dsimp [B,E,A,beta];rw [hzt];ring
  have hslack : 0<B x y t-1-2*E x y z t m := by
    rw [hs]
    have hp0 : 0≤2*m*(x-1)+x*beta+1+x := by positivity
    have hp1 : 0≤t*(2*m*(x-1)+x*beta+1+x) := mul_nonneg (by omega) hp0
    have hp2 : 0≤2*x*beta := by positivity
    have hp3 : 0≤(8*x-2)*m := by positivity
    nlinarith only [hp1,hp2,hp3,hx]
  have hn : SU x y t-1-2*Ep x y z t m=
      2*(B x y t-1-2*E x y z t m)+2*m := by dsimp [SU,Ep];ring
  constructor <;> constructor
  · omega
  · omega
  · omega
  · rw [show SU x y t-1=2*Ep x y z t m+
        (SU x y t-1-2*Ep x y z t m) by ring,hn];omega

/-- The exact Euclidean quotient is nonnegative and strictly below the
full high-block capacity t/2. This is proved, never an allocation premise. -/
private theorem quotient_bounds (x y z t m T : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (ht : y≤t) (htx : 4*x≤t)
    (hz : 2*t≤z) (hm : 2≤m) (hzt : z=m*t) (hT : 2*T=t) :
    0≤quotient x y z t m ∧ quotient x y z t m<T ∧
    0≤R x y z t m ∧ R x y z t m<m*B x y t ∧
    2*m*quotient x y z t m<z := by
  have margins:=basic_margins x y z t hx hy ht htx hz
  have hx0 : 0<x := by omega
  have hy0 : 0<y := by omega
  have ht0 : 0<t := by omega
  have hz0 : 0<z := by omega
  have hB : 0<B x y t := by dsimp [B];positivity
  have hJ : 0<m*B x y t := mul_pos (by omega) hB
  have hq : 0≤quotient x y z t m := Int.ediv_nonneg (by omega) hJ.le
  have he := Int.emod_add_mul_ediv (L x z t-A x y z) (m*B x y t)
  have hlo := Int.emod_nonneg (L x z t-A x y z) (ne_of_gt hJ)
  have hhi := Int.emod_lt_of_pos (L x z t-A x y z) hJ
  have hr : R x y z t m=(L x z t-A x y z)%(m*B x y t) := by
    dsimp [R,quotient];nlinarith only [he]
  have hrec : z*B x y t=x*y*z*t-1+L x z t := by dsimp [B,L];ring
  have hA : 0<A x y z := by dsimp [A];positivity
  have hcapId : 2*(T*(m*B x y t)-(L x z t-A x y z))=
      (x*y*z*t-1)-L x z t+2*A x y z := by
    calc
      _ = z*B x y t-2*L x z t+2*A x y z := by rw [hzt,←hT];ring
      _ = _ := by rw [hrec];ring
  have hcap : L x z t-A x y z<T*(m*B x y t) := by
    nlinarith only [hcapId,margins.2.2.2,hA]
  have hqcap : quotient x y z t m<T := by
    by_contra hh
    have hp:=mul_le_mul_of_nonneg_right (show T≤quotient x y z t m by omega) hJ.le
    dsimp [R,quotient] at hr
    dsimp [quotient] at hp ⊢
    nlinarith only [he,hlo,hcap,hp]
  have hshift:=mul_lt_mul_of_pos_left hqcap (show 0<2*m by omega)
  have hzT : z=2*m*T := by rw [hzt,←hT];ring
  exact ⟨hq,hqcap,by rw [hr];exact hlo,by rw [hr];exact hhi,
    by nlinarith only [hshift,hzT]⟩

set_option maxHeartbeats 2400000 in
private theorem v_windows (x y z t m T : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (ht : y≤t) (htx : 4*x≤t)
    (hz : 2*t≤z) (hm : 2≤m) (hmy : 4*m≤y) (hzt : z=m*t)
    (hT : 2*T=t) (dyadic : t=y ∨ 2*y≤t) :
    window (R x y z t m) (L x z t) ∧
    window (if Rp x y z t m<0 then Rp x y z t m+A x y z else Rp x y z t m)
      (SV x z t) := by
  have mar:=basic_margins x y z t hx hy ht htx hz
  have first:=first_windows x y z t m hx hy ht hz hm hmy hzt
  have qb:=quotient_bounds x y z t m T hx hy ht htx hz hm hzt hT
  have hy8 : 8≤y := by omega
  have ht16 : 16≤t := by omega
  have hxy0 : 0≤x*y := mul_nonneg (by omega) (by omega)
  have hw : window (R x y z t m) (L x z t) := by
    refine ⟨by omega,?_⟩
    rcases dyadic with he|hsep
    · have hid : 2*A x y z-L x z t-1=
          2*x+2*x*y+z*((x-1)*y-1) := by rw [he];dsimp [A,L];ring
      have hp : 0≤z*((x-1)*y-1) := by
        apply mul_nonneg (by omega)
        have hp:=mul_le_mul_of_nonneg_left (show 2≤y by omega) (show 0≤x-1 by omega)
        nlinarith only [hx,hp]
      have hsmall : L x z t-A x y z<m*B x y t := by
        dsimp [window,E] at first
        nlinarith only [hid,hp,hx,hxy0,first.1.1]
      have hzero : quotient x y z t m=0 := by
        by_contra hn
        have hB : 0<B x y t := by
          have hx0 : 0<x := by omega
          have hy0 : 0<y := by omega
          have ht0 : 0<t := by omega
          dsimp [B];positivity
        have hp:=mul_le_mul_of_nonneg_right (show 1≤quotient x y z t m by omega)
          (mul_nonneg (show 0≤m by omega) hB.le)
        have hr:=qb.2.2.1
        dsimp [R] at hr
        nlinarith only [hp,hr,hsmall]
      dsimp [R];rw [hzero];nlinarith only [hid,hp,hx,hxy0]
    · let C:=(1+x)*t-1-2*x-2*x*y
      have hc : 1≤C := by
        have hp:=mul_le_mul_of_nonneg_left hsep (show 0≤1+x by omega)
        dsimp [C];nlinarith only [hp,hy,hx]
      have hp:=mul_le_mul_of_nonneg_left hc (show 0≤t by omega)
      have hpos : 0<m*(t*C-2) := mul_pos (by omega) (by omega)
      have hid : L x z t-2*(m*B x y t)=1+m*(t*C-2) := by
        rw [hzt];dsimp [L,B,C];ring
      have hlarge : 2*(m*B x y t)<L x z t := by linarith only [hid,hpos]
      omega
  refine ⟨hw,?_⟩
  split_ifs with he
  · have hmQ : 0≤m*quotient x y z t m := mul_nonneg (by omega) qb.1
    have hlo : 0<Rp x y z t m+A x y z := by dsimp [Rp];omega
    exact ⟨by omega,by omega⟩
  · have hi : 2*Rp x y z t m≤SV x z t-1 := by
      dsimp [Rp,SV]
      nlinarith only [hw.2,qb.2.2.2.2]
    exact ⟨by omega,hi⟩

set_option maxHeartbeats 2400000 in
private theorem w_windows (x y z t w : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (htx : 4*x≤t) (hz : 2*t≤z)
    (hw : 2*x*w=y) :
    window (G x y z t w) (K y z t) ∧
    window (Gp x y z t w) (SW y z t) ∧
    window (Gp x y z t w+A x y z) (SW y z t) := by
  have hx0 : 0<x := by omega
  have hy8 : 8≤y := by omega
  have ht16 : 16≤t := by omega
  have hz32 : 32≤z := by omega
  have hy0 : 0<y := by omega
  have ht0 : 0<t := by omega
  have hz0 : 0<z := by omega
  have h2x : 0<2*x-1 := by omega
  let C0:=2*x^2-2*x+1
  let C1:=4*x^2-2*x+1
  have hc0 : C0≤2*x^2 := by dsimp [C0];omega
  have hc1 : C1≤4*x^2 := by dsimp [C1];omega
  have hp:=mul_le_mul_of_nonneg_left htx (show 0≤x-1 by omega)
  have hxs : 0≤x*(x-4) := mul_nonneg hx0.le (by omega)
  have hd0 : x^2≤(x-1)*t-C0 := by dsimp [C0];nlinarith only [hp,hxs,hx]
  have hd1 : 2*x^2≤2*(x-1)*t-C1 := by dsimp [C1];nlinarith only [hp,hxs,hx]
  have hgId : 2*x*G x y z t w=y*(z*((x-1)*t-C0)-C0)-2*x^2 := by
    dsimp [G,K,A,L,C0]
    linear_combination -(1+z+z*t+x*z*t)*hw
  have hgpId : 2*x*Gp x y z t w=
      y*(z*(2*(x-1)*t-C1)-C1)-4*x^2-2*x := by
    dsimp [Gp,G,K,A,L,H,C1]
    linear_combination (-2*(1+z+z*t+x*z*t)+z+1)*hw
  have hgLower : x^2*(y*(z-2)-2)≤2*x*G x y z t w := by
    have h0:=mul_le_mul_of_nonneg_left hd0 (show 0≤z by omega)
    have h1:=mul_le_mul_of_nonneg_left (show z*x^2-2*x^2≤z*((x-1)*t-C0)-C0 by
      nlinarith only [h0,hc0]) (show 0≤y by omega)
    nlinarith only [hgId,h1]
  have hgpLower : 2*x^2*(y*(z-2)-2)-2*x≤2*x*Gp x y z t w := by
    have h0:=mul_le_mul_of_nonneg_left hd1 (show 0≤z by omega)
    have h1:=mul_le_mul_of_nonneg_left (show z*(2*x^2)-4*x^2≤z*(2*(x-1)*t-C1)-C1 by
      nlinarith only [h0,hc1]) (show 0≤y by omega)
    nlinarith only [hgpId,h1]
  have hunit : 2≤y*(z-2)-2 := by
    have hp:=mul_le_mul_of_nonneg_left (show 30≤z-2 by omega) hy0.le
    nlinarith only [hp,hy8]
  have hgl : 0<G x y z t w := by
    have hpos : 0<x^2*(y*(z-2)-2) := mul_pos (sq_pos_of_pos hx0) (by omega)
    by_contra hn
    have hp:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*x by omega)
      (show G x y z t w≤0 by omega)
    linarith only [hp,hgLower,hpos]
  have hgpl : 0<Gp x y z t w := by
    have hp:=mul_le_mul_of_nonneg_left hunit (show 0≤2*x^2 by positivity)
    have hpos : 0<2*x^2*(y*(z-2)-2)-2*x := by nlinarith only [hp,hxs,hx]
    by_contra hn
    have hnonpos:=mul_nonpos_of_nonneg_of_nonpos (show 0≤2*x by omega)
      (show Gp x y z t w≤0 by omega)
    linarith only [hnonpos,hgpLower,hpos]
  have oldSlack : x*(K y z t-1-2*G x y z t w)=
      x*(2*x-1)*y*(z+1)+2*x^2+y*z*t+y*z+y := by
    dsimp [K,G,A,L]
    linear_combination (1+z+z*t+x*z*t)*hw
  have newSlack : x*(SW y z t-1-2*(Gp x y z t w+A x y z))=
      x*(2*x-1)*y*(z+1)+2*x^2+2*y*z*t+y*z+y := by
    dsimp [SW,Gp,G,K,A,L,H]
    linear_combination (2*(1+z+z*t+x*z*t)-z-1)*hw
  have ho : 0<x*(K y z t-1-2*G x y z t w) := by rw [oldSlack];positivity
  have hn : 0<x*(SW y z t-1-2*(Gp x y z t w+A x y z)) := by rw [newSlack];positivity
  have hA : 0<A x y z := by dsimp [A];positivity
  have hu : 2*G x y z t w≤K y z t-1 := by
    by_contra hh
    have hp:=mul_nonpos_of_nonneg_of_nonpos hx0.le
      (show K y z t-1-2*G x y z t w≤0 by omega)
    omega
  have hv : 2*(Gp x y z t w+A x y z)≤SW y z t-1 := by
    by_contra hh
    have hp:=mul_nonpos_of_nonneg_of_nonpos hx0.le
      (show SW y z t-1-2*(Gp x y z t w+A x y z)≤0 by omega)
    omega
  exact ⟨⟨by omega,hu⟩,⟨by omega,by omega⟩,⟨by omega,hv⟩⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
