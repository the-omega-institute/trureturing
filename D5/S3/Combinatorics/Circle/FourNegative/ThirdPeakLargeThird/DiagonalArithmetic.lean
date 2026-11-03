/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/DiagonalArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Actual paid-bit ceiling decomposition and all diagonal scalar windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic

/-! ThirdPeakLargeThird: DiagonalArithmetic. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open private A B L K H SU SV SW window ceilDiv quotient remainder ceil_bounds
  ceil_unique ceil_le base_positive from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic

private theorem corrected_polynomial (u : ℤ) :
    8*(u+4)^3-7*(u+4)^2-23*(u+4)-3=8*u^3+89*u^2+305*u+305 := by ring

private theorem diagonal_estimates (x z : ℤ) (hx : 4≤x) (hz : 16*x≤z) :
    2*x^3≤B x x (2*x) ∧ B x x (2*x)≤3*x^3 ∧
    SU x x (2*x)≤6*x^3 ∧
    4*x^3+2*x^2+3*x≤6*x^3 ∧ 4*B x x (2*x)+z<A x x z := by
  have hx0 : 0≤x-4 := by omega
  have hpoly : 0<x^3-2*x^2-2*x-1 := by
    have he : x^3-2*x^2-2*x-1=(x-4)^3+10*(x-4)^2+30*(x-4)+23 := by ring
    rw [he]; positivity
  have hs : 0<2*x^2-2*x-3 := by
    have he : 2*x^2-2*x-3=2*(x-4)^2+14*(x-4)+21 := by ring
    rw [he]; positivity
  have hxs : 0<x*(2*x^2-2*x-3) := by positivity
  have hcrit : 0<8*x^3-7*x^2-23*x-3 := by
    have hh := corrected_polynomial (x-4)
    have hpos : 0<8*(x-4)^3+89*(x-4)^2+305*(x-4)+305 := by positivity
    have he : x-4+4=x := by ring
    rw [he] at hh
    omega
  have hmargin : A x x z-4*B x x (2*x)-z=
      (x^2-1)*(z-16*x)+(8*x^3-7*x^2-23*x-3) := by dsimp [A,B]; ring
  have hxx : 0≤x^2-1 := by nlinarith only [hx,sq_nonneg (x-1)]
  have hp := mul_nonneg hxx (show 0≤z-16*x by omega)
  have hlower : 0≤2*x+2*x^2+1 := by positivity
  dsimp [B,SU] at *
  refine ⟨by nlinarith only [hlower],by nlinarith only [hpoly],
    by nlinarith only [hpoly],by nlinarith only [hxs],by omega⟩

private theorem payment_remainder (x p : ℤ) (hx : 4≤x) (hp : 1≤p) :
    let bb := B x x (2*x)
    let num := 2*p*(2*x+1)+1-bb
    let q := ceilDiv num (2*bb)
    0≤q ∧ q<p := by
  dsimp only
  let bb := B x x (2*x)
  let num := 2*p*(2*x+1)+1-bb
  have hb : 0<bb := by dsimp [bb,B]; positivity
  have hc : 0<bb-4*x-3 := by
    have he : bb-4*x-3=2*(x+1)*(x^2-1) := by dsimp [bb,B]; ring
    have hx2 : 0<x^2-1 := by nlinarith only [hx,sq_nonneg (x-4)]
    rw [he]; positivity
  have hcoef : 0<bb-2*x-1 := by omega
  have hmul := mul_nonneg (show 0≤p-1 by omega) hcoef.le
  have hn : -bb<num := by
    have hh : 0<2*p*(2*x+1) := by positivity
    dsimp [num]
    omega
  have hupper : num≤(p-1)*(2*bb) := by dsimp [num]; nlinarith only [hc,hmul]
  have qb := ceil_bounds num (2*bb) (by omega)
  have qcap := ceil_le num (2*bb) (p-1) (by omega) hupper
  have qnon : 0≤ceilDiv num (2*bb) := by
    by_contra hnq
    have hm := mul_le_mul_of_nonneg_right (show ceilDiv num (2*bb)≤-1 by omega) (show 0≤2*bb by omega)
    nlinarith only [hm,qb.2,hn,hb]
  change 0≤ceilDiv num (2*bb) ∧ ceilDiv num (2*bb)<p
  exact ⟨qnon,by omega⟩

private theorem payment_decomposition (x z p : ℤ)
    (hx : 4≤x) (hp : 1≤p) (hz : z=4*p*x^3) :
    ∃ q : ℤ, 0≤q ∧ q<p ∧ quotient x x z (2*x)=p*(2*x^2-1)+q := by
  let bb := B x x (2*x)
  let num := 2*p*(2*x+1)+1-bb
  let q := ceilDiv num (2*bb)
  have hb : 0<bb := by dsimp [bb,B]; positivity
  have qr := payment_remainder x p hx hp
  change 0≤q ∧ q<p at qr
  have bounds := ceil_bounds num (2*bb) (by omega)
  have identity : L x z (2*x)-bb=p*(2*x^2-1)*(2*bb)+num := by
    rw [hz]; dsimp [bb,num,L,B]; ring
  have qeq : quotient x x z (2*x)=p*(2*x^2-1)+q := by
    apply ceil_unique _ _ _ (by change 0<2*bb; omega)
    change (p*(2*x^2-1)+q-1)*(2*bb)<L x z (2*x)-bb ∧
      L x z (2*x)-bb≤(p*(2*x^2-1)+q)*(2*bb)
    rw [identity]
    constructor <;> nlinarith only [bounds.1,bounds.2]
  exact ⟨q,qr.1,qr.2,qeq⟩

set_option maxHeartbeats 1200000 in
private theorem diagonal_windows (x z p : ℤ)
    (hx : 4≤x) (hz : 16*x≤z) (hp : 0≤p)
    (hbranch : (p=0 ∧ z≤2*x^3) ∨ (1≤p ∧ z=4*p*x^3)) :
    window (B x x (2*x)+L x z (2*x)-2*A x x z) (L x z (2*x)) ∧
    window (SU x x (2*x)+SV x z (2*x)-4*A x x z) (SV x z (2*x)) ∧
    window (B x x (2*x)-L x z (2*x)+2*K x z (2*x)-2*A x x z+2*p*B x x (2*x))
      (K x z (2*x)) ∧
    window (SU x x (2*x)-SV x z (2*x)+2*SW x z (2*x)-2*A x x z+2*p*SU x x (2*x))
      (SW x z (2*x)) := by
  have hz0 : 0<z := by omega
  have hx0 : 0≤x := by omega
  have est := diagonal_estimates x z hx hz
  obtain ⟨hApos,hBpos,hLpos,hKpos,hSUpos,hSVpos,hSWpos,hHpos⟩ :=
    base_positive x x z (2*x) hx hx (by omega) (by omega)
  have ho1 : 0<B x x (2*x)+L x z (2*x)-2*A x x z := by
    have he : B x x (2*x)+L x z (2*x)-2*A x x z=
        2+(2*x-2)*(1+x+x^2)+(1+2*x)*z := by dsimp [B,L,A]; ring
    have hh : 0≤2*x-2 := by omega
    rw [he]; positivity
  have hn1 : 0<SU x x (2*x)+SV x z (2*x)-4*A x x z := by
    have he : SU x x (2*x)+SV x z (2*x)-4*A x x z=
        2+(4*x-4)*(1+x+x^2)+(1+4*x)*z := by dsimp [SU,SV,B,L,A]; ring
    have hh : 0≤4*x-4 := by omega
    rw [he]; positivity
  let E := 2*x^3+2*x-z+2*p*B x x (2*x)
  let EP := 4*x^3+4*x+2*x^2+(2*x^2-2*x-1)*z+2*p*SU x x (2*x)
  have oldeq : B x x (2*x)-L x z (2*x)+2*K x z (2*x)-2*A x x z+2*p*B x x (2*x)=E := by
    dsimp [B,L,K,A,E]; ring
  have neweq : SU x x (2*x)-SV x z (2*x)+2*SW x z (2*x)-2*A x x z+2*p*SU x x (2*x)=EP := by
    dsimp [SU,SV,SW,B,L,K,H,A,EP]; ring
  have hcube : 0<x^3 := by positivity
  have hc0 : 2*x^3+2*x≤4*x^3 := by
    have hh : 0≤x*(x-1)*(x+1) := by
      have hx1 : 0≤x-1 := by omega
      positivity
    nlinarith only [hh]
  have hk : 2*z≤K x z (2*x)-1 := by
    have he : K x z (2*x)-1-2*z=x+(x-2)*z+2*x^2*z := by dsimp [K]; ring
    have hx2 : 0≤x-2 := by omega
    have hh : 0≤x+(x-2)*z+2*x^2*z := by positivity
    omega
  have oldwin : 0≤E ∧ E≤K x z (2*x)-1 := by
    rcases hbranch with ⟨hp0,hsmall⟩|⟨hp1,hlarge⟩
    · dsimp only [E]
      simp only [hp0,zero_mul,add_zero]
      have hzbound : 4*x^3≤2*x^2*z := by
        have hmul := mul_nonneg (show 0≤z-16*x by omega) (show 0≤x^2 by positivity)
        nlinarith only [hmul,hcube]
      have hK : 2*x^2*z≤K x z (2*x)-1 := by
        dsimp [K]
        have hh : 0≤x*z := by positivity
        nlinarith only [hh,hx]
      constructor <;> nlinarith only [hx,hsmall,hc0,hzbound,hK,hz0]
    · have hlo := mul_le_mul_of_nonneg_left est.1 (show 0≤2*p by omega)
      have hhi := mul_le_mul_of_nonneg_left est.2.1 (show 0≤4*p by omega)
      have hbase : 4*x^3≤z := by
        rw [hlarge]
        have hh := mul_nonneg (show 0≤p-1 by omega) hcube.le
        nlinarith only [hh]
      dsimp [E]
      constructor <;> nlinarith only [hlo,hhi,hlarge,hbase,hc0,hk,hz0,hx,hcube]
  have hpay : 4*p*x^3≤z := by
    rcases hbranch with ⟨rfl,hs⟩|⟨hp1,he⟩
    · simpa only [zero_mul,mul_zero] using hz0.le
    · omega
  have hpSU := mul_le_mul_of_nonneg_left est.2.2.1 (show 0≤2*p by omega)
  have hpaid : 2*p*SU x x (2*x)≤3*z := by nlinarith only [hpSU,hpay]
  have hcost : 4*x^3+2*x^2+3*x≤x^2*z := by
    have hh := mul_nonneg (show 0≤z-16*x by omega) (show 0≤x^2 by positivity)
    nlinarith only [hh,est.2.2.2.1,hcube]
  have hcoeff : 0<2*x^2-2*x-1 := by
    have he : 2*x^2-2*x-1=2*(x-4)^2+14*(x-4)+23 := by ring
    have hx4 : 0≤x-4 := by omega
    rw [he]; positivity
  have hn2 : 0<EP := by dsimp [EP]; positivity
  have hslack : SW x z (2*x)-1-EP=
      (2*x^2+3*x+1)*z-(4*x^3+2*x^2+3*x)-2*p*SU x x (2*x) := by
    dsimp [EP,SW,K,H]; ring
  have hres : 0<(x^2+3*x-2)*z := by
    have hh : 0<x^2+3*x-2 := by nlinarith only [hx,sq_nonneg (x-1)]
    positivity
  have hnupper : EP≤SW x z (2*x)-1 := by
    nlinarith only [hslack,hcost,hpaid,hres]
  dsimp [window]
  refine ⟨⟨ho1.le,by omega⟩,⟨hn1.le,?_⟩,?_,?_⟩
  · dsimp [SU] at *; omega
  · rw [oldeq]; exact oldwin
  · rw [neweq]; exact ⟨hn2.le,hnupper⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
