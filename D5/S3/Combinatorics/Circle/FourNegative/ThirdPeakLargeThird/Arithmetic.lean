/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Unbounded integer ceiling and doubled terminal windows for Regions II and III. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! ThirdPeakLargeThird: Arithmetic. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird

private def A (x y z : ℤ) : ℤ := 1+x+x*y+x*y*z
private def B (x y t : ℤ) : ℤ := 1+t+x*t+x*y*t
private def L (x z t : ℤ) : ℤ := 1+z+z*t+x*z*t
private def K (y z t : ℤ) : ℤ := 1+y+y*z+y*z*t
private def H (y z : ℤ) : ℤ := 1+y+y*z
private def SU (x y t : ℤ) : ℤ := 2*B x y t-1
private def SV (x z t : ℤ) : ℤ := 2*L x z t-1-z
private def SW (y z t : ℤ) : ℤ := 2*K y z t-H y z
private def window (D T : ℤ) : Prop := 0≤D ∧ D≤T-1
private def ceilDiv (n den : ℤ) : ℤ := (n+den-1)/den
private def quotient (x y z t : ℤ) : ℤ := ceilDiv (L x z t-B x y t) (2*B x y t)
private def remainder (x y z t v : ℤ) : ℤ := (2*v+1)*B x y t-L x z t

private theorem ceil_bounds (n den : ℤ) (hd : 0<den) :
    (ceilDiv n den-1)*den<n ∧ n≤ceilDiv n den*den := by
  have hr := Int.emod_nonneg (n+den-1) (by omega : den≠0)
  have hs := Int.emod_lt_of_pos (n+den-1) hd
  have he := Int.ediv_mul_add_emod (n+den-1) den
  dsimp [ceilDiv]
  nlinarith only [hr,hs,he]

private theorem ceil_unique (n den q : ℤ) (hd : 0<den)
    (hq : (q-1)*den<n ∧ n≤q*den) : ceilDiv n den=q := by
  have hh := ceil_bounds n den hd
  by_contra hn
  rcases lt_or_gt_of_ne hn with h|h
  · have hm := mul_le_mul_of_nonneg_right (show ceilDiv n den≤q-1 by omega) hd.le
    nlinarith only [hm,hh.2,hq.1]
  · have hm := mul_le_mul_of_nonneg_right (show q≤ceilDiv n den-1 by omega) hd.le
    nlinarith only [hm,hh.1,hq.2]

private theorem ceil_le (n den q : ℤ) (hd : 0<den) (hq : n≤q*den) :
    ceilDiv n den≤q := by
  have hh := ceil_bounds n den hd
  by_contra hn
  have hm := mul_le_mul_of_nonneg_right (show q≤ceilDiv n den-1 by omega) hd.le
  nlinarith only [hm,hh.1,hq]

private theorem base_positive (x y z t : ℤ)
    (hx : 4≤x) (hy : 4≤y) (hz : 1≤z) (ht : 1≤t) :
    1≤A x y z ∧ 1≤B x y t ∧ 1≤L x z t ∧ 1≤K y z t ∧
    1≤SU x y t ∧ 1≤SV x z t ∧ 1≤SW y z t ∧ 1≤H y z := by
  dsimp [A,B,L,K,SU,SV,SW,H]
  repeat' constructor
  all_goals apply sub_nonneg.mp
  all_goals ring_nf
  all_goals positivity

private theorem large_head (x y z t : ℤ)
    (hy : 4≤y) (hyx : y≤x) (hxt : x≤t) (htz : 8*t≤z) :
    4*B x y t+z<A x y z ∧ B x y t<L x z t := by
  have hx : 4≤x := by omega
  have ht : 4≤t := by omega
  have hz : 32≤z := by omega
  have hxy : 0<x*y-x-3 := by
    have hp := mul_nonneg (show 0≤x by omega) (show 0≤y-4 by omega)
    nlinarith only [hp,hx]
  have hs : 0≤x*y-1 := by nlinarith only [hxy,hx]
  have hmargin : A x y z-4*B x y t-z=
      (z-8*t)*(x*y-1)+4*t*(x*y-x-3)+(x+x*y-3) := by dsimp [A,B]; ring
  have htail : 0<x+x*y-3 := by nlinarith only [hxy,hx]
  have hprod := mul_nonneg (show 0≤z-8*t by omega) hs
  have hprod' : 0<4*t*(x*y-x-3) := by positivity
  have hC : 0<8*(1+t+x*t)-(1+x+x*y) := by
    have he : 8*(1+t+x*t)-(1+x+x*y)=
        7+(8*t-x)+7*x*t+x*(t-y) := by ring
    rw [he]
    have ht' : 0<8*t-x := by omega
    have hty : 0≤t-y := by omega
    positivity
  have hdiff : L x z t-B x y t=
      (z-8*t)*(1+t+x*t)+t*(8*(1+t+x*t)-(1+x+x*y)) := by dsimp [L,B]; ring
  have hp : 0≤(z-8*t)*(1+t+x*t) := by positivity
  have hp' : 0<t*(8*(1+t+x*t)-(1+x+x*y)) := by positivity
  exact ⟨by omega,by omega⟩

private theorem quotient_remainder (x y z t : ℤ) (hB : 0<B x y t) :
    0≤remainder x y z t (quotient x y z t) ∧
      remainder x y z t (quotient x y z t)<2*B x y t := by
  have hh := ceil_bounds (L x z t-B x y t) (2*B x y t) (by omega)
  dsimp [quotient,remainder] at *
  constructor <;> nlinarith only [hh.1,hh.2]

private theorem third_windows (x y z t v : ℤ)
    (hB : 0<B x y t) (hA : 4*B x y t+z<A x y z)
    (hv : 0≤v) (hstock : 2*v≤z-2)
    (hD : 0≤remainder x y z t v ∧ remainder x y z t v<2*B x y t) :
    window (remainder x y z t v) (A x y z) ∧
    window (2*remainder x y z t v+z-2*v) (A x y z) := by
  dsimp [window]
  constructor
  · constructor <;> omega
  · constructor <;> omega

set_option maxHeartbeats 1200000 in
private theorem regionII_windows (x y z t : ℤ)
    (hy : 4≤y) (hyx : 2*y≤x) (hxt : 2*x≤t) (htz : 8*t≤z) :
    window (B x y t+K y z t-2*A x y z) (K y z t) ∧
    window (SU x y t+SW y z t-4*A x y z) (SW y z t) ∧
    window (B x y t+L x z t-K y z t-A x y z) (L x z t) ∧
    window (SU x y t+SV x z t-SW y z t-3*A x y z) (SV x z t) := by
  have hx : 4≤x := by omega
  have ht : 4≤t := by omega
  have hz : 1≤z := by omega
  obtain ⟨hApos,hBpos,hLpos,hKpos,hSUpos,hSVpos,hSWpos,hHpos⟩ :=
    base_positive x y z t hx hy hz (by omega)
  have big := (large_head x y z t hy (by omega) (by omega) htz).1
  have hz4 : 0≤z-4*x := by omega
  have ht2 : 0≤t-2*x := by omega
  have hxy : 0≤x-2*y := by omega
  have hxy' : 0≤x-y := by omega
  have hty : 0≤t-y := by omega
  have hn1 : 0<SU x y t+SW y z t-4*A x y z := by
    have he : SU x y t+SW y z t-4*A x y z=
        2*(t-2*x)+2*t*x*(1+y)+(y-2)+y*(z-4*x)+y*z*(2*t-4*x) := by
      dsimp [SU,SW,B,K,H,A]; ring
    rw [he]
    have hlast : 0≤2*t-4*x := by omega
    have hy' : 0<y-2 := by omega
    positivity
  have ho1 : 0<B x y t+K y z t-2*A x y z := by
    have he : SU x y t+SW y z t-4*A x y z=
        2*(B x y t+K y z t-2*A x y z)-H y z-1 := by dsimp [SU,SW]; ring
    omega
  let D := B x y t+L x z t-K y z t-2*A x y z
  have hd : 0<D := by
    have hconst : 0<t*(1+x+x*y)-2*x-2*x*y-y-1 := by
      have he : t*(1+x+x*y)-2*x-2*x*y-y-1=
          (t-2*x)*(1+x+x*y)+(2*x^2-y-1)+2*x*y*(x-1) := by ring
      have hs : 0<2*x^2-y-1 := by nlinarith only [hx,hyx,sq_nonneg (x-1)]
      have hx' : 0≤x-1 := by omega
      rw [he]; positivity
    have hcoeff : 0<t*(x-y)-2*x*y+t+1-y := by
      have he : t*(x-y)-2*x*y+t+1-y=
          (t-2*x)*(x-y)+2*x*(x-2*y)+(t-y)+1 := by ring
      rw [he]; positivity
    have he : D=(t*(1+x+x*y)-2*x-2*x*y-y-1)+
        z*(t*(x-y)-2*x*y+t+1-y) := by dsimp [D,A,B,L,K]; ring
    rw [he]; positivity
  have hh : 0<H y z-z-2 := by
    have he : H y z-z-2=(y-1)*z+(y-1) := by dsimp [H]; ring
    have hy' : 0<y-1 := by omega
    rw [he]; positivity
  have ho2 : 0<B x y t+L x z t-K y z t-A x y z := by dsimp [D] at hd; omega
  have hn2 : 0<SU x y t+SV x z t-SW y z t-3*A x y z := by
    have he : SU x y t+SV x z t-SW y z t-3*A x y z=
        2*D+A x y z+(H y z-z-2) := by dsimp [D,SU,SV,SW]; ring
    omega
  dsimp [window]
  refine ⟨⟨ho1.le,?_⟩,⟨hn1.le,?_⟩,⟨ho2.le,?_⟩,⟨hn2.le,?_⟩⟩
  · omega
  · dsimp [SU] at *; omega
  · omega
  · dsimp [SU] at *; omega

set_option maxHeartbeats 1200000 in
private theorem regionIII_windows (x z t : ℤ)
    (hx : 4≤x) (ht : 4*x≤t) (hz : 8*t≤z) :
    window (B x x t+L x z t-2*A x x z) (L x z t) ∧
    window (SU x x t+SV x z t-4*A x x z) (SV x z t) ∧
    window (B x x t-L x z t+2*K x z t-2*A x x z) (K x z t) ∧
    window (SU x x t-SV x z t+2*SW x z t-4*A x x z) (SW x z t) := by
  have hxpos : 0<x := by omega
  have hzpos : 0<z := by omega
  have ht' : 0≤t-4*x := by omega
  have hz' : 0≤z-2 := by omega
  have hx' : 0≤x-4 := by omega
  have hx1 : 0<x-1 := by omega
  obtain ⟨hApos,hBpos,hLpos,hKpos,hSUpos,hSVpos,hSWpos,hHpos⟩ :=
    base_positive x x z t hx hx (by omega) (by omega)
  have big := (large_head x x z t hx (by omega) (by omega) hz).1
  have hR : 0<2*L x z t-4*A x x z-z := by
    have he : 2*L x z t-4*A x x z-z=
        (z-2)*(2*(t-4*x)*(x+1)+4*x^2+8*x+1)+
        4*(t-4*x)*(x+1)+4*x^2+12*x := by dsimp [L,A]; ring
    rw [he]; positivity
  have ho1 : 0<B x x t+L x z t-2*A x x z := by omega
  have hn1 : 0<SU x x t+SV x z t-4*A x x z := by dsimp [SU,SV]; omega
  have ho2 : 0<B x x t-L x z t+2*K x z t-2*A x x z := by
    have he : B x x t-L x z t+2*K x z t-2*A x x z=
        (t-4*x)*(1+x+x^2)+4*x+2*x^2+4*x^3+
        z*((t-4*x)*(x-1)+(x-4)*(2*x+6)+23) := by dsimp [B,L,K,A]; ring
    rw [he]; positivity
  have hn2 : 0<SU x x t-SV x z t+2*SW x z t-4*A x x z := by
    have he : SU x x t-SV x z t+2*SW x z t-4*A x x z=
        2*(t-4*x)*(1+x+x^2)+8*x^3+4*x^2+(6*x-2)+
        z*(2*(t-4*x)*(x-1)+(x-4)*(4*x+10)+39) := by
      dsimp [SU,SV,SW,B,L,K,H,A]; ring
    have hs : 0<6*x-2 := by omega
    rw [he]; positivity
  have hlk : 0<L x z t-K x z t := by
    have he : L x z t-K x z t=(z-1)*(t+1-x)+(t-2*x)+1 := by dsimp [L,K]; ring
    have hz1 : 0≤z-1 := by omega
    have ht1 : 0≤t+1-x := by omega
    have ht2 : 0≤t-2*x := by omega
    rw [he]; positivity
  have hh : 0<H x z-z-1 := by
    have he : H x z-z-1=x+(x-1)*z := by dsimp [H]; ring
    rw [he]; positivity
  have upper2 : SW x z t-1-(SU x x t-SV x z t+2*SW x z t-4*A x x z)=
      2*(L x z t-K x z t)+(H x z-z-1)+4*A x x z-2*B x x t := by
    dsimp [SU,SV,SW]; ring
  dsimp [window]
  refine ⟨⟨ho1.le,by omega⟩,⟨hn1.le,?_⟩,⟨ho2.le,by omega⟩,⟨hn2.le,?_⟩⟩
  · dsimp [SU] at *; omega
  · omega

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
