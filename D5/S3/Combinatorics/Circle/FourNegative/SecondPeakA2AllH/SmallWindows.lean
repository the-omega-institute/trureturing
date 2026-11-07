/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallWindows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallWindows
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Corrected simultaneous window closure. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.TableData
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.IntegerSelector
import Mathlib.Tactic

/-! Corrected simultaneous window closure. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
open SecondPeakHighD

/-- The corrected interval uses the actual second-window charge. -/
def smallDelta (p q h M : ℤ) : ℤ := 5*M-(Y 4 p q h-8*h*p)

/-- Four exact slacks, including the late-fresh subtraction in `newEnds`. -/
def smallFirstSlacks (p q h v m M : ℤ) (before : Bool) : Fin 4 → ℤ :=
  ![oldEnds 4 p q h v m M 0,
    A 4 p q h-1-oldEnds 4 p q h v m M 0,
    newEnds 4 p q h v m M before 0,
    A 4 p q h-1-newEnds 4 p q h v m M before 0]

/-- A dyadic predecessor supplies properness as well as the bit inclusion. -/
theorem small_proper_predecessor (k n m : ℕ) (hn : 2≤n) (hm : m<2^k) :
    Submask m (2^k*n-1) ∧ m<2^k*n-1 := by
  have hp : 1≤(2:ℕ)^k := by have := Nat.two_pow_pos k; omega
  have hmul := Nat.mul_le_mul_left (2^k) hn
  have hprod : 2^k+1≤2^k*n := by omega
  exact ⟨submask_predecessor k n m (by omega) hm,by omega⟩

/-- The two later old windows and both charged new windows, with all stocks.
The lower endpoint is 4h, never the invalid arbitrary-h bound 2h. -/
theorem finish_small_bounds (p q h v m M : ℤ) (before : Bool)
    (hp : 4≤p) (hq : 2≤q) (hh : 4≤h)
    (hv0 : 1≤v) (hv : 2*v≤T 4 p q)
    (hd0 : 4*h≤smallDelta p q h M) (hd1 : smallDelta p q h M≤4*h*p)
    (hf : ∀ r : Fin 4, 0≤smallFirstSlacks p q h v m M before r) :
    rowBounds 4 p q h v m M before := by
  have hp0 : 0<p := by omega
  have hq0 : 0<q := by omega
  have hh0 : 0<h := by omega
  let z := Z (4:ℤ) q
  let t := T (4:ℤ) p q
  let y := Y (4:ℤ) p q h
  let Q := z+1
  let r := B (4:ℤ) p q h-K 4 p q h+M*L 4 p q
  have hz : 8≤z := by dsimp [z,Z]; omega
  have hz0 : 0<z := by omega
  have ht : 4*z≤t := by
    have := mul_nonneg (show 0≤p-4 by omega) (show 0≤z by omega)
    dsimp [t,z,T,Z] at *
    nlinarith only [this]
  have ht0 : 0<t := by omega
  have hy : 2*t≤y := by
    have := mul_nonneg (show 0≤h-1 by omega) ht0.le
    dsimp [y,Y]
    change 2*t≤2*h*t
    nlinarith only [this]
  have hy0 : 0<y := by omega
  have hQ : 0<Q := by dsimp [Q]; omega
  have hL : 0<L (4:ℤ) p q := by dsimp [L,Z,T]; positivity
  have hbase : 0≤Y (4:ℤ) p q h-8*h*p := by
    have he : Y (4:ℤ) p q h-8*h*p=8*h*p*(q-1) := by dsimp [Y,T]; ring
    rw [he]
    exact mul_nonneg (by positivity) (by omega)
  have hM0 : 0≤M := by dsimp [smallDelta] at hd0; nlinarith only [hd0,hbase,hh]
  have hhp : 0≤h*p := by positivity
  have hMlt : 2*M<y := by
    dsimp [smallDelta] at hd1
    change 5*M-(y-8*h*p)≤4*h*p at hd1
    nlinarith only [hd1,hy0,hhp]
  have hEven : y=2*(h*t) := by dsimp [y,t,Y]; ring
  have hMcap : 2*M≤Y 4 p q h-2 := by
    change 2*M≤y-2
    rw [hEven] at hMlt ⊢
    omega
  have hYM : 0≤y-M := by omega
  have hpoly : 0<3*z^2-4*z-2 := by
    have he : 3*z^2-4*z-2=3*(z-8)^2+44*(z-8)+158 := by ring
    rw [he]
    have hz0 : 0≤z-8 := by omega
    positivity
  have hlo : 0<4*h*(p*(3*z^2-4*z-2)+Q)+25*p*z := by positivity
  have hlowid : 5*r=(smallDelta p q h M-4*h)*L 4 p q+
      (4*h*(p*(3*z^2-4*z-2)+Q)+25*p*z) := by
    dsimp [r,smallDelta,Q,z,A,B,K,L,Y,Z,T]
    ring
  have hlowprod := mul_nonneg (show 0≤smallDelta p q h M-4*h by omega) hL.le
  have hr : 0≤r := by nlinarith only [hlowid,hlowprod,hlo]
  have hh12 : 0≤12*h-25 := by omega
  have hu : 0<p*(8*h*z^2+(12*h-25)*z+4*h) := by positivity
  have hcoeff : 0≤Q+10*p*z^2 := by positivity
  have huprod := mul_nonneg (show 0≤4*h*p-smallDelta p q h M by omega) hcoeff
  have hupid : 5*(B 4 p q h-1-2*r-(y-M)*Q)=
      (4*h*p-smallDelta p q h M)*(Q+10*p*z^2)+
      p*(8*h*z^2+(12*h-25)*z+4*h) := by
    dsimp [r,smallDelta,y,Q,z,A,B,K,L,Y,Z,T]
    ring
  have hupper : 0≤B 4 p q h-1-2*r-(y-M)*Q := by
    nlinarith only [hupid,huprod,hu]
  have hcharge := mul_nonneg hYM hQ.le
  have hs2 : oldEnds 4 p q h v m M 1=2*r := by dsimp [oldEnds,r]; ring
  have ht2 : newEnds 4 p q h v m M before 1=4*r+2*(y-M)*Q := by
    dsimp [newEnds,r,y,Q,z,SU,SV,SW,B,K,L,Y,Z,T]
    ring
  have hs2lo : 0≤oldEnds 4 p q h v m M 1 := by rw [hs2]; omega
  have hs2hi : oldEnds 4 p q h v m M 1≤B 4 p q h-1 := by
    rw [hs2]; nlinarith only [hupper,hcharge]
  have ht2lo : 0≤newEnds 4 p q h v m M before 1 := by
    rw [ht2]; nlinarith only [hr,hcharge]
  have ht2hi : newEnds 4 p q h v m M before 1≤SU 4 p q h-1 := by
    rw [ht2]; dsimp [SU]; nlinarith only [hupper]
  have hfactor : 0≤4*y-5*z+4 := by omega
  have hBLid : B 4 p q h-L 4 p q=(4*y-5*z+4)*t+(t-z) := by
    dsimp [y,t,z,B,L,Y,Z,T]; ring
  have hBL : 0≤B 4 p q h-L 4 p q := by
    rw [hBLid]
    exact add_nonneg (mul_nonneg hfactor ht0.le) (by omega)
  have hz8 : 0≤z-8 := by omega
  have hz1 : 0≤z-1 := by omega
  have hs3hiid : K 4 p q h-1-oldEnds 4 p q h v m M 2=
      y*t*(z-8)+y*Q+10*t*(z-1)+2*z := by
    dsimp [oldEnds,y,t,z,Q,B,K,L,Y,Z,T]; ring
  have ht3hiid : SW 4 p q h-1-newEnds 4 p q h v m M before 2=
      2*y*t*(z-8)+y*Q+20*t*(z-1)+2*z := by
    dsimp [newEnds,y,t,z,Q,SU,SV,SW,B,K,L,Y,Z,T]; ring
  have hs3lo : 0≤oldEnds 4 p q h v m M 2 := by
    change 0≤2*B 4 p q h-2*L 4 p q
    linarith only [hBL]
  have ht3lo : 0≤newEnds 4 p q h v m M before 2 := by
    have he : newEnds 4 p q h v m M before 2=
        2*oldEnds 4 p q h v m M 2+2*z := by
      dsimp [oldEnds,newEnds,SU,SV,z,Z]; ring
    rw [he]; positivity
  have hs3hi : oldEnds 4 p q h v m M 2≤K 4 p q h-1 := by
    have hn : 0≤K 4 p q h-1-oldEnds 4 p q h v m M 2 := by
      rw [hs3hiid]; positivity
    omega
  have ht3hi : newEnds 4 p q h v m M before 2≤SW 4 p q h-1 := by
    have hn : 0≤SW 4 p q h-1-newEnds 4 p q h v m M before 2 := by
      rw [ht3hiid]; positivity
    omega
  refine ⟨?_,hv0,hv,hM0,hMcap⟩
  intro r'
  fin_cases r'
  · have h0 := hf 0
    have h1 := hf 1
    have h2 := hf 2
    have h3 := hf 3
    dsimp [smallFirstSlacks] at h0 h1 h2 h3
    change 0≤oldEnds 4 p q h v m M 0 ∧
      oldEnds 4 p q h v m M 0≤A 4 p q h-1 ∧
      0≤newEnds 4 p q h v m M before 0 ∧
      newEnds 4 p q h v m M before 0≤A 4 p q h-1
    exact ⟨h0,by omega,h2,by omega⟩
  · exact ⟨hs2lo,hs2hi,ht2lo,ht2hi⟩
  · exact ⟨hs3lo,hs3hi,ht3lo,ht3hi⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH
