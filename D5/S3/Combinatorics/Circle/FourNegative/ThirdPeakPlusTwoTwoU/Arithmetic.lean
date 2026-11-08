/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Polynomial slack certificates for the two-U plus-two scalar windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU

private def A (x y t : ℤ) : ℤ := 1+x+x*y+4*x*y*t
private def B (x y t : ℤ) : ℤ := 1+t+x*t+x*y*t
private def L (x y t : ℤ) : ℤ := 1+4*t+4*t*t+4*x*t*t
private def K (x y t : ℤ) : ℤ := 1+y+4*y*t+4*y*t*t
private def SU (x y t : ℤ) : ℤ := 2*B x y t-1
private def SV (x y t : ℤ) : ℤ := 2*L x y t-1-4*t
private def SW (x y t : ℤ) : ℤ := 2*K x y t-1-y-4*y*t
private def oldFirst (x y t u : ℤ) : ℤ := B x y t+K x y t-2*(1+u)*A x y t
private def oldSecond (x y t u : ℤ) : ℤ := B x y t+L x y t-K x y t-(1+2*u)*A x y t
private def newFirst (x y t u : ℤ) : ℤ := SU x y t+SW x y t-4*(1+u)*A x y t
private def newSecond (x y t u : ℤ) : ℤ := SU x y t+SV x y t-SW x y t-(3+4*u)*A x y t
private def D (x y t u v : ℤ) : ℤ := (2*v+1)*B x y t-L x y t-2*u*A x y t
private def window (e h : ℤ) : Prop := 0≤e ∧ e≤h-1
private def firstTwo (x y t u : ℤ) : Prop :=
  window (oldFirst x y t u) (K x y t) ∧
  window (newFirst x y t u) (SW x y t) ∧
  window (oldSecond x y t u) (L x y t) ∧
  window (newSecond x y t u) (SV x y t)

/- The extremal lower (u=2) and upper (u=0) identities plus monotonicity
prove every one of the 24 first-two inequalities, including u=1. -/
set_option maxHeartbeats 2400000 in
private theorem general_firstTwo (x y t : ℤ) (hy : 4≤y) (hx : 2*y≤x) (ht : 8*x≤t)
    (u : ℤ) (hu : 0≤u ∧ u≤2) : firstTwo x y t u := by
  let p := y-4
  have hp : 0≤p := by dsimp [p]; omega
  let q := x-2*y
  let r := t-8*x
  have hq : 0≤q := by dsimp [q]; omega
  have hr : 0≤r := by dsimp [r]; omega
  have c0lo : 0 < oldFirst x y t 2 := by
    have he : oldFirst x y t 2 = 288 * p^3 + 288 * p^2 * q + 82 * p^2 * r + 3540 * p^2 + 72 * p * q^2 + 41 * p * q * r + 2362 * p * q + 4 * p * r^2 + 662 * p * r + 14501 * p + 296 * q^2 + 165 * q * r + 4842 * q + 16 * r^2 + 1337 * r + 19792 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c0hi : 0 < K x y t-1-oldFirst x y t 0 := by
    have he : K x y t-1-oldFirst x y t 0 = 224 * p^3 + 224 * p^2 * q + 14 * p^2 * r + 2660 * p^2 + 56 * p * q^2 + 7 * p * q * r + 1762 * p * q + 110 * p * r + 10516 * p + 216 * q^2 + 27 * q * r + 3458 * q + 215 * r + 13840 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c1lo : 0 < newFirst x y t 2 := by
    have he : newFirst x y t 2 = 576 * p^3 + 576 * p^2 * q + 164 * p^2 * r + 7016 * p^2 + 144 * p * q^2 + 82 * p * q * r + 4692 * p * q + 8 * p * r^2 + 1320 * p * r + 28489 * p + 592 * q^2 + 330 * q * r + 9556 * q + 32 * r^2 + 2658 * r + 38554 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c1hi : 0 < SW x y t-1-newFirst x y t 0 := by
    have he : SW x y t-1-newFirst x y t 0 = 448 * p^3 + 448 * p^2 * q + 28 * p^2 * r + 5320 * p^2 + 112 * p * q^2 + 14 * p * q * r + 3524 * p * q + 220 * p * r + 21032 * p + 432 * q^2 + 54 * q * r + 6916 * q + 430 * r + 27682 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c2lo : 0 < oldSecond x y t 2 := by
    have he : oldSecond x y t 2 = 416 * p^3 + 1440 * p^2 * q + 90 * p^2 * r + 5974 * p^2 + 1128 * p * q^2 + 173 * p * q * r + 12539 * p * q + 4 * p * r^2 + 846 * p * r + 27893 * p + 256 * q^3 + 64 * q^2 * r + 4776 * q^2 + 4 * q * r^2 + 757 * q * r + 27151 * q + 20 * r^2 + 1949 * r + 42608 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c2hi : 0 < L x y t-1-oldSecond x y t 0 := by
    have he : L x y t-1-oldSecond x y t 0 = 1120 * p^3 + 1120 * p^2 * q + 134 * p^2 * r + 13474 * p^2 + 280 * p * q^2 + 67 * p * q * r + 8961 * p * q + 4 * p * r^2 + 1074 * p * r + 54019 * p + 1112 * q^2 + 267 * q * r + 17917 * q + 16 * r^2 + 2151 * r + 72172 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c3lo : 0 < newSecond x y t 2 := by
    have he : newSecond x y t 2 = 704 * p^3 + 2752 * p^2 * q + 172 * p^2 * r + 10474 * p^2 + 2224 * p * q^2 + 342 * p * q * r + 24085 * p * q + 8 * p * r^2 + 1632 * p * r + 50073 * p + 512 * q^3 + 128 * q^2 * r + 9424 * q^2 + 8 * q * r^2 + 1498 * q * r + 52345 * q + 40 * r^2 + 3782 * r + 77754 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have c3hi : 0 < SV x y t-1-newSecond x y t 0 := by
    have he : SV x y t-1-newSecond x y t 0 = 2368 * p^3 + 2368 * p^2 * q + 276 * p^2 * r + 28422 * p^2 + 592 * p * q^2 + 138 * p * q * r + 18915 * p * q + 8 * p * r^2 + 2208 * p * r + 113687 * p + 2352 * q^2 + 550 * q * r + 37759 * q + 32 * r^2 + 4414 * r + 151550 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p,q,r]; ring
    rw [he]
    positivity
  have hx0 : 0≤x := by omega
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have hA : 0≤A x y t := by dsimp [A]; positivity
  have hlow : 0≤(2-u)*A x y t := mul_nonneg (by omega) hA
  have hhigh : 0≤u*A x y t := mul_nonneg hu.1 hA
  unfold firstTwo window
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c0lo ⊢
    nlinarith only [c0lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c0hi ⊢
    nlinarith only [c0hi,hhigh]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c1lo ⊢
    nlinarith only [c1lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c1hi ⊢
    nlinarith only [c1hi,hhigh]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c2lo ⊢
    nlinarith only [c2lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c2hi ⊢
    nlinarith only [c2hi,hhigh]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c3lo ⊢
    nlinarith only [c3lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c3hi ⊢
    nlinarith only [c3hi,hhigh]

set_option maxHeartbeats 2400000 in
private theorem general_aux (x y t : ℤ) (hy : 4≤y) (hx : 2*y≤x) (ht : 8*x≤t) :
    4*t < 4*B x y t-A x y t ∧ 4*B x y t-A x y t < B x y t ∧
    28*B x y t+4*t < 9*A x y t ∧ y*L x y t < 4*t*B x y t ∧
    B x y t < L x y t := by
  let p := y-4
  let q := x-2*y
  let r := t-8*x
  have hp : 0≤p := by dsimp [p]; omega
  have hq : 0≤q := by dsimp [q]; omega
  have hr : 0≤r := by dsimp [r]; omega
  have c0 : 0 < 4*B x y t-A x y t-4*t := by
    have he : 4*B x y t-A x y t-4*t = 126 * p^2 + 127 * p * q + 8 * p * r + 1006 * p + 32 * q^2 + 4 * q * r + 507 * q + 32 * r + 2011 := by
      dsimp [A,B,L,p,q,r]; ring
    rw [he]
    positivity
  have c1 : 0 < B x y t-(4*B x y t-A x y t) := by
    have he : B x y t-(4*B x y t-A x y t) = 32 * p^3 + 32 * p^2 * q + 2 * p^2 * r + 290 * p^2 + 8 * p * q^2 + p * q * r + 161 * p * q + 10 * p * r + 738 * p + 8 * q^2 + q * r + 109 * q + 5 * r + 358 := by
      dsimp [A,B,L,p,q,r]; ring
    rw [he]
    positivity
  have c2 : 0 < 9*A x y t-28*B x y t-4*t := by
    have he : 9*A x y t-28*B x y t-4*t = 256 * p^3 + 256 * p^2 * q + 16 * p^2 * r + 2194 * p^2 + 64 * p * q^2 + 8 * p * q * r + 1161 * p * q + 72 * p * r + 4770 * p + 32 * q^2 + 4 * q * r + 301 * q + 341 := by
      dsimp [A,B,L,p,q,r]; ring
    rw [he]
    positivity
  have c3 : 0 < 4*t*B x y t-y*L x y t := by
    have he : 4*t*B x y t-y*L x y t = 1024 * p^3 + 2048 * p^2 * q + 128 * p^2 * r + 13248 * p^2 + 1280 * p * q^2 + 192 * p * q * r + 17376 * p * q + 4 * p * r^2 + 1148 * p * r + 56895 * p + 256 * q^3 + 64 * q^2 * r + 5376 * q^2 + 4 * q * r^2 + 832 * q * r + 36768 * q + 20 * r^2 + 2548 * r + 81148 := by
      dsimp [A,B,L,p,q,r]; ring
    rw [he]
    positivity
  have c4 : 0 < L x y t-B x y t := by
    have he : L x y t-B x y t = 2016 * p^3 + 3040 * p^2 * q + 254 * p^2 * r + 25184 * p^2 + 1528 * p * q^2 + 255 * p * q * r + 25312 * p * q + 8 * p * r^2 + 2158 * p * r + 104752 * p + 256 * q^3 + 64 * q^2 * r + 6360 * q^2 + 4 * q * r^2 + 1083 * q * r + 52632 * q + 36 * r^2 + 4571 * r + 145088 := by
      dsimp [A,B,L,p,q,r]; ring
    rw [he]
    positivity
  exact ⟨by linarith only [c0],by linarith only [c1],by linarith only [c2],by linarith only [c3],by linarith only [c4]⟩

/- The same extremal argument covers all 16 boundary first-two inequalities. -/
set_option maxHeartbeats 2400000 in
private theorem boundary_firstTwo (x : ℤ) (hx : 8≤x)
    (u : ℤ) (hu : 0≤u ∧ u≤1) : firstTwo x 4 (4*x) u := by
  let p := x-8
  have hp : 0≤p := by dsimp [p]; omega
  have c0lo : 0 < oldFirst x 4 (4*x) 1 := by
    have he : oldFirst x 4 (4*x) 1 = 20 * p^2 + 368 * p + 1666 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c0hi : 0 < K x 4 (4*x)-1-oldFirst x 4 (4*x) 0 := by
    have he : K x 4 (4*x)-1-oldFirst x 4 (4*x) 0 = 108 * p^2 + 1734 * p + 6960 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c1lo : 0 < newFirst x 4 (4*x) 1 := by
    have he : newFirst x 4 (4*x) 1 = 40 * p^2 + 672 * p + 2814 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c1hi : 0 < SW x 4 (4*x)-1-newFirst x 4 (4*x) 0 := by
    have he : SW x 4 (4*x)-1-newFirst x 4 (4*x) 0 = 216 * p^2 + 3468 * p + 13922 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c2lo : 0 < oldSecond x 4 (4*x) 1 := by
    have he : oldSecond x 4 (4*x) 1 = 64 * p^3 + 1172 * p^2 + 6405 * p + 8994 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c2hi : 0 < L x 4 (4*x)-1-oldSecond x 4 (4*x) 0 := by
    have he : L x 4 (4*x)-1-oldSecond x 4 (4*x) 0 = 300 * p^2 + 4865 * p + 19724 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c3lo : 0 < newSecond x 4 (4*x) 1 := by
    have he : newSecond x 4 (4*x) 1 = 128 * p^3 + 2280 * p^2 + 11829 * p + 14238 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have c3hi : 0 < SV x 4 (4*x)-1-newSecond x 4 (4*x) 0 := by
    have he : SV x 4 (4*x)-1-newSecond x 4 (4*x) 0 = 664 * p^2 + 10695 * p + 43070 := by
      dsimp [A,B,L,K,SU,SV,SW,oldFirst,oldSecond,newFirst,newSecond,p]; ring
    rw [he]
    positivity
  have hA : 0≤A x 4 (4*x) := by dsimp [A]; nlinarith [sq_nonneg x]
  have hlow : 0≤(1-u)*A x 4 (4*x) := mul_nonneg (by omega) hA
  have hhigh : 0≤u*A x 4 (4*x) := mul_nonneg hu.1 hA
  unfold firstTwo window
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c0lo ⊢
    nlinarith only [c0lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c0hi ⊢
    nlinarith only [c0hi,hhigh]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c1lo ⊢
    nlinarith only [c1lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c1hi ⊢
    nlinarith only [c1hi,hhigh]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c2lo ⊢
    nlinarith only [c2lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c2hi ⊢
    nlinarith only [c2hi,hhigh]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c3lo ⊢
    nlinarith only [c3lo,hlow]
  · dsimp [oldFirst,newFirst,oldSecond,newSecond] at c3hi ⊢
    nlinarith only [c3hi,hhigh]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
