/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Dyadic
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Eight exact dyadic rows and safe native-mask coordinate transport. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private epsilon cutDelta mask_casts
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private allocation nativeAllocation
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams

-- Slots: x,y,z,z/2,y/z,y/(2z),y/z²,x/(2z),y/2,x/2,lambda.
-- All entries are integer monomials; no division is performed in the chart.
private def chartPowers (chart : Fin 8) (u v w : ℤ) : Fin 11 → ℤ :=
  ![![64*u^3*v, 128*u^3*v, 4*u, 2*u,
      32*u^2*v, 16*u^2*v, 8*u*v, 8*u^2*v,
      64*u^3*v, 32*u^3*v, 1],
    ![64*u^3*v, 256*u^3*v*w, 4*u, 2*u,
      64*u^2*v*w, 32*u^2*v*w, 16*u*v*w, 8*u^2*v,
      128*u^3*v*w, 32*u^3*v, 2*w],
    ![256*u^3*v^2, 1024*u^3*v^3*w, 8*u*v, 4*u*v,
      128*u^2*v^2*w, 64*u^2*v^2*w, 16*u*v*w, 16*u^2*v,
      512*u^3*v^3*w, 128*u^3*v^2, 2*v*w],
    ![256*u^3*v^2, 512*u^3*v^2, 8*u*v, 4*u*v,
      64*u^2*v, 32*u^2*v, 8*u, 16*u^2*v,
      256*u^3*v^2, 128*u^3*v^2, 1],
    ![1024*u^3*v^2*w^2, 4096*u^3*v^3*w^2, 16*u*v*w, 8*u*v*w,
      256*u^2*v^2*w, 128*u^2*v^2*w, 16*u*v, 32*u^2*v*w,
      2048*u^3*v^3*w^2, 512*u^3*v^2*w^2, 2*v],
    ![8*u, 128*u^3*v, 4*u, 2*u,
      32*u^2*v, 16*u^2*v, 8*u*v, 1,
      64*u^3*v, 4*u, 8*u^2*v],
    ![16*u^2*v, 128*u^3*v^3*w, 4*u*v, 2*u*v,
      32*u^2*v^2*w, 16*u^2*v^2*w, 8*u*v*w, 2*u,
      64*u^3*v^3*w, 8*u^2*v, 4*u*v^2*w],
    ![32*u^2, 128*u^3*v, 4*u, 2*u,
      32*u^2*v, 16*u^2*v, 8*u*v, 4*u,
      64*u^3*v, 16*u^2, 2*u*v]] chart

private def chartEpsilon (chart : Fin 8) (u v w : ℤ) : ℤ :=
  ![0, w, v*w, 0, v, 4*u^2*v, 2*u*v^2*w, u*v] chart
private def chartDelta (chart : Fin 8) : ℤ := ![1,1,1,0,0,1,1,1] chart
private def chartMasks (chart : Fin 8) (u v w : ℤ) : Fin 4 → Fin 4 → ℤ :=
  let d := chartPowers chart u v w
  allocation (d 3-1) (d 4-1) (d 5+d 6-1-chartEpsilon chart u v w)
    (d 7-chartDelta chart) (d 8-1) (d 9-1)
private def actualPowers (a b s : ℕ) : Fin 11 → ℤ :=
  ![2^a,2^b,2^s,2^(s-1),2^(b-s),2^(b-s-1),2^(b-2*s),
    2^(a-s-1),2^(b-1),2^(a-1),2^(b-a-1)]

private theorem pow_monomial (n c eu ev ew i j k : ℕ)
    (he : n=c+eu*i+ev*j+ew*k) :
    (2:ℤ)^n=2^c*((2:ℤ)^eu)^i*((2:ℤ)^ev)^j*((2:ℤ)^ew)^k := by
  rw [he]
  simp only [pow_add,pow_mul]
  ring

private theorem native_coordinates (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b)
    (chart : Fin 8) (u v w : ℤ)
    (hp : actualPowers a b s=chartPowers chart u v w)
    (he : (epsilon a b:ℤ)=chartEpsilon chart u v w)
    (hd : (cutDelta b s:ℤ)=chartDelta chart) :
    nativeAllocation a b s=chartMasks chart u v w := by
  have hm := mask_casts a b s hs ha hb hbs
  have h3 : (2:ℤ)^(s-1)=chartPowers chart u v w 3 := congrFun hp 3
  have h4 : (2:ℤ)^(b-s)=chartPowers chart u v w 4 := congrFun hp 4
  have h5 : (2:ℤ)^(b-s-1)=chartPowers chart u v w 5 := congrFun hp 5
  have h6 : (2:ℤ)^(b-2*s)=chartPowers chart u v w 6 := congrFun hp 6
  have h7 : (2:ℤ)^(a-s-1)=chartPowers chart u v w 7 := congrFun hp 7
  have h8 : (2:ℤ)^(b-1)=chartPowers chart u v w 8 := congrFun hp 8
  have h9 : (2:ℤ)^(a-1)=chartPowers chart u v w 9 := congrFun hp 9
  dsimp only [nativeAllocation,chartMasks]
  rw [hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,he,hd]
  rw [h3,h4,h5,h6,h7,h8,h9]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
