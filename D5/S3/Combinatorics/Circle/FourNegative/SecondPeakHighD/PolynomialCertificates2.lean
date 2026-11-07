/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates2
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Universal coefficient identities checked by ring and positivity proof terms. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Algebra

/-! UNCOMPILED. Candidate coefficients are inputs to ring, never axioms. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

theorem base_S3_upper (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < K x p q h-1-2*B x p q h+2*L x p q := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(K x p q h-1-2*B x p q h+2*L x p q) =
      16*X^3*P^2*Q^3*H
      + 16*X^3*P^2*Q^3
      + 64*X^3*P^2*Q^2*H
      + 64*X^3*P^2*Q^2
      + 64*X^3*P^2*Q*H
      + 64*X^3*P^2*Q
      + 128*X^3*P*Q^3*H
      + 128*X^3*P*Q^3
      + 512*X^3*P*Q^2*H
      + 528*X^3*P*Q^2
      + 512*X^3*P*Q*H
      + 576*X^3*P*Q
      + 64*X^3*P
      + 256*X^3*Q^3*H
      + 256*X^3*Q^3
      + 1024*X^3*Q^2*H
      + 1088*X^3*Q^2
      + 1024*X^3*Q*H
      + 1280*X^3*Q
      + 256*X^3
      + 192*X^2*P^2*Q^3*H
      + 192*X^2*P^2*Q^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 768*X^2*P^2*Q*H
      + 768*X^2*P^2*Q
      + 1536*X^2*P*Q^3*H
      + 1536*X^2*P*Q^3
      + 6160*X^2*P*Q^2*H
      + 6368*X^2*P*Q^2
      + 6208*X^2*P*Q*H
      + 7024*X^2*P*Q
      + 64*X^2*P*H
      + 864*X^2*P
      + 3072*X^2*Q^3*H
      + 3072*X^2*Q^3
      + 12352*X^2*Q^2*H
      + 13184*X^2*Q^2
      + 12544*X^2*Q*H
      + 15808*X^2*Q
      + 256*X^2*H
      + 3456*X^2
      + 768*X*P^2*Q^3*H
      + 768*X*P^2*Q^3
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 3072*X*P^2*Q*H
      + 3072*X*P^2*Q
      + 6144*X*P*Q^3*H
      + 6144*X*P*Q^3
      + 24704*X*P*Q^2*H
      + 25600*X*P*Q^2
      + 25104*X*P*Q*H
      + 28544*X*P*Q
      + 544*X*P*H
      + 3840*X*P
      + 12288*X*Q^3*H
      + 12288*X*Q^3
      + 49664*X*Q^2*H
      + 53248*X*Q^2
      + 51264*X*Q*H
      + 65040*X*Q
      + 2176*X*H
      + 15392*X
      + 1024*P^2*Q^3*H
      + 1024*P^2*Q^3
      + 4096*P^2*Q^2*H
      + 4096*P^2*Q^2
      + 4096*P^2*Q*H
      + 4096*P^2*Q
      + 8192*P*Q^3*H
      + 8192*P*Q^3
      + 33024*P*Q^2*H
      + 34304*P*Q^2
      + 33856*P*Q*H
      + 38656*P*Q
      + 1152*P*H
      + 5632*P
      + 16384*Q^3*H
      + 16384*Q^3
      + 66560*Q^2*H
      + 71680*Q^2
      + 69888*Q*H
      + 89152*Q
      + 4608*H
      + 22656 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      16*X^3*P^2*Q^3*H
      + 16*X^3*P^2*Q^3
      + 64*X^3*P^2*Q^2*H
      + 64*X^3*P^2*Q^2
      + 64*X^3*P^2*Q*H
      + 64*X^3*P^2*Q
      + 128*X^3*P*Q^3*H
      + 128*X^3*P*Q^3
      + 512*X^3*P*Q^2*H
      + 528*X^3*P*Q^2
      + 512*X^3*P*Q*H
      + 576*X^3*P*Q
      + 64*X^3*P
      + 256*X^3*Q^3*H
      + 256*X^3*Q^3
      + 1024*X^3*Q^2*H
      + 1088*X^3*Q^2
      + 1024*X^3*Q*H
      + 1280*X^3*Q
      + 256*X^3
      + 192*X^2*P^2*Q^3*H
      + 192*X^2*P^2*Q^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 768*X^2*P^2*Q*H
      + 768*X^2*P^2*Q
      + 1536*X^2*P*Q^3*H
      + 1536*X^2*P*Q^3
      + 6160*X^2*P*Q^2*H
      + 6368*X^2*P*Q^2
      + 6208*X^2*P*Q*H
      + 7024*X^2*P*Q
      + 64*X^2*P*H
      + 864*X^2*P
      + 3072*X^2*Q^3*H
      + 3072*X^2*Q^3
      + 12352*X^2*Q^2*H
      + 13184*X^2*Q^2
      + 12544*X^2*Q*H
      + 15808*X^2*Q
      + 256*X^2*H
      + 3456*X^2
      + 768*X*P^2*Q^3*H
      + 768*X*P^2*Q^3
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 3072*X*P^2*Q*H
      + 3072*X*P^2*Q
      + 6144*X*P*Q^3*H
      + 6144*X*P*Q^3
      + 24704*X*P*Q^2*H
      + 25600*X*P*Q^2
      + 25104*X*P*Q*H
      + 28544*X*P*Q
      + 544*X*P*H
      + 3840*X*P
      + 12288*X*Q^3*H
      + 12288*X*Q^3
      + 49664*X*Q^2*H
      + 53248*X*Q^2
      + 51264*X*Q*H
      + 65040*X*Q
      + 2176*X*H
      + 15392*X
      + 1024*P^2*Q^3*H
      + 1024*P^2*Q^3
      + 4096*P^2*Q^2*H
      + 4096*P^2*Q^2
      + 4096*P^2*Q*H
      + 4096*P^2*Q
      + 8192*P*Q^3*H
      + 8192*P*Q^3
      + 33024*P*Q^2*H
      + 34304*P*Q^2
      + 33856*P*Q*H
      + 38656*P*Q
      + 1152*P*H
      + 5632*P
      + 16384*Q^3*H
      + 16384*Q^3
      + 66560*Q^2*H
      + 71680*Q^2
      + 69888*Q*H
      + 89152*Q
      + 4608*H
      + 22656 := by positivity
  nlinarith only [expansion,positive]

theorem base_T3_lower (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < 2*SU x p q h-2*SV x p q := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(2*SU x p q h-2*SV x p q) =
      64*X^3*P^2*Q^2*H
      + 64*X^3*P^2*Q^2
      + 256*X^3*P^2*Q*H
      + 256*X^3*P^2*Q
      + 256*X^3*P^2*H
      + 256*X^3*P^2
      + 512*X^3*P*Q^2*H
      + 480*X^3*P*Q^2
      + 2048*X^3*P*Q*H
      + 1920*X^3*P*Q
      + 2048*X^3*P*H
      + 1920*X^3*P
      + 1024*X^3*Q^2*H
      + 896*X^3*Q^2
      + 4096*X^3*Q*H
      + 3584*X^3*Q
      + 4096*X^3*H
      + 3584*X^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 3072*X^2*P^2*Q*H
      + 3072*X^2*P^2*Q
      + 3072*X^2*P^2*H
      + 3072*X^2*P^2
      + 6144*X^2*P*Q^2*H
      + 5728*X^2*P*Q^2
      + 24576*X^2*P*Q*H
      + 22944*X^2*P*Q
      + 24576*X^2*P*H
      + 22976*X^2*P
      + 12288*X^2*Q^2*H
      + 10624*X^2*Q^2
      + 49152*X^2*Q*H
      + 42624*X^2*Q
      + 49152*X^2*H
      + 42752*X^2
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 12288*X*P^2*Q*H
      + 12288*X*P^2*Q
      + 12288*X*P^2*H
      + 12288*X*P^2
      + 24576*X*P*Q^2*H
      + 22784*X*P*Q^2
      + 98304*X*P*Q*H
      + 91424*X*P*Q
      + 98304*X*P*H
      + 91712*X*P
      + 49152*X*Q^2*H
      + 41984*X*Q^2
      + 196608*X*Q*H
      + 169072*X*Q
      + 196608*X*H
      + 170208*X
      + 4096*P^2*Q^2*H
      + 4096*P^2*Q^2
      + 16384*P^2*Q*H
      + 16384*P^2*Q
      + 16384*P^2*H
      + 16384*P^2
      + 32768*P*Q^2*H
      + 30208*P*Q^2
      + 131072*P*Q*H
      + 121472*P*Q
      + 131072*P*H
      + 122112*P
      + 65536*Q^2*H
      + 55296*Q^2
      + 262144*Q*H
      + 223680*Q
      + 262144*H
      + 226176 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      64*X^3*P^2*Q^2*H
      + 64*X^3*P^2*Q^2
      + 256*X^3*P^2*Q*H
      + 256*X^3*P^2*Q
      + 256*X^3*P^2*H
      + 256*X^3*P^2
      + 512*X^3*P*Q^2*H
      + 480*X^3*P*Q^2
      + 2048*X^3*P*Q*H
      + 1920*X^3*P*Q
      + 2048*X^3*P*H
      + 1920*X^3*P
      + 1024*X^3*Q^2*H
      + 896*X^3*Q^2
      + 4096*X^3*Q*H
      + 3584*X^3*Q
      + 4096*X^3*H
      + 3584*X^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 3072*X^2*P^2*Q*H
      + 3072*X^2*P^2*Q
      + 3072*X^2*P^2*H
      + 3072*X^2*P^2
      + 6144*X^2*P*Q^2*H
      + 5728*X^2*P*Q^2
      + 24576*X^2*P*Q*H
      + 22944*X^2*P*Q
      + 24576*X^2*P*H
      + 22976*X^2*P
      + 12288*X^2*Q^2*H
      + 10624*X^2*Q^2
      + 49152*X^2*Q*H
      + 42624*X^2*Q
      + 49152*X^2*H
      + 42752*X^2
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 12288*X*P^2*Q*H
      + 12288*X*P^2*Q
      + 12288*X*P^2*H
      + 12288*X*P^2
      + 24576*X*P*Q^2*H
      + 22784*X*P*Q^2
      + 98304*X*P*Q*H
      + 91424*X*P*Q
      + 98304*X*P*H
      + 91712*X*P
      + 49152*X*Q^2*H
      + 41984*X*Q^2
      + 196608*X*Q*H
      + 169072*X*Q
      + 196608*X*H
      + 170208*X
      + 4096*P^2*Q^2*H
      + 4096*P^2*Q^2
      + 16384*P^2*Q*H
      + 16384*P^2*Q
      + 16384*P^2*H
      + 16384*P^2
      + 32768*P*Q^2*H
      + 30208*P*Q^2
      + 131072*P*Q*H
      + 121472*P*Q
      + 131072*P*H
      + 122112*P
      + 65536*Q^2*H
      + 55296*Q^2
      + 262144*Q*H
      + 223680*Q
      + 262144*H
      + 226176 := by positivity
  nlinarith only [expansion,positive]

theorem base_T3_upper (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < SW x p q h-1-2*SU x p q h+2*SV x p q := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(SW x p q h-1-2*SU x p q h+2*SV x p q) =
      32*X^3*P^2*Q^3*H
      + 32*X^3*P^2*Q^3
      + 128*X^3*P^2*Q^2*H
      + 128*X^3*P^2*Q^2
      + 128*X^3*P^2*Q*H
      + 128*X^3*P^2*Q
      + 256*X^3*P*Q^3*H
      + 256*X^3*P*Q^3
      + 1024*X^3*P*Q^2*H
      + 1056*X^3*P*Q^2
      + 1024*X^3*P*Q*H
      + 1152*X^3*P*Q
      + 128*X^3*P
      + 512*X^3*Q^3*H
      + 512*X^3*Q^3
      + 2048*X^3*Q^2*H
      + 2176*X^3*Q^2
      + 2048*X^3*Q*H
      + 2560*X^3*Q
      + 512*X^3
      + 384*X^2*P^2*Q^3*H
      + 384*X^2*P^2*Q^3
      + 1536*X^2*P^2*Q^2*H
      + 1536*X^2*P^2*Q^2
      + 1536*X^2*P^2*Q*H
      + 1536*X^2*P^2*Q
      + 3072*X^2*P*Q^3*H
      + 3072*X^2*P*Q^3
      + 12304*X^2*P*Q^2*H
      + 12720*X^2*P*Q^2
      + 12352*X^2*P*Q*H
      + 13984*X^2*P*Q
      + 64*X^2*P*H
      + 1664*X^2*P
      + 6144*X^2*Q^3*H
      + 6144*X^2*Q^3
      + 24640*X^2*Q^2*H
      + 26304*X^2*Q^2
      + 24832*X^2*Q*H
      + 31360*X^2*Q
      + 256*X^2*H
      + 6656*X^2
      + 1536*X*P^2*Q^3*H
      + 1536*X*P^2*Q^3
      + 6144*X*P^2*Q^2*H
      + 6144*X*P^2*Q^2
      + 6144*X*P^2*Q*H
      + 6144*X*P^2*Q
      + 12288*X*P*Q^3*H
      + 12288*X*P*Q^3
      + 49280*X*P*Q^2*H
      + 51072*X*P*Q^2
      + 49680*X*P*Q*H
      + 56560*X*P*Q
      + 544*X*P*H
      + 7136*X*P
      + 24576*X*Q^3*H
      + 24576*X*Q^3
      + 98816*X*Q^2*H
      + 105984*X*Q^2
      + 100416*X*Q*H
      + 127952*X*Q
      + 2176*X*H
      + 28576*X
      + 2048*P^2*Q^3*H
      + 2048*P^2*Q^3
      + 8192*P^2*Q^2*H
      + 8192*P^2*Q^2
      + 8192*P^2*Q*H
      + 8192*P^2*Q
      + 16384*P*Q^3*H
      + 16384*P*Q^3
      + 65792*P*Q^2*H
      + 68352*P*Q^2
      + 66624*P*Q*H
      + 76224*P*Q
      + 1152*P*H
      + 10112*P
      + 32768*Q^3*H
      + 32768*Q^3
      + 132096*Q^2*H
      + 142336*Q^2
      + 135424*Q*H
      + 173888*Q
      + 4608*H
      + 40576 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      32*X^3*P^2*Q^3*H
      + 32*X^3*P^2*Q^3
      + 128*X^3*P^2*Q^2*H
      + 128*X^3*P^2*Q^2
      + 128*X^3*P^2*Q*H
      + 128*X^3*P^2*Q
      + 256*X^3*P*Q^3*H
      + 256*X^3*P*Q^3
      + 1024*X^3*P*Q^2*H
      + 1056*X^3*P*Q^2
      + 1024*X^3*P*Q*H
      + 1152*X^3*P*Q
      + 128*X^3*P
      + 512*X^3*Q^3*H
      + 512*X^3*Q^3
      + 2048*X^3*Q^2*H
      + 2176*X^3*Q^2
      + 2048*X^3*Q*H
      + 2560*X^3*Q
      + 512*X^3
      + 384*X^2*P^2*Q^3*H
      + 384*X^2*P^2*Q^3
      + 1536*X^2*P^2*Q^2*H
      + 1536*X^2*P^2*Q^2
      + 1536*X^2*P^2*Q*H
      + 1536*X^2*P^2*Q
      + 3072*X^2*P*Q^3*H
      + 3072*X^2*P*Q^3
      + 12304*X^2*P*Q^2*H
      + 12720*X^2*P*Q^2
      + 12352*X^2*P*Q*H
      + 13984*X^2*P*Q
      + 64*X^2*P*H
      + 1664*X^2*P
      + 6144*X^2*Q^3*H
      + 6144*X^2*Q^3
      + 24640*X^2*Q^2*H
      + 26304*X^2*Q^2
      + 24832*X^2*Q*H
      + 31360*X^2*Q
      + 256*X^2*H
      + 6656*X^2
      + 1536*X*P^2*Q^3*H
      + 1536*X*P^2*Q^3
      + 6144*X*P^2*Q^2*H
      + 6144*X*P^2*Q^2
      + 6144*X*P^2*Q*H
      + 6144*X*P^2*Q
      + 12288*X*P*Q^3*H
      + 12288*X*P*Q^3
      + 49280*X*P*Q^2*H
      + 51072*X*P*Q^2
      + 49680*X*P*Q*H
      + 56560*X*P*Q
      + 544*X*P*H
      + 7136*X*P
      + 24576*X*Q^3*H
      + 24576*X*Q^3
      + 98816*X*Q^2*H
      + 105984*X*Q^2
      + 100416*X*Q*H
      + 127952*X*Q
      + 2176*X*H
      + 28576*X
      + 2048*P^2*Q^3*H
      + 2048*P^2*Q^3
      + 8192*P^2*Q^2*H
      + 8192*P^2*Q^2
      + 8192*P^2*Q*H
      + 8192*P^2*Q
      + 16384*P*Q^3*H
      + 16384*P*Q^3
      + 65792*P*Q^2*H
      + 68352*P*Q^2
      + 66624*P*Q*H
      + 76224*P*Q
      + 1152*P*H
      + 10112*P
      + 32768*Q^3*H
      + 32768*Q^3
      + 132096*Q^2*H
      + 142336*Q^2
      + 135424*Q*H
      + 173888*Q
      + 4608*H
      + 40576 := by positivity
  nlinarith only [expansion,positive]

theorem base_F2_positive (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < (2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*((2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      32*X^3*P*Q^2*H
      + 32*X^3*P*Q^2
      + 128*X^3*P*Q*H
      + 128*X^3*P*Q
      + 128*X^3*P*H
      + 128*X^3*P
      + 128*X^3*Q^2*H
      + 128*X^3*Q^2
      + 512*X^3*Q*H
      + 512*X^3*Q
      + 512*X^3*H
      + 512*X^3
      + 32*X^2*P^2*Q*H
      + 32*X^2*P^2*Q
      + 64*X^2*P^2*H
      + 64*X^2*P^2
      + 384*X^2*P*Q^2*H
      + 384*X^2*P*Q^2
      + 1824*X^2*P*Q*H
      + 1808*X^2*P*Q
      + 2112*X^2*P*H
      + 2080*X^2*P
      + 1536*X^2*Q^2*H
      + 1536*X^2*Q^2
      + 6784*X^2*Q*H
      + 6720*X^2*Q
      + 7424*X^2*H
      + 7296*X^2
      + 256*X*P^2*Q*H
      + 256*X*P^2*Q
      + 512*X*P^2*H
      + 512*X*P^2
      + 1536*X*P*Q^2*H
      + 1536*X*P*Q^2
      + 8448*X*P*Q*H
      + 8304*X*P*Q
      + 10752*X*P*H
      + 10480*X*P
      + 6144*X*Q^2*H
      + 6144*X*Q^2
      + 29696*X*Q*H
      + 29120*X*Q
      + 34816*X*H
      + 33744*X
      + 512*P^2*Q*H
      + 512*P^2*Q
      + 1024*P^2*H
      + 1024*P^2
      + 2048*P*Q^2*H
      + 2048*P*Q^2
      + 12800*P*Q*H
      + 12480*P*Q
      + 17408*P*H
      + 16848*P
      + 8192*Q^2*H
      + 8192*Q^2
      + 43008*Q*H
      + 41728*Q
      + 53248*H
      + 51072 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      32*X^3*P*Q^2*H
      + 32*X^3*P*Q^2
      + 128*X^3*P*Q*H
      + 128*X^3*P*Q
      + 128*X^3*P*H
      + 128*X^3*P
      + 128*X^3*Q^2*H
      + 128*X^3*Q^2
      + 512*X^3*Q*H
      + 512*X^3*Q
      + 512*X^3*H
      + 512*X^3
      + 32*X^2*P^2*Q*H
      + 32*X^2*P^2*Q
      + 64*X^2*P^2*H
      + 64*X^2*P^2
      + 384*X^2*P*Q^2*H
      + 384*X^2*P*Q^2
      + 1824*X^2*P*Q*H
      + 1808*X^2*P*Q
      + 2112*X^2*P*H
      + 2080*X^2*P
      + 1536*X^2*Q^2*H
      + 1536*X^2*Q^2
      + 6784*X^2*Q*H
      + 6720*X^2*Q
      + 7424*X^2*H
      + 7296*X^2
      + 256*X*P^2*Q*H
      + 256*X*P^2*Q
      + 512*X*P^2*H
      + 512*X*P^2
      + 1536*X*P*Q^2*H
      + 1536*X*P*Q^2
      + 8448*X*P*Q*H
      + 8304*X*P*Q
      + 10752*X*P*H
      + 10480*X*P
      + 6144*X*Q^2*H
      + 6144*X*Q^2
      + 29696*X*Q*H
      + 29120*X*Q
      + 34816*X*H
      + 33744*X
      + 512*P^2*Q*H
      + 512*P^2*Q
      + 1024*P^2*H
      + 1024*P^2
      + 2048*P*Q^2*H
      + 2048*P*Q^2
      + 12800*P*Q*H
      + 12480*P*Q
      + 17408*P*H
      + 16848*P
      + 8192*Q^2*H
      + 8192*Q^2
      + 43008*Q*H
      + 41728*Q
      + 53248*H
      + 51072 := by positivity
  nlinarith only [expansion,positive]

theorem first_large (x p q h : ℚ)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < A x p q h-4*C x p q h-2*Y x p q h*(Z x q+1)-2 := by
  let X : ℚ := x-8
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(A x p q h-4*C x p q h-2*Y x p q h*(Z x q+1)-2) =
      16*X^3*P*Q^2*H
      + 16*X^3*P*Q^2
      + 64*X^3*P*Q*H
      + 64*X^3*P*Q
      + 64*X^3*P*H
      + 64*X^3*P
      + 64*X^3*Q^2*H
      + 64*X^3*Q^2
      + 256*X^3*Q*H
      + 256*X^3*Q
      + 256*X^3*H
      + 256*X^3
      + 288*X^2*P*Q^2*H
      + 288*X^2*P*Q^2
      + 1232*X^2*P*Q*H
      + 1232*X^2*P*Q
      + 1312*X^2*P*H
      + 1312*X^2*P
      + 1152*X^2*Q^2*H
      + 1152*X^2*Q^2
      + 4928*X^2*Q*H
      + 4928*X^2*Q
      + 5248*X^2*H
      + 5248*X^2
      + 1536*X*P*Q^2*H
      + 1536*X*P*Q^2
      + 7392*X*P*Q*H
      + 7392*X*P*Q
      + 8640*X*P*H
      + 8640*X*P
      + 6144*X*Q^2*H
      + 6144*X*Q^2
      + 29504*X*Q*H
      + 29504*X*Q
      + 34432*X*H
      + 34472*X
      + 2048*P*Q^2*H
      + 2048*P*Q^2
      + 13056*P*Q*H
      + 13056*P*Q
      + 17920*P*H
      + 17920*P
      + 8192*Q^2*H
      + 8192*Q^2
      + 51712*Q*H
      + 51712*Q
      + 70592*H
      + 70936 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      16*X^3*P*Q^2*H
      + 16*X^3*P*Q^2
      + 64*X^3*P*Q*H
      + 64*X^3*P*Q
      + 64*X^3*P*H
      + 64*X^3*P
      + 64*X^3*Q^2*H
      + 64*X^3*Q^2
      + 256*X^3*Q*H
      + 256*X^3*Q
      + 256*X^3*H
      + 256*X^3
      + 288*X^2*P*Q^2*H
      + 288*X^2*P*Q^2
      + 1232*X^2*P*Q*H
      + 1232*X^2*P*Q
      + 1312*X^2*P*H
      + 1312*X^2*P
      + 1152*X^2*Q^2*H
      + 1152*X^2*Q^2
      + 4928*X^2*Q*H
      + 4928*X^2*Q
      + 5248*X^2*H
      + 5248*X^2
      + 1536*X*P*Q^2*H
      + 1536*X*P*Q^2
      + 7392*X*P*Q*H
      + 7392*X*P*Q
      + 8640*X*P*H
      + 8640*X*P
      + 6144*X*Q^2*H
      + 6144*X*Q^2
      + 29504*X*Q*H
      + 29504*X*Q
      + 34432*X*H
      + 34472*X
      + 2048*P*Q^2*H
      + 2048*P*Q^2
      + 13056*P*Q*H
      + 13056*P*Q
      + 17920*P*H
      + 17920*P
      + 8192*Q^2*H
      + 8192*Q^2
      + 51712*Q*H
      + 51712*Q
      + 70592*H
      + 70936 := by positivity
  nlinarith only [expansion,positive]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
