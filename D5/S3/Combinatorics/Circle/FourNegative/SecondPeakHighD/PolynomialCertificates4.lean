/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates4
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

theorem tail_R16 (x p q h : ℚ)
    (hx : 16≤x) (hp : 2*x≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-16
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-(2*x)
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      64*X^5*Q^2*H
      + 64*X^5*Q^2
      + 192*X^5*Q*H
      + 192*X^5*Q
      + 128*X^5*H
      + 128*X^5
      + 64*X^4*P*Q^2*H
      + 64*X^4*P*Q^2
      + 192*X^4*P*Q*H
      + 192*X^4*P*Q
      + 128*X^4*P*H
      + 128*X^4*P
      + 4864*X^4*Q^2*H
      + 4864*X^4*Q^2
      + 14208*X^4*Q*H
      + 14208*X^4*Q
      + 8960*X^4*H
      + 8960*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 48*X^3*P^2*Q*H
      + 48*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 3968*X^3*P*Q^2*H
      + 3968*X^3*P*Q^2
      + 11584*X^3*P*Q*H
      + 11584*X^3*P*Q
      + 7296*X^3*P*H
      + 7296*X^3*P
      + 147456*X^3*Q^2*H
      + 147456*X^3*Q^2
      + 417696*X^3*Q*H
      + 417760*X^3*Q
      + 245568*X^3*H
      + 245680*X^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 2240*X^2*P^2*Q*H
      + 2240*X^2*P^2*Q
      + 1408*X^2*P^2*H
      + 1408*X^2*P^2
      + 92160*X^2*P*Q^2*H
      + 92160*X^2*P*Q^2
      + 261072*X^2*P*Q*H
      + 261104*X^2*P*Q
      + 153504*X^2*P*H
      + 153560*X^2*P
      + 2228224*X^2*Q^2*H
      + 2228224*X^2*Q^2
      + 6090176*X^2*Q*H
      + 6093312*X^2*Q
      + 3267488*X^2*H
      + 3272944*X^2
      + 12288*X*P^2*Q^2*H
      + 12288*X*P^2*Q^2
      + 34816*X*P^2*Q*H
      + 34816*X*P^2*Q
      + 20480*X*P^2*H
      + 20480*X*P^2
      + 950272*X*P*Q^2*H
      + 950272*X*P*Q^2
      + 2603520*X*P*Q*H
      + 2604576*X*P*Q
      + 1405968*X*P*H
      + 1407784*X*P
      + 16777216*X*Q^2*H
      + 16777216*X*Q^2
      + 43964416*X*Q*H
      + 44015616*X*Q
      + 20820928*X*H
      + 20909440*X
      + 65536*P^2*Q^2*H
      + 65536*P^2*Q^2
      + 180224*P^2*Q*H
      + 180224*P^2*Q
      + 98304*P^2*H
      + 98304*P^2
      + 3670016*P*Q^2*H
      + 3670016*P*Q^2
      + 9687040*P*Q*H
      + 9695744*P*Q
      + 4694272*P*H
      + 4708960*P
      + 50331648*Q^2*H
      + 50331648*Q^2
      + 125419520*Q*H
      + 125698048*Q
      + 49519616*H
      + 49997824 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      64*X^5*Q^2*H
      + 64*X^5*Q^2
      + 192*X^5*Q*H
      + 192*X^5*Q
      + 128*X^5*H
      + 128*X^5
      + 64*X^4*P*Q^2*H
      + 64*X^4*P*Q^2
      + 192*X^4*P*Q*H
      + 192*X^4*P*Q
      + 128*X^4*P*H
      + 128*X^4*P
      + 4864*X^4*Q^2*H
      + 4864*X^4*Q^2
      + 14208*X^4*Q*H
      + 14208*X^4*Q
      + 8960*X^4*H
      + 8960*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 48*X^3*P^2*Q*H
      + 48*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 3968*X^3*P*Q^2*H
      + 3968*X^3*P*Q^2
      + 11584*X^3*P*Q*H
      + 11584*X^3*P*Q
      + 7296*X^3*P*H
      + 7296*X^3*P
      + 147456*X^3*Q^2*H
      + 147456*X^3*Q^2
      + 417696*X^3*Q*H
      + 417760*X^3*Q
      + 245568*X^3*H
      + 245680*X^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 2240*X^2*P^2*Q*H
      + 2240*X^2*P^2*Q
      + 1408*X^2*P^2*H
      + 1408*X^2*P^2
      + 92160*X^2*P*Q^2*H
      + 92160*X^2*P*Q^2
      + 261072*X^2*P*Q*H
      + 261104*X^2*P*Q
      + 153504*X^2*P*H
      + 153560*X^2*P
      + 2228224*X^2*Q^2*H
      + 2228224*X^2*Q^2
      + 6090176*X^2*Q*H
      + 6093312*X^2*Q
      + 3267488*X^2*H
      + 3272944*X^2
      + 12288*X*P^2*Q^2*H
      + 12288*X*P^2*Q^2
      + 34816*X*P^2*Q*H
      + 34816*X*P^2*Q
      + 20480*X*P^2*H
      + 20480*X*P^2
      + 950272*X*P*Q^2*H
      + 950272*X*P*Q^2
      + 2603520*X*P*Q*H
      + 2604576*X*P*Q
      + 1405968*X*P*H
      + 1407784*X*P
      + 16777216*X*Q^2*H
      + 16777216*X*Q^2
      + 43964416*X*Q*H
      + 44015616*X*Q
      + 20820928*X*H
      + 20909440*X
      + 65536*P^2*Q^2*H
      + 65536*P^2*Q^2
      + 180224*P^2*Q*H
      + 180224*P^2*Q
      + 98304*P^2*H
      + 98304*P^2
      + 3670016*P*Q^2*H
      + 3670016*P*Q^2
      + 9687040*P*Q*H
      + 9695744*P*Q
      + 4694272*P*H
      + 4708960*P
      + 50331648*Q^2*H
      + 50331648*Q^2
      + 125419520*Q*H
      + 125698048*Q
      + 49519616*H
      + 49997824 := by positivity
  nlinarith only [expansion,positive]

theorem tail_R16q4 (x p q h : ℚ)
    (hx : 16≤x) (hp : x≤p) (hq : 4≤q) (hh : 1≤h) :
    0 < x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-16
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-(x)
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-4
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      16*X^5*Q^2*H
      + 16*X^5*Q^2
      + 112*X^5*Q*H
      + 112*X^5*Q
      + 192*X^5*H
      + 192*X^5
      + 32*X^4*P*Q^2*H
      + 32*X^4*P*Q^2
      + 224*X^4*P*Q*H
      + 224*X^4*P*Q
      + 384*X^4*P*H
      + 384*X^4*P
      + 1152*X^4*Q^2*H
      + 1152*X^4*Q^2
      + 7936*X^4*Q*H
      + 7936*X^4*Q
      + 13312*X^4*H
      + 13312*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 112*X^3*P^2*Q*H
      + 112*X^3*P^2*Q
      + 192*X^3*P^2*H
      + 192*X^3*P^2
      + 1920*X^3*P*Q^2*H
      + 1920*X^3*P*Q^2
      + 13248*X^3*P*Q*H
      + 13248*X^3*P*Q
      + 22272*X^3*P*H
      + 22272*X^3*P
      + 32768*X^3*Q^2*H
      + 32768*X^3*Q^2
      + 221136*X^3*Q*H
      + 221168*X^3*Q
      + 360256*X^3*H
      + 360376*X^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 5312*X^2*P^2*Q*H
      + 5312*X^2*P^2*Q
      + 8960*X^2*P^2*H
      + 8960*X^2*P^2
      + 43008*X^2*P*Q^2*H
      + 43008*X^2*P*Q^2
      + 291792*X^2*P*Q*H
      + 291824*X^2*P*Q
      + 479040*X^2*P*H
      + 479160*X^2*P
      + 458752*X^2*Q^2*H
      + 458752*X^2*Q^2
      + 3012288*X^2*Q*H
      + 3013856*X^2*Q
      + 4709136*X^2*H
      + 4715016*X^2
      + 12288*X*P^2*Q^2*H
      + 12288*X*P^2*Q^2
      + 83968*X*P^2*Q*H
      + 83968*X*P^2*Q
      + 139264*X*P^2*H
      + 139264*X*P^2
      + 425984*X*P*Q^2*H
      + 425984*X*P*Q^2
      + 2832896*X*P*Q*H
      + 2833952*X*P*Q
      + 4515856*X*P*H
      + 4519784*X*P
      + 3145728*X*Q^2*H
      + 3145728*X*Q^2
      + 19884032*X*Q*H
      + 19909632*X*Q
      + 29204928*X*H
      + 29300896*X
      + 65536*P^2*Q^2*H
      + 65536*P^2*Q^2
      + 442368*P^2*Q*H
      + 442368*P^2*Q
      + 720896*P^2*H
      + 720896*P^2
      + 1572864*P*Q^2*H
      + 1572864*P*Q^2
      + 10211328*P*Q*H
      + 10220032*P*Q
      + 15679744*P*H
      + 15711840*P
      + 8388608*Q^2*H
      + 8388608*Q^2
      + 50118656*Q*H
      + 50257920*Q
      + 66259968*H
      + 66781696 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      16*X^5*Q^2*H
      + 16*X^5*Q^2
      + 112*X^5*Q*H
      + 112*X^5*Q
      + 192*X^5*H
      + 192*X^5
      + 32*X^4*P*Q^2*H
      + 32*X^4*P*Q^2
      + 224*X^4*P*Q*H
      + 224*X^4*P*Q
      + 384*X^4*P*H
      + 384*X^4*P
      + 1152*X^4*Q^2*H
      + 1152*X^4*Q^2
      + 7936*X^4*Q*H
      + 7936*X^4*Q
      + 13312*X^4*H
      + 13312*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 112*X^3*P^2*Q*H
      + 112*X^3*P^2*Q
      + 192*X^3*P^2*H
      + 192*X^3*P^2
      + 1920*X^3*P*Q^2*H
      + 1920*X^3*P*Q^2
      + 13248*X^3*P*Q*H
      + 13248*X^3*P*Q
      + 22272*X^3*P*H
      + 22272*X^3*P
      + 32768*X^3*Q^2*H
      + 32768*X^3*Q^2
      + 221136*X^3*Q*H
      + 221168*X^3*Q
      + 360256*X^3*H
      + 360376*X^3
      + 768*X^2*P^2*Q^2*H
      + 768*X^2*P^2*Q^2
      + 5312*X^2*P^2*Q*H
      + 5312*X^2*P^2*Q
      + 8960*X^2*P^2*H
      + 8960*X^2*P^2
      + 43008*X^2*P*Q^2*H
      + 43008*X^2*P*Q^2
      + 291792*X^2*P*Q*H
      + 291824*X^2*P*Q
      + 479040*X^2*P*H
      + 479160*X^2*P
      + 458752*X^2*Q^2*H
      + 458752*X^2*Q^2
      + 3012288*X^2*Q*H
      + 3013856*X^2*Q
      + 4709136*X^2*H
      + 4715016*X^2
      + 12288*X*P^2*Q^2*H
      + 12288*X*P^2*Q^2
      + 83968*X*P^2*Q*H
      + 83968*X*P^2*Q
      + 139264*X*P^2*H
      + 139264*X*P^2
      + 425984*X*P*Q^2*H
      + 425984*X*P*Q^2
      + 2832896*X*P*Q*H
      + 2833952*X*P*Q
      + 4515856*X*P*H
      + 4519784*X*P
      + 3145728*X*Q^2*H
      + 3145728*X*Q^2
      + 19884032*X*Q*H
      + 19909632*X*Q
      + 29204928*X*H
      + 29300896*X
      + 65536*P^2*Q^2*H
      + 65536*P^2*Q^2
      + 442368*P^2*Q*H
      + 442368*P^2*Q
      + 720896*P^2*H
      + 720896*P^2
      + 1572864*P*Q^2*H
      + 1572864*P*Q^2
      + 10211328*P*Q*H
      + 10220032*P*Q
      + 15679744*P*H
      + 15711840*P
      + 8388608*Q^2*H
      + 8388608*Q^2
      + 50118656*Q*H
      + 50257920*Q
      + 66259968*H
      + 66781696 := by positivity
  nlinarith only [expansion,positive]

theorem tail_R16odd (x p q h : ℚ)
    (hx : 16≤x) (hp : p=x/2) (hq : 8≤q) (hh : 1≤h) :
    0 < x*(p/2-1)*C x p q h-(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-16
  have hX : 0≤X := by dsimp [X]; linarith
  let Q : ℚ := q-8
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(x*(p/2-1)*C x p q h-(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      2*X^5*Q^2*H
      + 2*X^5*Q^2
      + 30*X^5*Q*H
      + 30*X^5*Q
      + 112*X^5*H
      + 112*X^5
      + 136*X^4*Q^2*H
      + 136*X^4*Q^2
      + 2016*X^4*Q*H
      + 2016*X^4*Q
      + 7424*X^4*H
      + 7424*X^4
      + 3584*X^3*Q^2*H
      + 3584*X^3*Q^2
      + 52212*X^3*Q*H
      + 52220*X^3*Q
      + 188320*X^3*H
      + 188382*X^3
      + 45056*X^2*Q^2*H
      + 45056*X^2*Q^2
      + 638384*X^2*Q*H
      + 638776*X^2*Q
      + 2223492*X^2*H
      + 2226530*X^2
      + 262144*X*Q^2*H
      + 262144*X*Q^2
      + 3529216*X*Q*H
      + 3535616*X*Q
      + 11456624*X*H
      + 11506208*X
      + 524288*Q^2*H
      + 524288*Q^2
      + 6238208*Q*H
      + 6273024*Q
      + 16352000*H
      + 16621568 := by
    rw [hp]
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,Q,H]
    ring
  have positive : 0 <
      2*X^5*Q^2*H
      + 2*X^5*Q^2
      + 30*X^5*Q*H
      + 30*X^5*Q
      + 112*X^5*H
      + 112*X^5
      + 136*X^4*Q^2*H
      + 136*X^4*Q^2
      + 2016*X^4*Q*H
      + 2016*X^4*Q
      + 7424*X^4*H
      + 7424*X^4
      + 3584*X^3*Q^2*H
      + 3584*X^3*Q^2
      + 52212*X^3*Q*H
      + 52220*X^3*Q
      + 188320*X^3*H
      + 188382*X^3
      + 45056*X^2*Q^2*H
      + 45056*X^2*Q^2
      + 638384*X^2*Q*H
      + 638776*X^2*Q
      + 2223492*X^2*H
      + 2226530*X^2
      + 262144*X*Q^2*H
      + 262144*X*Q^2
      + 3529216*X*Q*H
      + 3535616*X*Q
      + 11456624*X*H
      + 11506208*X
      + 524288*Q^2*H
      + 524288*Q^2
      + 6238208*Q*H
      + 6273024*Q
      + 16352000*H
      + 16621568 := by positivity
  nlinarith only [expansion,positive]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
