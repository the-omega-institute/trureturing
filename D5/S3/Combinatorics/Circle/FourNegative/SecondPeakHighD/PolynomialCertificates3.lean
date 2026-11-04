/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates3
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

theorem first_small_R_lower (x p q h : ℚ)
    (hx : 4*p≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < p*q*A x p q h-K x p q h := by
  let X : ℚ := x-4*p
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(p*q*A x p q h-K x p q h) =
      16*X^2*P^2*Q^2*H
      + 16*X^2*P^2*Q^2
      + 64*X^2*P^2*Q*H
      + 64*X^2*P^2*Q
      + 64*X^2*P^2*H
      + 64*X^2*P^2
      + 112*X^2*P*Q^2*H
      + 112*X^2*P*Q^2
      + 448*X^2*P*Q*H
      + 448*X^2*P*Q
      + 448*X^2*P*H
      + 448*X^2*P
      + 192*X^2*Q^2*H
      + 192*X^2*Q^2
      + 768*X^2*Q*H
      + 768*X^2*Q
      + 768*X^2*H
      + 768*X^2
      + 128*X*P^3*Q^2*H
      + 128*X*P^3*Q^2
      + 512*X*P^3*Q*H
      + 512*X*P^3*Q
      + 512*X*P^3*H
      + 512*X*P^3
      + 1408*X*P^2*Q^2*H
      + 1408*X*P^2*Q^2
      + 5632*X*P^2*Q*H
      + 5632*X*P^2*Q
      + 5632*X*P^2*H
      + 5632*X*P^2
      + 5120*X*P*Q^2*H
      + 5120*X*P*Q^2
      + 20464*X*P*Q*H
      + 20472*X*P*Q
      + 20448*X*P*H
      + 20464*X*P
      + 6144*X*Q^2*H
      + 6144*X*Q^2
      + 24512*X*Q*H
      + 24544*X*Q
      + 24448*X*H
      + 24512*X
      + 256*P^4*Q^2*H
      + 256*P^4*Q^2
      + 1024*P^4*Q*H
      + 1024*P^4*Q
      + 1024*P^4*H
      + 1024*P^4
      + 3840*P^3*Q^2*H
      + 3840*P^3*Q^2
      + 15360*P^3*Q*H
      + 15360*P^3*Q
      + 15360*P^3*H
      + 15360*P^3
      + 21504*P^2*Q^2*H
      + 21504*P^2*Q^2
      + 85952*P^2*Q*H
      + 85984*P^2*Q
      + 85888*P^2*H
      + 85952*P^2
      + 53248*P*Q^2*H
      + 53248*P*Q^2
      + 212480*P*Q*H
      + 212744*P*Q
      + 211968*P*H
      + 212496*P
      + 49152*Q^2*H
      + 49152*Q^2
      + 195584*Q*H
      + 196128*Q
      + 194560*H
      + 195640 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      16*X^2*P^2*Q^2*H
      + 16*X^2*P^2*Q^2
      + 64*X^2*P^2*Q*H
      + 64*X^2*P^2*Q
      + 64*X^2*P^2*H
      + 64*X^2*P^2
      + 112*X^2*P*Q^2*H
      + 112*X^2*P*Q^2
      + 448*X^2*P*Q*H
      + 448*X^2*P*Q
      + 448*X^2*P*H
      + 448*X^2*P
      + 192*X^2*Q^2*H
      + 192*X^2*Q^2
      + 768*X^2*Q*H
      + 768*X^2*Q
      + 768*X^2*H
      + 768*X^2
      + 128*X*P^3*Q^2*H
      + 128*X*P^3*Q^2
      + 512*X*P^3*Q*H
      + 512*X*P^3*Q
      + 512*X*P^3*H
      + 512*X*P^3
      + 1408*X*P^2*Q^2*H
      + 1408*X*P^2*Q^2
      + 5632*X*P^2*Q*H
      + 5632*X*P^2*Q
      + 5632*X*P^2*H
      + 5632*X*P^2
      + 5120*X*P*Q^2*H
      + 5120*X*P*Q^2
      + 20464*X*P*Q*H
      + 20472*X*P*Q
      + 20448*X*P*H
      + 20464*X*P
      + 6144*X*Q^2*H
      + 6144*X*Q^2
      + 24512*X*Q*H
      + 24544*X*Q
      + 24448*X*H
      + 24512*X
      + 256*P^4*Q^2*H
      + 256*P^4*Q^2
      + 1024*P^4*Q*H
      + 1024*P^4*Q
      + 1024*P^4*H
      + 1024*P^4
      + 3840*P^3*Q^2*H
      + 3840*P^3*Q^2
      + 15360*P^3*Q*H
      + 15360*P^3*Q
      + 15360*P^3*H
      + 15360*P^3
      + 21504*P^2*Q^2*H
      + 21504*P^2*Q^2
      + 85952*P^2*Q*H
      + 85984*P^2*Q
      + 85888*P^2*H
      + 85952*P^2
      + 53248*P*Q^2*H
      + 53248*P*Q^2
      + 212480*P*Q*H
      + 212744*P*Q
      + 211968*P*H
      + 212496*P
      + 49152*Q^2*H
      + 49152*Q^2
      + 195584*Q*H
      + 196128*Q
      + 194560*H
      + 195640 := by positivity
  nlinarith only [expansion,positive]

theorem first_small_T1_upper (x p q h : ℚ)
    (hx : 4*p≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < A x p q h-1-4*(p*q*A x p q h-K x p q h)-2*Y x p q h*(Z x q+1)-2 := by
  let X : ℚ := x-4*p
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(A x p q h-1-4*(p*q*A x p q h-K x p q h)-2*Y x p q h*(Z x q+1)-2) =
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
      + 128*X^2*P^2*Q^2*H
      + 128*X^2*P^2*Q^2
      + 512*X^2*P^2*Q*H
      + 512*X^2*P^2*Q
      + 512*X^2*P^2*H
      + 512*X^2*P^2
      + 1056*X^2*P*Q^2*H
      + 1056*X^2*P*Q^2
      + 4240*X^2*P*Q*H
      + 4240*X^2*P*Q
      + 4256*X^2*P*H
      + 4256*X^2*P
      + 2176*X^2*Q^2*H
      + 2176*X^2*Q^2
      + 8768*X^2*Q*H
      + 8768*X^2*Q
      + 8832*X^2*H
      + 8832*X^2
      + 256*X*P^3*Q^2*H
      + 256*X*P^3*Q^2
      + 1024*X*P^3*Q*H
      + 1024*X*P^3*Q
      + 1024*X*P^3*H
      + 1024*X*P^3
      + 3328*X*P^2*Q^2*H
      + 3328*X*P^2*Q^2
      + 13440*X*P^2*Q*H
      + 13440*X*P^2*Q
      + 13568*X*P^2*H
      + 13568*X*P^2
      + 14336*X*P*Q^2*H
      + 14336*X*P*Q^2
      + 58400*X*P*Q*H
      + 58368*X*P*Q
      + 59456*X*P*H
      + 59392*X*P
      + 20480*X*Q^2*H
      + 20480*X*Q^2
      + 84096*X*Q*H
      + 83968*X*Q
      + 86272*X*H
      + 86024*X
      + 512*P^3*Q^2*H
      + 512*P^3*Q^2
      + 2304*P^3*Q*H
      + 2304*P^3*Q
      + 2560*P^3*H
      + 2560*P^3
      + 6144*P^2*Q^2*H
      + 6144*P^2*Q^2
      + 27776*P^2*Q*H
      + 27648*P^2*Q
      + 30976*P^2*H
      + 30720*P^2
      + 24576*P*Q^2*H
      + 24576*P*Q^2
      + 111616*P*Q*H
      + 110560*P*Q
      + 124928*P*H
      + 122848*P
      + 32768*Q^2*H
      + 32768*Q^2
      + 149504*Q*H
      + 147328*Q
      + 167936*H
      + 163728 := by
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
      + 128*X^2*P^2*Q^2*H
      + 128*X^2*P^2*Q^2
      + 512*X^2*P^2*Q*H
      + 512*X^2*P^2*Q
      + 512*X^2*P^2*H
      + 512*X^2*P^2
      + 1056*X^2*P*Q^2*H
      + 1056*X^2*P*Q^2
      + 4240*X^2*P*Q*H
      + 4240*X^2*P*Q
      + 4256*X^2*P*H
      + 4256*X^2*P
      + 2176*X^2*Q^2*H
      + 2176*X^2*Q^2
      + 8768*X^2*Q*H
      + 8768*X^2*Q
      + 8832*X^2*H
      + 8832*X^2
      + 256*X*P^3*Q^2*H
      + 256*X*P^3*Q^2
      + 1024*X*P^3*Q*H
      + 1024*X*P^3*Q
      + 1024*X*P^3*H
      + 1024*X*P^3
      + 3328*X*P^2*Q^2*H
      + 3328*X*P^2*Q^2
      + 13440*X*P^2*Q*H
      + 13440*X*P^2*Q
      + 13568*X*P^2*H
      + 13568*X*P^2
      + 14336*X*P*Q^2*H
      + 14336*X*P*Q^2
      + 58400*X*P*Q*H
      + 58368*X*P*Q
      + 59456*X*P*H
      + 59392*X*P
      + 20480*X*Q^2*H
      + 20480*X*Q^2
      + 84096*X*Q*H
      + 83968*X*Q
      + 86272*X*H
      + 86024*X
      + 512*P^3*Q^2*H
      + 512*P^3*Q^2
      + 2304*P^3*Q*H
      + 2304*P^3*Q
      + 2560*P^3*H
      + 2560*P^3
      + 6144*P^2*Q^2*H
      + 6144*P^2*Q^2
      + 27776*P^2*Q*H
      + 27648*P^2*Q
      + 30976*P^2*H
      + 30720*P^2
      + 24576*P*Q^2*H
      + 24576*P*Q^2
      + 111616*P*Q*H
      + 110560*P*Q
      + 124928*P*H
      + 122848*P
      + 32768*Q^2*H
      + 32768*Q^2
      + 149504*Q*H
      + 147328*Q
      + 167936*H
      + 163728 := by positivity
  nlinarith only [expansion,positive]

theorem tail_R32 (x p q h : ℚ)
    (hx : 32≤x) (hp : x/2≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-32
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-(x/2)
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      4*X^5*Q^2*H
      + 4*X^5*Q^2
      + 12*X^5*Q*H
      + 12*X^5*Q
      + 8*X^5*H
      + 8*X^5
      + 16*X^4*P*Q^2*H
      + 16*X^4*P*Q^2
      + 48*X^4*P*Q*H
      + 48*X^4*P*Q
      + 32*X^4*P*H
      + 32*X^4*P
      + 576*X^4*Q^2*H
      + 576*X^4*Q^2
      + 1680*X^4*Q*H
      + 1680*X^4*Q
      + 1056*X^4*H
      + 1056*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 48*X^3*P^2*Q*H
      + 48*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 1920*X^3*P*Q^2*H
      + 1920*X^3*P*Q^2
      + 5632*X^3*P*Q*H
      + 5632*X^3*P*Q
      + 3584*X^3*P*H
      + 3584*X^3*P
      + 32768*X^3*Q^2*H
      + 32768*X^3*Q^2
      + 92136*X^3*Q*H
      + 92152*X^3*Q
      + 53200*X^3*H
      + 53228*X^3
      + 1536*X^2*P^2*Q^2*H
      + 1536*X^2*P^2*Q^2
      + 4544*X^2*P^2*Q*H
      + 4544*X^2*P^2*Q
      + 2944*X^2*P^2*H
      + 2944*X^2*P^2
      + 86016*X^2*P*Q^2*H
      + 86016*X^2*P*Q^2
      + 245712*X^2*P*Q*H
      + 245744*X^2*P*Q
      + 147360*X^2*P*H
      + 147416*X^2*P
      + 917504*X^2*Q^2*H
      + 917504*X^2*Q^2
      + 2455232*X^2*Q*H
      + 2456784*X^2*Q
      + 1240456*X^2*H
      + 1243188*X^2
      + 49152*X*P^2*Q^2*H
      + 49152*X*P^2*Q^2
      + 143360*X*P^2*Q*H
      + 143360*X*P^2*Q
      + 90112*X*P^2*H
      + 90112*X*P^2
      + 1703936*X*P*Q^2*H
      + 1703936*X*P*Q^2
      + 4715520*X*P*Q*H
      + 4717600*X*P*Q
      + 2615312*X*P*H
      + 2618920*X*P
      + 12582912*X*Q^2*H
      + 12582912*X*Q^2
      + 31379456*X*Q*H
      + 31429632*X*Q
      + 12427712*X*H
      + 12516528*X
      + 524288*P^2*Q^2*H
      + 524288*P^2*Q^2
      + 1507328*P^2*Q*H
      + 1507328*P^2*Q
      + 917504*P^2*H
      + 917504*P^2
      + 12582912*P*Q^2*H
      + 12582912*P*Q^2
      + 33505280*P*Q*H
      + 33539072*P*Q
      + 16679424*P*H
      + 16737504*P
      + 67108864*Q^2*H
      + 67108864*Q^2
      + 150142976*Q*H
      + 150683648*Q
      + 31856640*H
      + 32818688 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      4*X^5*Q^2*H
      + 4*X^5*Q^2
      + 12*X^5*Q*H
      + 12*X^5*Q
      + 8*X^5*H
      + 8*X^5
      + 16*X^4*P*Q^2*H
      + 16*X^4*P*Q^2
      + 48*X^4*P*Q*H
      + 48*X^4*P*Q
      + 32*X^4*P*H
      + 32*X^4*P
      + 576*X^4*Q^2*H
      + 576*X^4*Q^2
      + 1680*X^4*Q*H
      + 1680*X^4*Q
      + 1056*X^4*H
      + 1056*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 48*X^3*P^2*Q*H
      + 48*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 1920*X^3*P*Q^2*H
      + 1920*X^3*P*Q^2
      + 5632*X^3*P*Q*H
      + 5632*X^3*P*Q
      + 3584*X^3*P*H
      + 3584*X^3*P
      + 32768*X^3*Q^2*H
      + 32768*X^3*Q^2
      + 92136*X^3*Q*H
      + 92152*X^3*Q
      + 53200*X^3*H
      + 53228*X^3
      + 1536*X^2*P^2*Q^2*H
      + 1536*X^2*P^2*Q^2
      + 4544*X^2*P^2*Q*H
      + 4544*X^2*P^2*Q
      + 2944*X^2*P^2*H
      + 2944*X^2*P^2
      + 86016*X^2*P*Q^2*H
      + 86016*X^2*P*Q^2
      + 245712*X^2*P*Q*H
      + 245744*X^2*P*Q
      + 147360*X^2*P*H
      + 147416*X^2*P
      + 917504*X^2*Q^2*H
      + 917504*X^2*Q^2
      + 2455232*X^2*Q*H
      + 2456784*X^2*Q
      + 1240456*X^2*H
      + 1243188*X^2
      + 49152*X*P^2*Q^2*H
      + 49152*X*P^2*Q^2
      + 143360*X*P^2*Q*H
      + 143360*X*P^2*Q
      + 90112*X*P^2*H
      + 90112*X*P^2
      + 1703936*X*P*Q^2*H
      + 1703936*X*P*Q^2
      + 4715520*X*P*Q*H
      + 4717600*X*P*Q
      + 2615312*X*P*H
      + 2618920*X*P
      + 12582912*X*Q^2*H
      + 12582912*X*Q^2
      + 31379456*X*Q*H
      + 31429632*X*Q
      + 12427712*X*H
      + 12516528*X
      + 524288*P^2*Q^2*H
      + 524288*P^2*Q^2
      + 1507328*P^2*Q*H
      + 1507328*P^2*Q
      + 917504*P^2*H
      + 917504*P^2
      + 12582912*P*Q^2*H
      + 12582912*P*Q^2
      + 33505280*P*Q*H
      + 33539072*P*Q
      + 16679424*P*H
      + 16737504*P
      + 67108864*Q^2*H
      + 67108864*Q^2
      + 150142976*Q*H
      + 150683648*Q
      + 31856640*H
      + 32818688 := by positivity
  nlinarith only [expansion,positive]

theorem tail_R8 (x p q h : ℚ)
    (hx : 8≤x) (hp : 4*x≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-8
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-(4*x)
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      256*X^5*Q^2*H
      + 256*X^5*Q^2
      + 768*X^5*Q*H
      + 768*X^5*Q
      + 512*X^5*H
      + 512*X^5
      + 128*X^4*P*Q^2*H
      + 128*X^4*P*Q^2
      + 384*X^4*P*Q*H
      + 384*X^4*P*Q
      + 256*X^4*P*H
      + 256*X^4*P
      + 9728*X^4*Q^2*H
      + 9728*X^4*Q^2
      + 27904*X^4*Q*H
      + 27904*X^4*Q
      + 16896*X^4*H
      + 16896*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 48*X^3*P^2*Q*H
      + 48*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 3968*X^3*P*Q^2*H
      + 3968*X^3*P*Q^2
      + 11328*X^3*P*Q*H
      + 11328*X^3*P*Q
      + 6784*X^3*P*H
      + 6784*X^3*P
      + 147456*X^3*Q^2*H
      + 147456*X^3*Q^2
      + 401216*X^3*Q*H
      + 401344*X^3*Q
      + 212608*X^3*H
      + 212832*X^3
      + 384*X^2*P^2*Q^2*H
      + 384*X^2*P^2*Q^2
      + 1088*X^2*P^2*Q*H
      + 1088*X^2*P^2*Q
      + 640*X^2*P^2*H
      + 640*X^2*P^2
      + 46080*X^2*P*Q^2*H
      + 46080*X^2*P*Q^2
      + 124368*X^2*P*Q*H
      + 124400*X^2*P*Q
      + 64416*X^2*P*H
      + 64472*X^2*P
      + 1114112*X^2*Q^2*H
      + 1114112*X^2*Q^2
      + 2846144*X^2*Q*H
      + 2849344*X^2*Q
      + 1235904*X^2*H
      + 1241408*X^2
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 8192*X*P^2*Q*H
      + 8192*X*P^2*Q
      + 4096*X*P^2*H
      + 4096*X*P^2
      + 237568*X*P*Q^2*H
      + 237568*X*P*Q^2
      + 601344*X*P*Q*H
      + 601888*X*P*Q
      + 252432*X*P*H
      + 253352*X*P
      + 4194304*X*Q^2*H
      + 4194304*X*Q^2
      + 9923584*X*Q*H
      + 9950208*X*Q
      + 3070912*X*H
      + 3115840*X
      + 8192*P^2*Q^2*H
      + 8192*P^2*Q^2
      + 20480*P^2*Q*H
      + 20480*P^2*Q
      + 8192*P^2*H
      + 8192*P^2
      + 458752*P*Q^2*H
      + 458752*P*Q^2
      + 1078272*P*Q*H
      + 1080576*P*Q
      + 321664*P*H
      + 325408*P
      + 6291456*Q^2*H
      + 6291456*Q^2
      + 13529088*Q*H
      + 13602816*Q
      + 1895936*H
      + 2017792 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      256*X^5*Q^2*H
      + 256*X^5*Q^2
      + 768*X^5*Q*H
      + 768*X^5*Q
      + 512*X^5*H
      + 512*X^5
      + 128*X^4*P*Q^2*H
      + 128*X^4*P*Q^2
      + 384*X^4*P*Q*H
      + 384*X^4*P*Q
      + 256*X^4*P*H
      + 256*X^4*P
      + 9728*X^4*Q^2*H
      + 9728*X^4*Q^2
      + 27904*X^4*Q*H
      + 27904*X^4*Q
      + 16896*X^4*H
      + 16896*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 48*X^3*P^2*Q*H
      + 48*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 3968*X^3*P*Q^2*H
      + 3968*X^3*P*Q^2
      + 11328*X^3*P*Q*H
      + 11328*X^3*P*Q
      + 6784*X^3*P*H
      + 6784*X^3*P
      + 147456*X^3*Q^2*H
      + 147456*X^3*Q^2
      + 401216*X^3*Q*H
      + 401344*X^3*Q
      + 212608*X^3*H
      + 212832*X^3
      + 384*X^2*P^2*Q^2*H
      + 384*X^2*P^2*Q^2
      + 1088*X^2*P^2*Q*H
      + 1088*X^2*P^2*Q
      + 640*X^2*P^2*H
      + 640*X^2*P^2
      + 46080*X^2*P*Q^2*H
      + 46080*X^2*P*Q^2
      + 124368*X^2*P*Q*H
      + 124400*X^2*P*Q
      + 64416*X^2*P*H
      + 64472*X^2*P
      + 1114112*X^2*Q^2*H
      + 1114112*X^2*Q^2
      + 2846144*X^2*Q*H
      + 2849344*X^2*Q
      + 1235904*X^2*H
      + 1241408*X^2
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 8192*X*P^2*Q*H
      + 8192*X*P^2*Q
      + 4096*X*P^2*H
      + 4096*X*P^2
      + 237568*X*P*Q^2*H
      + 237568*X*P*Q^2
      + 601344*X*P*Q*H
      + 601888*X*P*Q
      + 252432*X*P*H
      + 253352*X*P
      + 4194304*X*Q^2*H
      + 4194304*X*Q^2
      + 9923584*X*Q*H
      + 9950208*X*Q
      + 3070912*X*H
      + 3115840*X
      + 8192*P^2*Q^2*H
      + 8192*P^2*Q^2
      + 20480*P^2*Q*H
      + 20480*P^2*Q
      + 8192*P^2*H
      + 8192*P^2
      + 458752*P*Q^2*H
      + 458752*P*Q^2
      + 1078272*P*Q*H
      + 1080576*P*Q
      + 321664*P*H
      + 325408*P
      + 6291456*Q^2*H
      + 6291456*Q^2
      + 13529088*Q*H
      + 13602816*Q
      + 1895936*H
      + 2017792 := by positivity
  nlinarith only [expansion,positive]

theorem tail_R8q4 (x p q h : ℚ)
    (hx : 8≤x) (hp : 2*x≤p) (hq : 4≤q) (hh : 1≤h) :
    0 < x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  let X : ℚ := x-8
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-(2*x)
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-4
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h)) =
      64*X^5*Q^2*H
      + 64*X^5*Q^2
      + 448*X^5*Q*H
      + 448*X^5*Q
      + 768*X^5*H
      + 768*X^5
      + 64*X^4*P*Q^2*H
      + 64*X^4*P*Q^2
      + 448*X^4*P*Q*H
      + 448*X^4*P*Q
      + 768*X^4*P*H
      + 768*X^4*P
      + 2304*X^4*Q^2*H
      + 2304*X^4*Q^2
      + 15744*X^4*Q*H
      + 15744*X^4*Q
      + 26112*X^4*H
      + 26112*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 112*X^3*P^2*Q*H
      + 112*X^3*P^2*Q
      + 192*X^3*P^2*H
      + 192*X^3*P^2
      + 1920*X^3*P*Q^2*H
      + 1920*X^3*P*Q^2
      + 13120*X^3*P*Q*H
      + 13120*X^3*P*Q
      + 21760*X^3*P*H
      + 21760*X^3*P
      + 32768*X^3*Q^2*H
      + 32768*X^3*Q^2
      + 216992*X^3*Q*H
      + 217056*X^3*Q
      + 343680*X^3*H
      + 343920*X^3
      + 384*X^2*P^2*Q^2*H
      + 384*X^2*P^2*Q^2
      + 2624*X^2*P^2*Q*H
      + 2624*X^2*P^2*Q
      + 4352*X^2*P^2*H
      + 4352*X^2*P^2
      + 21504*X^2*P*Q^2*H
      + 21504*X^2*P*Q^2
      + 142800*X^2*P*Q*H
      + 142832*X^2*P*Q
      + 227136*X^2*P*H
      + 227256*X^2*P
      + 229376*X^2*Q^2*H
      + 229376*X^2*Q^2
      + 1455808*X^2*Q*H
      + 1457408*X^2*Q
      + 2153248*X^2*H
      + 2159216*X^2
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 20480*X*P^2*Q*H
      + 20480*X*P^2*Q
      + 32768*X*P^2*H
      + 32768*X*P^2
      + 106496*X*P*Q^2*H
      + 106496*X*P*Q^2
      + 683264*X*P*Q*H
      + 683808*X*P*Q
      + 1029136*X*P*H
      + 1031144*X*P
      + 786432*X*Q^2*H
      + 786432*X*Q^2
      + 4699136*X*Q*H
      + 4712448*X*Q
      + 6214080*X*H
      + 6263424*X
      + 8192*P^2*Q^2*H
      + 8192*P^2*Q^2
      + 53248*P^2*Q*H
      + 53248*P^2*Q
      + 81920*P^2*H
      + 81920*P^2
      + 196608*P*Q^2*H
      + 196608*P*Q^2
      + 1209344*P*Q*H
      + 1211648*P*Q
      + 1691776*P*H
      + 1700128*P
      + 1048576*Q^2*H
      + 1048576*Q^2
      + 5713920*Q*H
      + 5750784*Q
      + 6080000*H
      + 6215680 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      64*X^5*Q^2*H
      + 64*X^5*Q^2
      + 448*X^5*Q*H
      + 448*X^5*Q
      + 768*X^5*H
      + 768*X^5
      + 64*X^4*P*Q^2*H
      + 64*X^4*P*Q^2
      + 448*X^4*P*Q*H
      + 448*X^4*P*Q
      + 768*X^4*P*H
      + 768*X^4*P
      + 2304*X^4*Q^2*H
      + 2304*X^4*Q^2
      + 15744*X^4*Q*H
      + 15744*X^4*Q
      + 26112*X^4*H
      + 26112*X^4
      + 16*X^3*P^2*Q^2*H
      + 16*X^3*P^2*Q^2
      + 112*X^3*P^2*Q*H
      + 112*X^3*P^2*Q
      + 192*X^3*P^2*H
      + 192*X^3*P^2
      + 1920*X^3*P*Q^2*H
      + 1920*X^3*P*Q^2
      + 13120*X^3*P*Q*H
      + 13120*X^3*P*Q
      + 21760*X^3*P*H
      + 21760*X^3*P
      + 32768*X^3*Q^2*H
      + 32768*X^3*Q^2
      + 216992*X^3*Q*H
      + 217056*X^3*Q
      + 343680*X^3*H
      + 343920*X^3
      + 384*X^2*P^2*Q^2*H
      + 384*X^2*P^2*Q^2
      + 2624*X^2*P^2*Q*H
      + 2624*X^2*P^2*Q
      + 4352*X^2*P^2*H
      + 4352*X^2*P^2
      + 21504*X^2*P*Q^2*H
      + 21504*X^2*P*Q^2
      + 142800*X^2*P*Q*H
      + 142832*X^2*P*Q
      + 227136*X^2*P*H
      + 227256*X^2*P
      + 229376*X^2*Q^2*H
      + 229376*X^2*Q^2
      + 1455808*X^2*Q*H
      + 1457408*X^2*Q
      + 2153248*X^2*H
      + 2159216*X^2
      + 3072*X*P^2*Q^2*H
      + 3072*X*P^2*Q^2
      + 20480*X*P^2*Q*H
      + 20480*X*P^2*Q
      + 32768*X*P^2*H
      + 32768*X*P^2
      + 106496*X*P*Q^2*H
      + 106496*X*P*Q^2
      + 683264*X*P*Q*H
      + 683808*X*P*Q
      + 1029136*X*P*H
      + 1031144*X*P
      + 786432*X*Q^2*H
      + 786432*X*Q^2
      + 4699136*X*Q*H
      + 4712448*X*Q
      + 6214080*X*H
      + 6263424*X
      + 8192*P^2*Q^2*H
      + 8192*P^2*Q^2
      + 53248*P^2*Q*H
      + 53248*P^2*Q
      + 81920*P^2*H
      + 81920*P^2
      + 196608*P*Q^2*H
      + 196608*P*Q^2
      + 1209344*P*Q*H
      + 1211648*P*Q
      + 1691776*P*H
      + 1700128*P
      + 1048576*Q^2*H
      + 1048576*Q^2
      + 5713920*Q*H
      + 5750784*Q
      + 6080000*H
      + 6215680 := by positivity
  nlinarith only [expansion,positive]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
