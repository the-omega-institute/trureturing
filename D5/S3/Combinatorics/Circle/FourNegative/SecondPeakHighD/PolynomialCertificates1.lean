/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/PolynomialCertificates1
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

theorem base_K_gt_B (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < K x p q h-B x p q h := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(K x p q h-B x p q h) =
      16*X^3*P^2*Q^3*H
      + 16*X^3*P^2*Q^3
      + 80*X^3*P^2*Q^2*H
      + 80*X^3*P^2*Q^2
      + 128*X^3*P^2*Q*H
      + 128*X^3*P^2*Q
      + 64*X^3*P^2*H
      + 64*X^3*P^2
      + 128*X^3*P*Q^3*H
      + 128*X^3*P*Q^3
      + 640*X^3*P*Q^2*H
      + 640*X^3*P*Q^2
      + 1024*X^3*P*Q*H
      + 1024*X^3*P*Q
      + 512*X^3*P*H
      + 512*X^3*P
      + 256*X^3*Q^3*H
      + 256*X^3*Q^3
      + 1280*X^3*Q^2*H
      + 1280*X^3*Q^2
      + 2048*X^3*Q*H
      + 2048*X^3*Q
      + 1024*X^3*H
      + 1024*X^3
      + 192*X^2*P^2*Q^3*H
      + 192*X^2*P^2*Q^3
      + 960*X^2*P^2*Q^2*H
      + 960*X^2*P^2*Q^2
      + 1536*X^2*P^2*Q*H
      + 1536*X^2*P^2*Q
      + 768*X^2*P^2*H
      + 768*X^2*P^2
      + 1536*X^2*P*Q^3*H
      + 1536*X^2*P*Q^3
      + 7696*X^2*P*Q^2*H
      + 7696*X^2*P*Q^2
      + 12352*X^2*P*Q*H
      + 12344*X^2*P*Q
      + 6208*X^2*P*H
      + 6192*X^2*P
      + 3072*X^2*Q^3*H
      + 3072*X^2*Q^3
      + 15424*X^2*Q^2*H
      + 15424*X^2*Q^2
      + 24832*X^2*Q*H
      + 24800*X^2*Q
      + 12544*X^2*H
      + 12480*X^2
      + 768*X*P^2*Q^3*H
      + 768*X*P^2*Q^3
      + 3840*X*P^2*Q^2*H
      + 3840*X*P^2*Q^2
      + 6144*X*P^2*Q*H
      + 6144*X*P^2*Q
      + 3072*X*P^2*H
      + 3072*X*P^2
      + 6144*X*P*Q^3*H
      + 6144*X*P*Q^3
      + 30848*X*P*Q^2*H
      + 30848*X*P*Q^2
      + 49680*X*P*Q*H
      + 49608*X*P*Q
      + 25120*X*P*H
      + 24976*X*P
      + 12288*X*Q^3*H
      + 12288*X*Q^3
      + 61952*X*Q^2*H
      + 61952*X*Q^2
      + 100416*X*Q*H
      + 100128*X*Q
      + 51328*X*H
      + 50752*X
      + 1024*P^2*Q^3*H
      + 1024*P^2*Q^3
      + 5120*P^2*Q^2*H
      + 5120*P^2*Q^2
      + 8192*P^2*Q*H
      + 8192*P^2*Q
      + 4096*P^2*H
      + 4096*P^2
      + 8192*P*Q^3*H
      + 8192*P*Q^3
      + 41216*P*Q^2*H
      + 41216*P*Q^2
      + 66624*P*Q*H
      + 66464*P*Q
      + 33920*P*H
      + 33600*P
      + 16384*Q^3*H
      + 16384*Q^3
      + 82944*Q^2*H
      + 82944*Q^2
      + 135424*Q*H
      + 134784*Q
      + 70144*H
      + 68864 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      16*X^3*P^2*Q^3*H
      + 16*X^3*P^2*Q^3
      + 80*X^3*P^2*Q^2*H
      + 80*X^3*P^2*Q^2
      + 128*X^3*P^2*Q*H
      + 128*X^3*P^2*Q
      + 64*X^3*P^2*H
      + 64*X^3*P^2
      + 128*X^3*P*Q^3*H
      + 128*X^3*P*Q^3
      + 640*X^3*P*Q^2*H
      + 640*X^3*P*Q^2
      + 1024*X^3*P*Q*H
      + 1024*X^3*P*Q
      + 512*X^3*P*H
      + 512*X^3*P
      + 256*X^3*Q^3*H
      + 256*X^3*Q^3
      + 1280*X^3*Q^2*H
      + 1280*X^3*Q^2
      + 2048*X^3*Q*H
      + 2048*X^3*Q
      + 1024*X^3*H
      + 1024*X^3
      + 192*X^2*P^2*Q^3*H
      + 192*X^2*P^2*Q^3
      + 960*X^2*P^2*Q^2*H
      + 960*X^2*P^2*Q^2
      + 1536*X^2*P^2*Q*H
      + 1536*X^2*P^2*Q
      + 768*X^2*P^2*H
      + 768*X^2*P^2
      + 1536*X^2*P*Q^3*H
      + 1536*X^2*P*Q^3
      + 7696*X^2*P*Q^2*H
      + 7696*X^2*P*Q^2
      + 12352*X^2*P*Q*H
      + 12344*X^2*P*Q
      + 6208*X^2*P*H
      + 6192*X^2*P
      + 3072*X^2*Q^3*H
      + 3072*X^2*Q^3
      + 15424*X^2*Q^2*H
      + 15424*X^2*Q^2
      + 24832*X^2*Q*H
      + 24800*X^2*Q
      + 12544*X^2*H
      + 12480*X^2
      + 768*X*P^2*Q^3*H
      + 768*X*P^2*Q^3
      + 3840*X*P^2*Q^2*H
      + 3840*X*P^2*Q^2
      + 6144*X*P^2*Q*H
      + 6144*X*P^2*Q
      + 3072*X*P^2*H
      + 3072*X*P^2
      + 6144*X*P*Q^3*H
      + 6144*X*P*Q^3
      + 30848*X*P*Q^2*H
      + 30848*X*P*Q^2
      + 49680*X*P*Q*H
      + 49608*X*P*Q
      + 25120*X*P*H
      + 24976*X*P
      + 12288*X*Q^3*H
      + 12288*X*Q^3
      + 61952*X*Q^2*H
      + 61952*X*Q^2
      + 100416*X*Q*H
      + 100128*X*Q
      + 51328*X*H
      + 50752*X
      + 1024*P^2*Q^3*H
      + 1024*P^2*Q^3
      + 5120*P^2*Q^2*H
      + 5120*P^2*Q^2
      + 8192*P^2*Q*H
      + 8192*P^2*Q
      + 4096*P^2*H
      + 4096*P^2
      + 8192*P*Q^3*H
      + 8192*P*Q^3
      + 41216*P*Q^2*H
      + 41216*P*Q^2
      + 66624*P*Q*H
      + 66464*P*Q
      + 33920*P*H
      + 33600*P
      + 16384*Q^3*H
      + 16384*Q^3
      + 82944*Q^2*H
      + 82944*Q^2
      + 135424*Q*H
      + 134784*Q
      + 70144*H
      + 68864 := by positivity
  nlinarith only [expansion,positive]

theorem base_C_positive (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < C x p q h := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(C x p q h) =
      16*X^2*P*Q^2*H
      + 16*X^2*P*Q^2
      + 48*X^2*P*Q*H
      + 48*X^2*P*Q
      + 32*X^2*P*H
      + 32*X^2*P
      + 64*X^2*Q^2*H
      + 64*X^2*Q^2
      + 192*X^2*Q*H
      + 192*X^2*Q
      + 128*X^2*H
      + 128*X^2
      + 128*X*P*Q^2*H
      + 128*X*P*Q^2
      + 384*X*P*Q*H
      + 384*X*P*Q
      + 256*X*P*H
      + 256*X*P
      + 512*X*Q^2*H
      + 512*X*Q^2
      + 1552*X*Q*H
      + 1552*X*Q
      + 1056*X*H
      + 1048*X
      + 256*P*Q^2*H
      + 256*P*Q^2
      + 768*P*Q*H
      + 768*P*Q
      + 512*P*H
      + 512*P
      + 1024*Q^2*H
      + 1024*Q^2
      + 3136*Q*H
      + 3136*Q
      + 2192*H
      + 2152 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      16*X^2*P*Q^2*H
      + 16*X^2*P*Q^2
      + 48*X^2*P*Q*H
      + 48*X^2*P*Q
      + 32*X^2*P*H
      + 32*X^2*P
      + 64*X^2*Q^2*H
      + 64*X^2*Q^2
      + 192*X^2*Q*H
      + 192*X^2*Q
      + 128*X^2*H
      + 128*X^2
      + 128*X*P*Q^2*H
      + 128*X*P*Q^2
      + 384*X*P*Q*H
      + 384*X*P*Q
      + 256*X*P*H
      + 256*X*P
      + 512*X*Q^2*H
      + 512*X*Q^2
      + 1552*X*Q*H
      + 1552*X*Q
      + 1056*X*H
      + 1048*X
      + 256*P*Q^2*H
      + 256*P*Q^2
      + 768*P*Q*H
      + 768*P*Q
      + 512*P*H
      + 512*P
      + 1024*Q^2*H
      + 1024*Q^2
      + 3136*Q*H
      + 3136*Q
      + 2192*H
      + 2152 := by positivity
  nlinarith only [expansion,positive]

theorem base_second_slack (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < B x p q h-h*p*L x p q-Y x p q h*(Z x q+1) := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(B x p q h-h*p*L x p q-Y x p q h*(Z x q+1)) =
      8*X^3*P^2*Q^2*H
      + 8*X^3*P^2*Q^2
      + 32*X^3*P^2*Q*H
      + 32*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 64*X^3*P*Q^2*H
      + 64*X^3*P*Q^2
      + 256*X^3*P*Q*H
      + 256*X^3*P*Q
      + 256*X^3*P*H
      + 256*X^3*P
      + 128*X^3*Q^2*H
      + 128*X^3*Q^2
      + 512*X^3*Q*H
      + 512*X^3*Q
      + 512*X^3*H
      + 512*X^3
      + 88*X^2*P^2*Q^2*H
      + 88*X^2*P^2*Q^2
      + 352*X^2*P^2*Q*H
      + 352*X^2*P^2*Q
      + 352*X^2*P^2*H
      + 352*X^2*P^2
      + 688*X^2*P*Q^2*H
      + 688*X^2*P*Q^2
      + 2752*X^2*P*Q*H
      + 2760*X^2*P*Q
      + 2752*X^2*P*H
      + 2768*X^2*P
      + 1344*X^2*Q^2*H
      + 1344*X^2*Q^2
      + 5376*X^2*Q*H
      + 5408*X^2*Q
      + 5376*X^2*H
      + 5440*X^2
      + 320*X*P^2*Q^2*H
      + 320*X*P^2*Q^2
      + 1280*X*P^2*Q*H
      + 1280*X*P^2*Q
      + 1280*X*P^2*H
      + 1280*X*P^2
      + 2432*X*P*Q^2*H
      + 2432*X*P*Q^2
      + 9704*X*P*Q*H
      + 9776*X*P*Q
      + 9680*X*P*H
      + 9824*X*P
      + 4608*X*Q^2*H
      + 4608*X*Q^2
      + 18336*X*Q*H
      + 18624*X*Q
      + 18240*X*H
      + 18816*X
      + 384*P^2*Q^2*H
      + 384*P^2*Q^2
      + 1536*P^2*Q*H
      + 1536*P^2*Q
      + 1536*P^2*H
      + 1536*P^2
      + 2816*P*Q^2*H
      + 2816*P*Q^2
      + 11168*P*Q*H
      + 11328*P*Q
      + 11064*P*H
      + 11384*P
      + 5120*Q^2*H
      + 5120*Q^2
      + 20096*Q*H
      + 20736*Q
      + 19680*H
      + 20968 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      8*X^3*P^2*Q^2*H
      + 8*X^3*P^2*Q^2
      + 32*X^3*P^2*Q*H
      + 32*X^3*P^2*Q
      + 32*X^3*P^2*H
      + 32*X^3*P^2
      + 64*X^3*P*Q^2*H
      + 64*X^3*P*Q^2
      + 256*X^3*P*Q*H
      + 256*X^3*P*Q
      + 256*X^3*P*H
      + 256*X^3*P
      + 128*X^3*Q^2*H
      + 128*X^3*Q^2
      + 512*X^3*Q*H
      + 512*X^3*Q
      + 512*X^3*H
      + 512*X^3
      + 88*X^2*P^2*Q^2*H
      + 88*X^2*P^2*Q^2
      + 352*X^2*P^2*Q*H
      + 352*X^2*P^2*Q
      + 352*X^2*P^2*H
      + 352*X^2*P^2
      + 688*X^2*P*Q^2*H
      + 688*X^2*P*Q^2
      + 2752*X^2*P*Q*H
      + 2760*X^2*P*Q
      + 2752*X^2*P*H
      + 2768*X^2*P
      + 1344*X^2*Q^2*H
      + 1344*X^2*Q^2
      + 5376*X^2*Q*H
      + 5408*X^2*Q
      + 5376*X^2*H
      + 5440*X^2
      + 320*X*P^2*Q^2*H
      + 320*X*P^2*Q^2
      + 1280*X*P^2*Q*H
      + 1280*X*P^2*Q
      + 1280*X*P^2*H
      + 1280*X*P^2
      + 2432*X*P*Q^2*H
      + 2432*X*P*Q^2
      + 9704*X*P*Q*H
      + 9776*X*P*Q
      + 9680*X*P*H
      + 9824*X*P
      + 4608*X*Q^2*H
      + 4608*X*Q^2
      + 18336*X*Q*H
      + 18624*X*Q
      + 18240*X*H
      + 18816*X
      + 384*P^2*Q^2*H
      + 384*P^2*Q^2
      + 1536*P^2*Q*H
      + 1536*P^2*Q
      + 1536*P^2*H
      + 1536*P^2
      + 2816*P*Q^2*H
      + 2816*P*Q^2
      + 11168*P*Q*H
      + 11328*P*Q
      + 11064*P*H
      + 11384*P
      + 5120*Q^2*H
      + 5120*Q^2
      + 20096*Q*H
      + 20736*Q
      + 19680*H
      + 20968 := by positivity
  nlinarith only [expansion,positive]

theorem base_M_stock (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < (Y x p q h/2-h*p/2)*L x p q-K x p q h+B x p q h := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*((Y x p q h/2-h*p/2)*L x p q-K x p q h+B x p q h) =
      8*X^4*P^2*Q^3*H
      + 8*X^4*P^2*Q^3
      + 48*X^4*P^2*Q^2*H
      + 48*X^4*P^2*Q^2
      + 96*X^4*P^2*Q*H
      + 96*X^4*P^2*Q
      + 64*X^4*P^2*H
      + 64*X^4*P^2
      + 64*X^4*P*Q^3*H
      + 64*X^4*P*Q^3
      + 384*X^4*P*Q^2*H
      + 384*X^4*P*Q^2
      + 768*X^4*P*Q*H
      + 768*X^4*P*Q
      + 512*X^4*P*H
      + 512*X^4*P
      + 128*X^4*Q^3*H
      + 128*X^4*Q^3
      + 768*X^4*Q^2*H
      + 768*X^4*Q^2
      + 1536*X^4*Q*H
      + 1536*X^4*Q
      + 1024*X^4*H
      + 1024*X^4
      + 120*X^3*P^2*Q^3*H
      + 120*X^3*P^2*Q^3
      + 732*X^3*P^2*Q^2*H
      + 732*X^3*P^2*Q^2
      + 1488*X^3*P^2*Q*H
      + 1488*X^3*P^2*Q
      + 1008*X^3*P^2*H
      + 1008*X^3*P^2
      + 960*X^3*P*Q^3*H
      + 960*X^3*P*Q^3
      + 5856*X^3*P*Q^2*H
      + 5856*X^3*P*Q^2
      + 11904*X^3*P*Q*H
      + 11904*X^3*P*Q
      + 8064*X^3*P*H
      + 8064*X^3*P
      + 1920*X^3*Q^3*H
      + 1920*X^3*Q^3
      + 11712*X^3*Q^2*H
      + 11712*X^3*Q^2
      + 23808*X^3*Q*H
      + 23808*X^3*Q
      + 16128*X^3*H
      + 16128*X^3
      + 672*X^2*P^2*Q^3*H
      + 672*X^2*P^2*Q^3
      + 4172*X^2*P^2*Q^2*H
      + 4172*X^2*P^2*Q^2
      + 8624*X^2*P^2*Q*H
      + 8624*X^2*P^2*Q
      + 5936*X^2*P^2*H
      + 5936*X^2*P^2
      + 5376*X^2*P*Q^3*H
      + 5376*X^2*P*Q^3
      + 33368*X^2*P*Q^2*H
      + 33368*X^2*P*Q^2
      + 68960*X^2*P*Q*H
      + 68968*X^2*P*Q
      + 47456*X^2*P*H
      + 47472*X^2*P
      + 10752*X^2*Q^3*H
      + 10752*X^2*Q^3
      + 66720*X^2*Q^2*H
      + 66720*X^2*Q^2
      + 137856*X^2*Q*H
      + 137888*X^2*Q
      + 94848*X^2*H
      + 94912*X^2
      + 1664*X*P^2*Q^3*H
      + 1664*X*P^2*Q^3
      + 10528*X*P^2*Q^2*H
      + 10528*X*P^2*Q^2
      + 22144*X*P^2*Q*H
      + 22144*X*P^2*Q
      + 15488*X*P^2*H
      + 15488*X*P^2
      + 13312*X*P*Q^3*H
      + 13312*X*P*Q^3
      + 84160*X*P*Q^2*H
      + 84160*X*P*Q^2
      + 176884*X*P*Q*H
      + 176956*X*P*Q
      + 123624*X*P*H
      + 123768*X*P
      + 26624*X*Q^3*H
      + 26624*X*Q^3
      + 168192*X*Q^2*H
      + 168192*X*Q^2
      + 353232*X*Q*H
      + 353520*X*Q
      + 246688*X*H
      + 247264*X
      + 1536*P^2*Q^3*H
      + 1536*P^2*Q^3
      + 9920*P^2*Q^2*H
      + 9920*P^2*Q^2
      + 21248*P^2*Q*H
      + 21248*P^2*Q
      + 15104*P^2*H
      + 15104*P^2
      + 12288*P*Q^3*H
      + 12288*P*Q^3
      + 79232*P*Q^2*H
      + 79232*P*Q^2
      + 169424*P*Q*H
      + 169584*P*Q
      + 120220*P*H
      + 120540*P
      + 24576*Q^3*H
      + 24576*Q^3
      + 158208*Q^2*H
      + 158208*Q^2
      + 337728*Q*H
      + 338368*Q
      + 239216*H
      + 240496 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      8*X^4*P^2*Q^3*H
      + 8*X^4*P^2*Q^3
      + 48*X^4*P^2*Q^2*H
      + 48*X^4*P^2*Q^2
      + 96*X^4*P^2*Q*H
      + 96*X^4*P^2*Q
      + 64*X^4*P^2*H
      + 64*X^4*P^2
      + 64*X^4*P*Q^3*H
      + 64*X^4*P*Q^3
      + 384*X^4*P*Q^2*H
      + 384*X^4*P*Q^2
      + 768*X^4*P*Q*H
      + 768*X^4*P*Q
      + 512*X^4*P*H
      + 512*X^4*P
      + 128*X^4*Q^3*H
      + 128*X^4*Q^3
      + 768*X^4*Q^2*H
      + 768*X^4*Q^2
      + 1536*X^4*Q*H
      + 1536*X^4*Q
      + 1024*X^4*H
      + 1024*X^4
      + 120*X^3*P^2*Q^3*H
      + 120*X^3*P^2*Q^3
      + 732*X^3*P^2*Q^2*H
      + 732*X^3*P^2*Q^2
      + 1488*X^3*P^2*Q*H
      + 1488*X^3*P^2*Q
      + 1008*X^3*P^2*H
      + 1008*X^3*P^2
      + 960*X^3*P*Q^3*H
      + 960*X^3*P*Q^3
      + 5856*X^3*P*Q^2*H
      + 5856*X^3*P*Q^2
      + 11904*X^3*P*Q*H
      + 11904*X^3*P*Q
      + 8064*X^3*P*H
      + 8064*X^3*P
      + 1920*X^3*Q^3*H
      + 1920*X^3*Q^3
      + 11712*X^3*Q^2*H
      + 11712*X^3*Q^2
      + 23808*X^3*Q*H
      + 23808*X^3*Q
      + 16128*X^3*H
      + 16128*X^3
      + 672*X^2*P^2*Q^3*H
      + 672*X^2*P^2*Q^3
      + 4172*X^2*P^2*Q^2*H
      + 4172*X^2*P^2*Q^2
      + 8624*X^2*P^2*Q*H
      + 8624*X^2*P^2*Q
      + 5936*X^2*P^2*H
      + 5936*X^2*P^2
      + 5376*X^2*P*Q^3*H
      + 5376*X^2*P*Q^3
      + 33368*X^2*P*Q^2*H
      + 33368*X^2*P*Q^2
      + 68960*X^2*P*Q*H
      + 68968*X^2*P*Q
      + 47456*X^2*P*H
      + 47472*X^2*P
      + 10752*X^2*Q^3*H
      + 10752*X^2*Q^3
      + 66720*X^2*Q^2*H
      + 66720*X^2*Q^2
      + 137856*X^2*Q*H
      + 137888*X^2*Q
      + 94848*X^2*H
      + 94912*X^2
      + 1664*X*P^2*Q^3*H
      + 1664*X*P^2*Q^3
      + 10528*X*P^2*Q^2*H
      + 10528*X*P^2*Q^2
      + 22144*X*P^2*Q*H
      + 22144*X*P^2*Q
      + 15488*X*P^2*H
      + 15488*X*P^2
      + 13312*X*P*Q^3*H
      + 13312*X*P*Q^3
      + 84160*X*P*Q^2*H
      + 84160*X*P*Q^2
      + 176884*X*P*Q*H
      + 176956*X*P*Q
      + 123624*X*P*H
      + 123768*X*P
      + 26624*X*Q^3*H
      + 26624*X*Q^3
      + 168192*X*Q^2*H
      + 168192*X*Q^2
      + 353232*X*Q*H
      + 353520*X*Q
      + 246688*X*H
      + 247264*X
      + 1536*P^2*Q^3*H
      + 1536*P^2*Q^3
      + 9920*P^2*Q^2*H
      + 9920*P^2*Q^2
      + 21248*P^2*Q*H
      + 21248*P^2*Q
      + 15104*P^2*H
      + 15104*P^2
      + 12288*P*Q^3*H
      + 12288*P*Q^3
      + 79232*P*Q^2*H
      + 79232*P*Q^2
      + 169424*P*Q*H
      + 169584*P*Q
      + 120220*P*H
      + 120540*P
      + 24576*Q^3*H
      + 24576*Q^3
      + 158208*Q^2*H
      + 158208*Q^2
      + 337728*Q*H
      + 338368*Q
      + 239216*H
      + 240496 := by positivity
  nlinarith only [expansion,positive]

theorem base_S3_lower (x p q h : ℚ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) :
    0 < 2*B x p q h-2*L x p q := by
  let X : ℚ := x-4
  have hX : 0≤X := by dsimp [X]; linarith
  let P : ℚ := p-4
  have hP : 0≤P := by dsimp [P]; linarith
  let Q : ℚ := q-2
  have hQ : 0≤Q := by dsimp [Q]; linarith
  let H : ℚ := h-1
  have hH : 0≤H := by dsimp [H]; linarith
  have expansion : 8*(2*B x p q h-2*L x p q) =
      32*X^3*P^2*Q^2*H
      + 32*X^3*P^2*Q^2
      + 128*X^3*P^2*Q*H
      + 128*X^3*P^2*Q
      + 128*X^3*P^2*H
      + 128*X^3*P^2
      + 256*X^3*P*Q^2*H
      + 240*X^3*P*Q^2
      + 1024*X^3*P*Q*H
      + 960*X^3*P*Q
      + 1024*X^3*P*H
      + 960*X^3*P
      + 512*X^3*Q^2*H
      + 448*X^3*Q^2
      + 2048*X^3*Q*H
      + 1792*X^3*Q
      + 2048*X^3*H
      + 1792*X^3
      + 384*X^2*P^2*Q^2*H
      + 384*X^2*P^2*Q^2
      + 1536*X^2*P^2*Q*H
      + 1536*X^2*P^2*Q
      + 1536*X^2*P^2*H
      + 1536*X^2*P^2
      + 3072*X^2*P*Q^2*H
      + 2864*X^2*P*Q^2
      + 12288*X^2*P*Q*H
      + 11472*X^2*P*Q
      + 12288*X^2*P*H
      + 11488*X^2*P
      + 6144*X^2*Q^2*H
      + 5312*X^2*Q^2
      + 24576*X^2*Q*H
      + 21312*X^2*Q
      + 24576*X^2*H
      + 21376*X^2
      + 1536*X*P^2*Q^2*H
      + 1536*X*P^2*Q^2
      + 6144*X*P^2*Q*H
      + 6144*X*P^2*Q
      + 6144*X*P^2*H
      + 6144*X*P^2
      + 12288*X*P*Q^2*H
      + 11392*X*P*Q^2
      + 49152*X*P*Q*H
      + 45712*X*P*Q
      + 49152*X*P*H
      + 45856*X*P
      + 24576*X*Q^2*H
      + 20992*X*Q^2
      + 98304*X*Q*H
      + 84528*X*Q
      + 98304*X*H
      + 85088*X
      + 2048*P^2*Q^2*H
      + 2048*P^2*Q^2
      + 8192*P^2*Q*H
      + 8192*P^2*Q
      + 8192*P^2*H
      + 8192*P^2
      + 16384*P*Q^2*H
      + 15104*P*Q^2
      + 65536*P*Q*H
      + 60736*P*Q
      + 65536*P*H
      + 61056*P
      + 32768*Q^2*H
      + 27648*Q^2
      + 131072*Q*H
      + 111808*Q
      + 131072*H
      + 113024 := by
    dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T,X,P,Q,H]
    ring
  have positive : 0 <
      32*X^3*P^2*Q^2*H
      + 32*X^3*P^2*Q^2
      + 128*X^3*P^2*Q*H
      + 128*X^3*P^2*Q
      + 128*X^3*P^2*H
      + 128*X^3*P^2
      + 256*X^3*P*Q^2*H
      + 240*X^3*P*Q^2
      + 1024*X^3*P*Q*H
      + 960*X^3*P*Q
      + 1024*X^3*P*H
      + 960*X^3*P
      + 512*X^3*Q^2*H
      + 448*X^3*Q^2
      + 2048*X^3*Q*H
      + 1792*X^3*Q
      + 2048*X^3*H
      + 1792*X^3
      + 384*X^2*P^2*Q^2*H
      + 384*X^2*P^2*Q^2
      + 1536*X^2*P^2*Q*H
      + 1536*X^2*P^2*Q
      + 1536*X^2*P^2*H
      + 1536*X^2*P^2
      + 3072*X^2*P*Q^2*H
      + 2864*X^2*P*Q^2
      + 12288*X^2*P*Q*H
      + 11472*X^2*P*Q
      + 12288*X^2*P*H
      + 11488*X^2*P
      + 6144*X^2*Q^2*H
      + 5312*X^2*Q^2
      + 24576*X^2*Q*H
      + 21312*X^2*Q
      + 24576*X^2*H
      + 21376*X^2
      + 1536*X*P^2*Q^2*H
      + 1536*X*P^2*Q^2
      + 6144*X*P^2*Q*H
      + 6144*X*P^2*Q
      + 6144*X*P^2*H
      + 6144*X*P^2
      + 12288*X*P*Q^2*H
      + 11392*X*P*Q^2
      + 49152*X*P*Q*H
      + 45712*X*P*Q
      + 49152*X*P*H
      + 45856*X*P
      + 24576*X*Q^2*H
      + 20992*X*Q^2
      + 98304*X*Q*H
      + 84528*X*Q
      + 98304*X*H
      + 85088*X
      + 2048*P^2*Q^2*H
      + 2048*P^2*Q^2
      + 8192*P^2*Q*H
      + 8192*P^2*Q
      + 8192*P^2*H
      + 8192*P^2
      + 16384*P*Q^2*H
      + 15104*P*Q^2
      + 65536*P*Q*H
      + 60736*P*Q
      + 65536*P*H
      + 61056*P
      + 32768*Q^2*H
      + 27648*Q^2
      + 131072*Q*H
      + 111808*Q
      + 131072*H
      + 113024 := by positivity
  nlinarith only [expansion,positive]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
