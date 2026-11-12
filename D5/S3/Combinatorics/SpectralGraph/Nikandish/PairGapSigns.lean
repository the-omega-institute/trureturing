/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairGapSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairGapSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete symbolic endpoint signs for small, square, weighted and even tail gaps. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Sources: four-prime-single-pair-small-gap, four-prime-single-pair-midpoint,
four-prime-weighted-midpoint and four-prime-even-midpoint, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. Every coefficient of the
18/91/128/128 positive identities is retained and checked by Lean ring.
Weighted equality boundaries are included. These polynomial signs do not
assert integrality or nonintegrality outside their exact domains. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Combinatorics.SpectralGraph.PairGapSigns
open Matrix PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

private def p (a b r x : ℝ) : ℝ := (tensorK a b (b+r)-x • 1).det

private def midpoint (a b r : ℝ) : ℝ :=
      4*a^2*b^2 +
      4*a^2*b*r +
      8*a^2*b +
      4*a^2*r +
      4*a*b^3 +
      6*a*b^2*r +
      8*a*b^2 +
      2*a*b*r^2 +
      8*a*b*r +
      4*a*b +
      2*a*r^2 +
      2*a*r +
      4*b^3 +
      6*b^2*r +
      4*b^2 +
      2*b*r^2 +
      4*b*r +
      r^2

private def square (u v w : ℝ) : ℝ :=
      8*u^3*v^6 +
      112*u^3*v^5 +
      32*u^3*v^4*w +
      632*u^3*v^4 +
      296*u^3*v^3*w +
      1848*u^3*v^3 +
      40*u^3*v^2*w^2 +
      1000*u^3*v^2*w +
      2968*u^3*v^2 +
      184*u^3*v*w^2 +
      1472*u^3*v*w +
      2496*u^3*v +
      16*u^3*w^3 +
      208*u^3*w^2 +
      800*u^3*w +
      864*u^3 +
      8*u^2*v^8 +
      148*u^2*v^7 +
      40*u^2*v^6*w +
      1224*u^2*v^6 +
      552*u^2*v^5*w +
      5912*u^2*v^5 +
      72*u^2*v^4*w^2 +
      3292*u^2*v^4*w +
      18132*u^2*v^4 +
      660*u^2*v^3*w^2 +
      10836*u^2*v^3*w +
      35836*u^2*v^3 +
      56*u^2*v^2*w^3 +
      2428*u^2*v^2*w^2 +
      20532*u^2*v^2*w +
      44196*u^2*v^2 +
      256*u^2*v*w^3 +
      4204*u^2*v*w^2 +
      20948*u^2*v*w +
      30912*u^2*v +
      16*u^2*w^4 +
      360*u^2*w^3 +
      2812*u^2*w^2 +
      8888*u^2*w +
      9360*u^2 +
      20*u*v^8 +
      374*u*v^7 +
      108*u*v^6*w +
      3084*u*v^6 +
      1500*u*v^5*w +
      14660*u*v^5 +
      204*u*v^4*w^2 +
      8818*u*v^4*w +
      43860*u*v^4 +
      1878*u*v^3*w^2 +
      28094*u*v^3*w +
      84280*u*v^3 +
      164*u*v^2*w^3 +
      6690*u*v^2*w^2 +
      50986*u*v^2*w +
      101202*u*v^2 +
      752*u*v*w^3 +
      10914*u*v*w^2 +
      49710*u*v*w +
      69222*u*v +
      48*u*w^4 +
      956*u*w^3 +
      6810*u*w^2 +
      20224*u*w +
      20610*u +
      8*v^8 +
      156*v^7 +
      56*v^6*w +
      1336*v^6 +
      792*v^5*w +
      6568*v^5 +
      120*v^4*w^2 +
      4724*v^4*w +
      20243*v^4 +
      1116*v^3*w^2 +
      15212*v^3*w +
      39950*v^3 +
      104*v^2*w^3 +
      3988*v^2*w^2 +
      27824*v^2*w +
      49180*v^2 +
      480*v*w^3 +
      6484*v*w^2 +
      27308*v*w +
      34470*v +
      32*w^4 +
      600*w^3 +
      4020*w^2 +
      11188*w +
      10521

private def weighted (z a v : ℝ) : ℝ :=
      z^4*a +
      z^4 +
      4*z^3*a^3 +
      6*z^3*a^2*v^2 +
      44*z^3*a^2*v +
      84*z^3*a^2 +
      9*z^3*a*v^2 +
      62*z^3*a*v +
      108*z^3*a +
      3*z^3*v^2 +
      18*z^3*v +
      28*z^3 +
      16*z^2*a^4*v^2 +
      120*z^2*a^4*v +
      216*z^2*a^4 +
      12*z^2*a^3*v^4 +
      180*z^2*a^3*v^3 +
      1024*z^2*a^3*v^2 +
      2616*z^2*a^3*v +
      2508*z^2*a^3 +
      24*z^2*a^2*v^4 +
      342*z^2*a^2*v^3 +
      1828*z^2*a^2*v^2 +
      4344*z^2*a^2*v +
      3876*z^2*a^2 +
      15*z^2*a*v^4 +
      198*z^2*a*v^3 +
      985*z^2*a*v^2 +
      2190*z^2*a*v +
      1838*z^2*a +
      3*z^2*v^4 +
      36*z^2*v^3 +
      165*z^2*v^2 +
      342*z^2*v +
      270*z^2 +
      16*z*a^5*v^4 +
      256*z*a^5*v^3 +
      1408*z*a^5*v^2 +
      3264*z*a^5*v +
      2736*z*a^5 +
      8*z*a^4*v^6 +
      192*z*a^4*v^5 +
      1904*z*a^4*v^4 +
      10032*z*a^4*v^3 +
      29592*z*a^4*v^2 +
      46176*z*a^4*v +
      29664*z*a^4 +
      20*z*a^3*v^6 +
      456*z*a^3*v^5 +
      4284*z*a^3*v^4 +
      21288*z*a^3*v^3 +
      59116*z*a^3*v^2 +
      87096*z*a^3*v +
      53228*z*a^3 +
      18*z*a^2*v^6 +
      384*z*a^2*v^5 +
      3400*z*a^2*v^4 +
      16012*z*a^2*v^3 +
      42346*z*a^2*v^2 +
      59684*z*a^2*v +
      35052*z*a^2 +
      7*z*a*v^6 +
      138*z*a*v^5 +
      1142*z*a*v^4 +
      5076*z*a*v^3 +
      12775*z*a*v^2 +
      17250*z*a*v +
      9756*z*a +
      z*v^6 +
      18*z*v^5 +
      138*z*v^4 +
      576*z*v^3 +
      1377*z*v^2 +
      1782*z*v +
      972*z +
      32*a^6*v^5 +
      416*a^6*v^4 +
      1984*a^6*v^3 +
      4160*a^6*v^2 +
      3360*a^6*v +
      288*a^6 +
      16*a^5*v^7 +
      384*a^5*v^6 +
      4000*a^5*v^5 +
      23232*a^5*v^4 +
      80688*a^5*v^3 +
      166816*a^5*v^2 +
      189600*a^5*v +
      91296*a^5 +
      40*a^4*v^7 +
      944*a^4*v^6 +
      9576*a^4*v^5 +
      54040*a^4*v^4 +
      183032*a^4*v^3 +
      371872*a^4*v^2 +
      419608*a^4*v +
      202840*a^4 +
      36*a^3*v^7 +
      836*a^3*v^6 +
      8336*a^3*v^5 +
      46260*a^3*v^4 +
      154300*a^3*v^3 +
      309364*a^3*v^2 +
      345264*a^3*v +
      165476*a^3 +
      14*a^2*v^7 +
      324*a^2*v^6 +
      3220*a^2*v^5 +
      17812*a^2*v^4 +
      59222*a^2*v^3 +
      118332*a^2*v^2 +
      131544*a^2*v +
      62748*a^2 +
      2*a*v^7 +
      49*a*v^6 +
      510*a*v^5 +
      2927*a*v^4 +
      10014*a*v^3 +
      20439*a*v^2 +
      23058*a*v +
      11097*a +
      v^6 +
      18*v^5 +
      135*v^4 +
      540*v^3 +
      1215*v^2 +
      1458*v +
      729

private def even (z a v : ℝ) : ℝ :=
      4*z^4*a +
      4*z^4 +
      32*z^3*a^3 +
      24*z^3*a^2*v^2 +
      160*z^3*a^2*v +
      256*z^3*a^2 +
      36*z^3*a*v^2 +
      208*z^3*a*v +
      288*z^3*a +
      12*z^3*v^2 +
      48*z^3*v +
      64*z^3 +
      128*z^2*a^4*v^2 +
      896*z^2*a^4*v +
      1280*z^2*a^4 +
      48*z^2*a^3*v^4 +
      672*z^2*a^3*v^3 +
      3392*z^2*a^3*v^2 +
      7424*z^2*a^3*v +
      5504*z^2*a^3 +
      96*z^2*a^2*v^4 +
      1200*z^2*a^2*v^3 +
      5376*z^2*a^2*v^2 +
      10368*z^2*a^2*v +
      7424*z^2*a^2 +
      60*z^2*a*v^4 +
      624*z^2*a*v^3 +
      2448*z^2*a*v^2 +
      4416*z^2*a*v +
      3072*z^2*a +
      12*z^2*v^4 +
      96*z^2*v^3 +
      336*z^2*v^2 +
      576*z^2*v +
      384*z^2 +
      128*z*a^5*v^4 +
      2048*z*a^5*v^3 +
      9216*z*a^5*v^2 +
      16384*z*a^5*v +
      10240*z*a^5 +
      32*z*a^4*v^6 +
      768*z*a^4*v^5 +
      7040*z*a^4*v^4 +
      32768*z*a^4*v^3 +
      81920*z*a^4*v^2 +
      101376*z*a^4*v +
      47104*z*a^4 +
      80*z*a^3*v^6 +
      1728*z*a^3*v^5 +
      14368*z*a^3*v^4 +
      60416*z*a^3*v^3 +
      137728*z*a^3*v^2 +
      163840*z*a^3*v +
      77312*z*a^3 +
      72*z*a^2*v^6 +
      1344*z*a^2*v^5 +
      10048*z*a^2*v^4 +
      39296*z*a^2*v^3 +
      85632*z*a^2*v^2 +
      98816*z*a^2*v +
      47104*z*a^2 +
      28*z*a*v^6 +
      432*z*a*v^5 +
      2880*z*a*v^4 +
      10624*z*a*v^3 +
      22464*z*a*v^2 +
      25344*z*a*v +
      11776*z*a +
      4*z*v^6 +
      48*z*v^5 +
      288*z*v^4 +
      1024*z*v^3 +
      2112*z*v^2 +
      2304*z*v +
      1024*z +
      512*a^6*v^5 +
      5120*a^6*v^4 +
      16384*a^6*v^3 +
      24576*a^6*v^2 +
      24576*a^6*v +
      16384*a^6 +
      128*a^5*v^7 +
      2560*a^5*v^6 +
      22016*a^5*v^5 +
      102912*a^5*v^4 +
      278528*a^5*v^3 +
      434176*a^5*v^2 +
      360448*a^5*v +
      122880*a^5 +
      320*a^4*v^7 +
      6144*a^4*v^6 +
      49792*a^4*v^5 +
      220416*a^4*v^4 +
      577536*a^4*v^3 +
      903168*a^4*v^2 +
      776192*a^4*v +
      266240*a^4 +
      288*a^3*v^7 +
      5312*a^3*v^6 +
      41728*a^3*v^5 +
      181120*a^3*v^4 +
      469504*a^3*v^3 +
      728064*a^3*v^2 +
      626688*a^3*v +
      223232*a^3 +
      112*a^2*v^7 +
      2048*a^2*v^6 +
      16128*a^2*v^5 +
      70400*a^2*v^4 +
      183040*a^2*v^3 +
      282624*a^2*v^2 +
      239616*a^2*v +
      86016*a^2 +
      16*a*v^7 +
      336*a*v^6 +
      2880*a*v^5 +
      13120*a*v^4 +
      34560*a*v^3 +
      52992*a*v^2 +
      44032*a*v +
      15360*a +
      16*v^6 +
      192*v^5 +
      960*v^4 +
      2560*v^3 +
      3840*v^2 +
      3072*v +
      1024

/-- The generic positive midpoint, with no size constraint. -/
theorem midpoint_positive (a b r : ℝ) (ha : 0<a) (hb : 0<b) (hr : 0<r) :
    0<(tensorK a b (b+r)-(a+b+(r+2)/2) • 1).det := by
  have hid : 16*p a b r (a+b+(r+2)/2)=r^2*(2*a+1)*midpoint a b r := by
    dsimp [p,midpoint]
    rw [det_tensorK_sub_scalar]
    ring
  have hp : 0<midpoint a b r := by unfold midpoint; positivity
  have hh : 0<16*p a b r (a+b+(r+2)/2) := by rw [hid]; positivity
  dsimp [p] at hh
  linarith

/-- Full square-size half-unit lower endpoint; all equality faces retained. -/
theorem square_lower_negative (a b r : ℝ) (ha : 1≤a) (hr : 2≤r) (hb : r^2≤b) :
    (tensorK a b (b+r)-(a+b+(r+1)/2) • 1).det<0 := by
  let u:=a-1
  let v:=r-2
  let w:=b-r^2
  have hu : 0≤u := by dsimp [u]; linarith
  have hv : 0≤v := by dsimp [v]; linarith
  have hw : 0≤w := by dsimp [w]; linarith
  have hid : -16*p a b r (a+b+(r+1)/2)=square u v w := by
    dsimp [p,square,u,v,w]
    rw [det_tensorK_sub_scalar]
    ring
  have hp : 0<square u v w := by unfold square; positivity
  rw [←hid] at hp
  dsimp [p] at hp
  linarith

/-- The complete weighted slack identity includes equality and r=3. -/
theorem weighted_lower_negative (a b r : ℝ) (ha : 0<a) (hr : 3≤r)
    (hz : (2*a+1)*r^2≤4*a*b) :
    (tensorK a b (b+r)-(a+b+(r+1)/2) • 1).det<0 := by
  let z:=4*a*b-(2*a+1)*r^2
  let v:=r-3
  have hz0 : 0≤z := by dsimp [z]; linarith
  have hv : 0≤v := by dsimp [v]; linarith
  have hid : -256*a^3*p a b r (a+b+(r+1)/2)=weighted z a v := by
    dsimp [p,weighted,z,v]
    rw [det_tensorK_sub_scalar]
    ring
  have hp : 0<weighted z a v := by unfold weighted; positivity
  rw [←hid] at hp
  have hh : 0<256*a^3 := by positivity
  have hf : p a b r (a+b+(r+1)/2)<0 := by nlinarith
  exact hf

/-- The full even-gap polynomial sign is valid over real r>=2; using its
unit interval to exclude integers separately requires even integer r. -/
theorem even_lower_negative (a b r : ℝ) (ha : 0<a) (hr : 2≤r)
    (hz : (2*a+1)*r^2≤8*a*b) :
    (tensorK a b (b+r)-(a+b+r/2) • 1).det<0 := by
  let z:=8*a*b-(2*a+1)*r^2
  let v:=r-2
  have hz0 : 0≤z := by dsimp [z]; linarith
  have hv : 0≤v := by dsimp [v]; linarith
  have hid : -8192*a^3*p a b r (a+b+r/2)=even z a v := by
    dsimp [p,even,z,v]
    rw [det_tensorK_sub_scalar]
    ring
  have hp : 0<even z a v := by unfold even; positivity
  rw [←hid] at hp
  have hh : 0<8192*a^3 := by positivity
  have hf : p a b r (a+b+r/2)<0 := by nlinarith
  exact hf

/-- The generic negative endpoint for every unequal tail. -/
theorem unequal_lower_negative (a b c : ℝ) (ha : 0<a) (hb : 1≤b) (hbc : b<c) :
    (tensorK a b c-(a+b+1) • 1).det<0 := by
  have hid : (tensorK a b c-(a+b+1) • 1).det =
      a*b*(b-c)*(a+b+1)*(a*c*(b-1)+a*b+b*c) := by
    rw [det_tensorK_sub_scalar]
    ring
  rw [hid]
  have hc : 0<c := by linarith
  have hb0 : 0<b := by linarith
  have hp : 0<a*c*(b-1)+a*b+b*c := by positivity
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith))
      (by positivity)) hp

/-- The exact complete gap-two positive intermediate endpoint. -/
theorem gap_two_positive (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    0<(tensorK a b (b+2)-(a+b+2) • 1).det := by
  have hid : (tensorK a b (b+2)-(a+b+2) • 1).det =
      (2*a+1)*(a^2*b^2+4*a^2*b+2*a^2+a*b^3+5*a*b^2+7*a*b+3*a+
      b^3+4*b^2+4*b+1) := by
    rw [det_tensorK_sub_scalar]
    ring
  rw [hid]
  positivity

end D5.S3.Combinatorics.SpectralGraph.PairGapSigns
