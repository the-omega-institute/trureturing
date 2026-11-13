/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTailSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointTwoTailSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact full endpoint-two rectangle and tail sign identities. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! The manuscript's complete positive84/44/112 coefficient identities.
The a≥8 rectangle here is the portion consumed by the classification; the
separate sharp alpha boundary is not asserted by this module. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoTailSigns

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

/-- Outside the first rectangle, at every real a≥8. -/
theorem first_positive (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < h (8+m) (14+2*m+u) (14+2*m+u+v) 2 := by
  have hid : h (8+m) (14+2*m+u) (14+2*m+u+v) 2 =
      24*m^5*u +
      12*m^5*v +
      156*m^5 +
      52*m^4*u^2 +
      52*m^4*u*v +
      1180*m^4*u +
      18*m^4*v^2 +
      590*m^4*v +
      5176*m^4 +
      42*m^3*u^3 +
      63*m^3*u^2*v +
      1783*m^3*u^2 +
      33*m^3*u*v^2 +
      1783*m^3*u*v +
      20752*m^3*u +
      6*m^3*v^3 +
      588*m^3*v^2 +
      10376*m^3*v +
      68080*m^3 +
      15*m^2*u^4 +
      30*m^2*u^3*v +
      1056*m^2*u^3 +
      20*m^2*u^2*v^2 +
      1584*m^2*u^2*v +
      21770*m^2*u^2 +
      5*m^2*u*v^3 +
      812*m^2*u*v^2 +
      21770*m^2*u*v +
      170720*m^2*u +
      142*m^2*v^3 +
      6992*m^2*v^2 +
      85360*m^2*v +
      443360*m^2 +
      2*m*u^5 +
      5*m*u^4*v +
      260*m*u^4 +
      4*m*u^3*v^2 +
      520*m*u^3*v +
      8480*m*u^3 +
      m*u^2*v^3 +
      343*m*u^2*v^2 +
      12720*m*u^2*v +
      113844*m*u^2 +
      83*m*u*v^3 +
      6448*m*u*v^2 +
      113844*m*u*v +
      670656*m*u +
      1104*m*v^3 +
      36096*m*v^2 +
      335328*m*v +
      1427904*m +
      20*u^5 +
      50*u^4*v +
      1068*u^4 +
      40*u^3*v^2 +
      2136*u^3*v +
      22000*u^3 +
      10*u^2*v^3 +
      1402*u^2*v^2 +
      33000*u^2*v +
      216952*u^2 +
      334*u*v^3 +
      16648*u*v^2 +
      216952*u*v +
      1017408*u +
      2824*v^3 +
      68544*v^2 +
      508704*v +
      1816448 := by simp [h,quintic]; ring
  rw [hid]
  positivity

/-- The exact84-coefficient remainder, with both source square terms retained. -/
theorem second_positive (m t v : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hv : 0 ≤ v) :
    0 < h (8+m) ((8+m+(2*(8+m)-2)*t)/(1+t)) (9*(8+m)/4-8+v) 2 := by
  have ht0 : 1+t ≠ 0 := by positivity
  have hid : 64*(1+t)^3*h (8+m) ((8+m+(2*(8+m)-2)*t)/(1+t)) (9*(8+m)/4-8+v) 2 =
      9*m^6*(1+2*t)*(14*(1-t)^2+5*t+t^2)+308*m^5*t*(t-1)^2 +
      (1416*m^5*t^3*v +
      15946*m^5*t^3 +
      2684*m^5*t^2*v +
      m^5*t^2 +
      2252*m^5*t*v +
      6322*m^5*t +
      632*m^5*v +
      6027*m^5 +
      1440*m^4*t^3*v^2 +
      46760*m^4*t^3*v +
      316272*m^4*t^3 +
      3120*m^4*t^2*v^2 +
      88300*m^4*t^2*v +
      79824*m^4*t^2 +
      2288*m^4*t*v^2 +
      74792*m^4*t*v +
      131516*m^4*t +
      544*m^4*v^2 +
      21796*m^4*v +
      100060*m^4 +
      384*m^3*t^3*v^3 +
      39840*m^3*t^3*v^2 +
      563904*m^3*t^3*v +
      2952456*m^3*t^3 +
      832*m^3*t^2*v^3 +
      87472*m^3*t^2*v^2 +
      1047616*m^3*t^2*v +
      995716*m^3*t^2 +
      576*m^3*t*v^3 +
      65568*m^3*t*v^2 +
      907536*m^3*t*v +
      974712*m^3*t +
      128*m^3*v^3 +
      16144*m^3*v^2 +
      277392*m^3*v +
      766780*m^3 +
      9088*m^2*t^3*v^3 +
      391424*m^2*t^3*v^2 +
      3084384*m^2*t^3*v +
      14832512*m^2*t^3 +
      20032*m^2*t^2*v^3 +
      872192*m^2*t^2*v^2 +
      5473584*m^2*t^2*v +
      5200064*m^2*t^2 +
      14208*m^2*t*v^3 +
      670016*m^2*t*v^2 +
      4914464*m^2*t*v +
      2984064*m^2*t +
      3264*m^2*v^3 +
      170816*m^2*v^2 +
      1603664*m^2*v +
      2878080*m^2 +
      70656*m*t^3*v^3 +
      1597824*m*t^3*v^2 +
      7480320*m*t^3*v +
      39516672*m*t^3 +
      158720*m*t^2*v^3 +
      3608768*m*t^2*v^2 +
      11799040*m*t^2*v +
      14490880*m*t^2 +
      115456*m*t*v^3 +
      2845312*m*t*v^2 +
      11273216*m*t*v +
      3104768*m*t +
      27392*m*v^3 +
      751424*m*v^2 +
      4092928*m*v +
      4968448*m +
      180736*t^3*v^3 +
      2217984*t^3*v^2 +
      6137856*t^3*v +
      44646400*t^3 +
      413952*t^2*v^3 +
      5053440*t^2*v^2 +
      6706176*t^2*v +
      19243008*t^2 +
      308736*t*v^3 +
      4098048*t*v^2 +
      7569408*t*v +
      393216*t +
      75520*v^3 +
      1124352*v^2 +
      3489792*v +
      3014656) := by
    simp only [h_eq_value]
    dsimp [value]
    field_simp [ht0]
    <;> ring
  have hp : 0 < 64*(1+t)^3*h (8+m) ((8+m+(2*(8+m)-2)*t)/(1+t)) (9*(8+m)/4-8+v) 2 := by
    rw [hid]
    positivity
  exact (mul_pos_iff_of_pos_left (show (0 : ℝ) < 64*(1+t)^3 by positivity)).mp hp

/-- The exact44-coefficient D5 identity on every three real parameters≥8. -/
theorem fifth_difference_positive (m t u : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 < 4*h (8+m) (8+t) (8+u) 2-h (8+m) (8+t) (8+u) 5 := by
  have hid : 4*h (8+m) (8+t) (8+u) 2-h (8+m) (8+t) (8+u) 5 =
      3*m^3*t^2 +
      12*m^3*t*u +
      156*m^3*t +
      3*m^3*u^2 +
      156*m^3*u +
      1353*m^3 +
      3*m^2*t^3 +
      30*m^2*t^2*u +
      417*m^2*t^2 +
      30*m^2*t*u^2 +
      1239*m^2*t*u +
      10395*m^2*t +
      3*m^2*u^3 +
      417*m^2*u^2 +
      10395*m^2*u +
      67377*m^2 +
      12*m*t^3*u +
      156*m*t^3 +
      30*m*t^2*u^2 +
      1239*m*t^2*u +
      10395*m*t^2 +
      12*m*t*u^3 +
      1239*m*t*u^2 +
      29079*m*t*u +
      186366*m*t +
      156*m*u^3 +
      10395*m*u^2 +
      186366*m*u +
      996483*m +
      3*t^3*u^2 +
      156*t^3*u +
      1353*t^3 +
      3*t^2*u^3 +
      417*t^2*u^2 +
      10395*t^2*u +
      67377*t^2 +
      156*t*u^3 +
      10395*t*u^2 +
      186366*t*u +
      996483*t +
      1353*u^3 +
      67377*u^2 +
      996483*u +
      4629843 := by simp [h,quintic]; ring
  rw [hid]
  positivity

/-- The exact112-coefficient D4 identity on the full source ratio rectangle. -/
theorem fourth_difference_positive (m t u : ℝ) (hm : 0 ≤ m) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 < h (40+m) ((40+m)*(1+2*t)/(1+t)) ((40+m)*(4+9*u)/(4*(1+u))) 4-
      3*h (40+m) ((40+m)*(1+2*t)/(1+t)) ((40+m)*(4+9*u)/(4*(1+u))) 2 := by
  have ht0 : 1+t ≠ 0 := by positivity
  have hu0 : 1+u ≠ 0 := by positivity
  have hid : 64*(1+t)^3*(1+u)^3*
      (h (40+m) ((40+m)*(1+2*t)/(1+t)) ((40+m)*(4+9*u)/(4*(1+u))) 4-
       3*h (40+m) ((40+m)*(1+2*t)/(1+t)) ((40+m)*(4+9*u)/(4*(1+u))) 2) =
      2592*m^6*t^3*u^3 +
      4896*m^6*t^3*u^2 +
      2816*m^6*t^3*u +
      512*m^6*t^3 +
      5184*m^6*t^2*u^3 +
      9792*m^6*t^2*u^2 +
      5632*m^6*t^2*u +
      1024*m^6*t^2 +
      3240*m^6*t*u^3 +
      6120*m^6*t*u^2 +
      3520*m^6*t*u +
      640*m^6*t +
      648*m^6*u^3 +
      1224*m^6*u^2 +
      704*m^6*u +
      128*m^6 +
      549714*m^5*t^3*u^3 +
      1035632*m^5*t^3*u^2 +
      587872*m^5*t^3*u +
      104704*m^5*t^3 +
      1093460*m^5*t^2*u^3 +
      2065240*m^5*t^2*u^2 +
      1175200*m^5*t^2*u +
      209920*m^5*t^2 +
      674384*m^5*t*u^3 +
      1277272*m^5*t*u^2 +
      728192*m^5*t*u +
      130304*m^5*t +
      132278*m^5*u^3 +
      251384*m^5*u^2 +
      143584*m^5*u +
      25728*m^5 +
      47677022*m^4*t^3*u^3 +
      89506456*m^4*t^3*u^2 +
      49911296*m^4*t^3*u +
      8634112*m^4*t^3 +
      94149320*m^4*t^2*u^3 +
      177794520*m^4*t^2*u^2 +
      99710080*m^4*t^2*u +
      17370880*m^4*t^2 +
      57022790*m^4*t*u^3 +
      108398120*m^4*t*u^2 +
      61045920*m^4*t*u +
      10675840*m^4*t +
      10879740*m^4*u^3 +
      20857320*m^4*u^2 +
      11793920*m^4*u +
      2067840*m^4 +
      2150833004*m^3*t^3*u^3 +
      4018207392*m^3*t^3*u^2 +
      2184643072*m^3*t^3*u +
      361629184*m^3*t^3 +
      4204474452*m^3*t^2*u^3 +
      7938026736*m^3*t^2*u^2 +
      4360110016*m^3*t^2*u +
      731519232*m^3*t^2 +
      2481039396*m^3*t*u^3 +
      4741723008*m^3*t*u^2 +
      2622449728*m^3*t*u +
      442607616*m^3*t +
      453837884*m^3*u^3 +
      881946672*m^3*u^2 +
      490948992*m^3*u +
      83080704*m^3 +
      52684826880*m^2*t^3*u^3 +
      97721281760*m^2*t^3*u^2 +
      51112650880*m^2*t^3*u +
      7857856000*m^2*t^3 +
      101452569344*m^2*t^2*u^3 +
      191477361952*m^2*t^2*u^2 +
      101856239872*m^2*t^2*u +
      16049227264*m^2*t^2 +
      57495972608*m^2*t*u^3 +
      110831526304*m^2*t*u^2 +
      59528518784*m^2*t*u +
      9443545088*m^2*t +
      9789841664*m^2*u^3 +
      19487672672*m^2*u^2 +
      10552548352*m^2*u +
      1669177344*m^2 +
      652290753536*m*t^3*u^3 +
      1195972016128*m*t^3*u^2 +
      585405371648*m*t^3*u +
      77502509056*m*t^3 +
      1225715108864*m*t^2*u^3 +
      2312188925952*m*t^2*u^2 +
      1163490925312*m*t^2*u +
      161760308224*m*t^2 +
      647063198720*m*t*u^3 +
      1267215288320*m*t*u^2 +
      644107380480*m*t*u +
      89306490880*m*t +
      94951560192*m*u^3 +
      199453648896*m*u^2 +
      101554217216*m*u +
      13438528512*m +
      3069924728832*t^3*u^3 +
      5508276535296*t^3*u^2 +
      2343969284096*t^3*u +
      193009477632*t^3 +
      5505239310336*t^2*u^3 +
      10376062353408*t^2*u^2 +
      4630697975808*t^2*u +
      440930932736*t^2 +
      2483032498176*t*u^3 +
      5054388092928*t*u^2 +
      2226833891328*t*u +
      181014296576*t +
      218865180672*u^3 +
      575935266816*u^2 +
      225809391616*u +
      611305472 := by
    simp only [h_eq_value]
    dsimp [value]
    field_simp [ht0,hu0]
    <;> ring
  have hp : 0 < 64*(1+t)^3*(1+u)^3*
      (h (40+m) ((40+m)*(1+2*t)/(1+t)) ((40+m)*(4+9*u)/(4*(1+u))) 4-
       3*h (40+m) ((40+m)*(1+2*t)/(1+t)) ((40+m)*(4+9*u)/(4*(1+u))) 2) := by
    rw [hid]
    positivity
  exact (mul_pos_iff_of_pos_left (show (0 : ℝ) < 64*(1+t)^3*(1+u)^3 by positivity)).mp hp

#print axioms first_positive
#print axioms second_positive
#print axioms fifth_difference_positive
#print axioms fourth_difference_positive

end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointTwoTailSigns
