/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/CMiddleXPolynomials
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: none
   digest: 40 exact X1/X2/X3/X4/X5 equality-chart coefficient identities and margins. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddlePolynomials
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
private theorem cert_h4_e2_t8_old_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ v.t*v.A-2*s*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      5136 +
      1282*H +
      1793*T +
      448*T*H +
      208*T^2 +
      52*T^2*H +
      8*T^3 +
      2*T^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_old_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      3632 +
      910*H +
      1415*T +
      354*T*H +
      184*T^2 +
      46*T^2*H +
      8*T^3 +
      2*T^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_new_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      406 +
      98*H +
      114*T +
      28*T*H +
      8*T^2 +
      2*T^2*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_new_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      8362 +
      2094*H +
      3094*T +
      774*T*H +
      384*T^2 +
      96*T^2*H +
      16*T^3 +
      4*T^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2191023 +
      1179648*H +
      1636782*T +
      868352*T*H +
      508731*T^2 +
      266240*T^2*H +
      84216*T^3 +
      43520*T^3*H +
      7832*T^4 +
      4000*T^4*H +
      388*T^5 +
      196*T^5*H +
      8*T^6 +
      4*T^6*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      4123 +
      1033*H +
      1539*T +
      385*T*H +
      192*T^2 +
      48*T^2*H +
      8*T^3 +
      2*T^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_third_nonnegative (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ (v.L-v.B-v.M)*v.Mn-v.B*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      231078 +
      620288*H +
      428845*T +
      523456*T*H +
      210811*T^2 +
      181148*T^2*H +
      47462*T^3 +
      33020*T^3*H +
      5564*T^4 +
      3352*T^4*H +
      332*T^5 +
      180*T^5*H +
      8*T^6 +
      4*T^6*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e2_t8_third_upper (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ 2*v.B-v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      896 +
      256*H +
      224*T +
      64*T*H +
      14*T^2 +
      4*T^2*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h4_e2_t8 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (2) (4+H)
  let g : ℤ := 4+H
  let s : ℤ := (4+H)*(v.t-1)
  0 ≤ v.t*v.A-2*s*v.M ∧
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) ∧
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ (v.L-v.B-v.M)*v.Mn-v.B*v.M ∧
  0 ≤ 2*v.B-v.L-1 := by
  exact ⟨cert_h4_e2_t8_old_first_lower Y T H E hY hT hH hE,
    cert_h4_e2_t8_old_first_peak Y T H E hY hT hH hE,
    cert_h4_e2_t8_new_first_lower Y T H E hY hT hH hE,
    cert_h4_e2_t8_new_first_peak Y T H E hY hT hH hE,
    cert_h4_e2_t8_ceil_old_bank Y T H E hY hT hH hE,
    cert_h4_e2_t8_r_capacity Y T H E hY hT hH hE,
    cert_h4_e2_t8_third_nonnegative Y T H E hY hT hH hE,
    cert_h4_e2_t8_third_upper Y T H E hY hT hH hE⟩

private theorem cert_h32_e2_t4_old_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ v.t*v.A-2*s*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      6212 +
      194*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_old_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      3260 +
      102*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_new_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      582 +
      18*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_new_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      8890 +
      278*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      607655 +
      20480*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      4251 +
      133*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_third_nonnegative (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ (v.L-v.B-v.M)*v.Mn-v.B*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      16674 +
      1728*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h32_e2_t4_third_upper (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ 2*v.B-v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2016 +
      64*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h32_e2_t4 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (2) (32+H)
  let g : ℤ := 32+H
  let s : ℤ := (32+H)*(v.t-1)
  0 ≤ v.t*v.A-2*s*v.M ∧
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) ∧
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ (v.L-v.B-v.M)*v.Mn-v.B*v.M ∧
  0 ≤ 2*v.B-v.L-1 := by
  exact ⟨cert_h32_e2_t4_old_first_lower Y T H E hY hT hH hE,
    cert_h32_e2_t4_old_first_peak Y T H E hY hT hH hE,
    cert_h32_e2_t4_new_first_lower Y T H E hY hT hH hE,
    cert_h32_e2_t4_new_first_peak Y T H E hY hT hH hE,
    cert_h32_e2_t4_ceil_old_bank Y T H E hY hT hH hE,
    cert_h32_e2_t4_r_capacity Y T H E hY hT hH hE,
    cert_h32_e2_t4_third_nonnegative Y T H E hY hT hH hE,
    cert_h32_e2_t4_third_upper Y T H E hY hT hH hE⟩

private theorem cert_h4_e4_t8_old_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.t*v.A-2*s*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      30816 +
      53336*E +
      22528*E^2 +
      7702*H +
      13334*H*E +
      5632*H*E^2 +
      10761*T +
      18440*T*E +
      7680*T*E^2 +
      2690*T*H +
      4610*T*H*E +
      1920*T*H*E^2 +
      1248*T^2 +
      2112*T^2*E +
      864*T^2*E^2 +
      312*T^2*H +
      528*T^2*H*E +
      216*T^2*H*E^2 +
      48*T^3 +
      80*T^3*E +
      32*T^3*E^2 +
      12*T^3*H +
      20*T^3*H*E +
      8*T^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_old_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      3104 +
      13352*E +
      10240*E^2 +
      778*H +
      3338*H*E +
      2560*H*E^2 +
      1799*T +
      6408*T*E +
      4608*T*E^2 +
      450*T*H +
      1602*T*H*E +
      1152*T*H*E^2 +
      304*T^2 +
      976*T^2*E +
      672*T^2*E^2 +
      76*T^2*H +
      244*T^2*H*E +
      168*T^2*H*E^2 +
      16*T^3 +
      48*T^3*E +
      32*T^3*E^2 +
      4*T^3*H +
      12*T^3*H*E +
      8*T^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_new_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      21350 +
      27480*E +
      6144*E^2 +
      5334*H +
      6870*H*E +
      1536*H*E^2 +
      7402*T +
      8936*T*E +
      1536*T*E^2 +
      1850*T*H +
      2234*T*H*E +
      384*T*H*E^2 +
      848*T^2 +
      944*T^2*E +
      96*T^2*E^2 +
      212*T^2*H +
      236*T^2*H*E +
      24*T^2*H*E^2 +
      32*T^3 +
      32*T^3*E +
      8*T^3*H +
      8*T^3*H*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_new_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      12570 +
      39208*E +
      26624*E^2 +
      3146*H +
      9802*H*E +
      6656*H*E^2 +
      5158*T +
      15912*T*E +
      10752*T*E^2 +
      1290*T*H +
      3978*T*H*E +
      2688*T*H*E^2 +
      704*T^2 +
      2144*T^2*E +
      1440*T^2*E^2 +
      176*T^2*H +
      536*T^2*H*E +
      360*T^2*H*E^2 +
      32*T^3 +
      96*T^3*E +
      64*T^3*E^2 +
      8*T^3*H +
      24*T^3*H*E +
      16*T^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      8805807 +
      17653248*E +
      8847360*E^2 +
      4718592*H +
      9437184*H*E +
      4718592*H*E^2 +
      6566766*T +
      13153152*T*E +
      6586368*T*E^2 +
      3473408*T*H +
      6946816*T*H*E +
      3473408*T*H*E^2 +
      2038391*T^2 +
      4080248*T^2*E +
      2041856*T^2*E^2 +
      1064960*T^2*H +
      2129920*T^2*H*E +
      1064960*T^2*H*E^2 +
      337136*T^3 +
      674544*T^3*E +
      337408*T^3*E^2 +
      174080*T^3*H +
      348160*T^3*H*E +
      174080*T^3*H*E^2 +
      31336*T^4 +
      62680*T^4*E +
      31344*T^4*E^2 +
      16000*T^4*H +
      32000*T^4*H*E +
      16000*T^4*H*E^2 +
      1552*T^5 +
      3104*T^5*E +
      1552*T^5*E^2 +
      784*T^5*H +
      1568*T^5*H*E +
      784*T^5*H*E^2 +
      32*T^6 +
      64*T^6*E +
      32*T^6*E^2 +
      16*T^6*H +
      32*T^6*H*E +
      16*T^6*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      8219 +
      25636*E +
      17408*E^2 +
      2057*H +
      6409*H*E +
      4352*H*E^2 +
      3075*T +
      9476*T*E +
      6400*T*E^2 +
      769*T*H +
      2369*T*H*E +
      1600*T*H*E^2 +
      384*T^2 +
      1168*T^2*E +
      784*T^2*E^2 +
      96*T^2*H +
      292*T^2*H*E +
      196*T^2*H*E^2 +
      16*T^3 +
      48*T^3*E +
      32*T^3*E^2 +
      4*T^3*H +
      12*T^3*H*E +
      8*T^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_third_width (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.L-2*v.B-g*v.D := by
  dsimp only
  convert (show (0 : ℤ) ≤
      13547 +
      45308*E +
      31744*E^2 +
      3319*H +
      11255*H*E +
      7936*H*E^2 +
      5438*T +
      17472*T*E +
      12032*T*E^2 +
      1343*T*H +
      4351*T*H*E +
      3008*T*H*E^2 +
      724*T^2 +
      2244*T^2*E +
      1520*T^2*E^2 +
      180*T^2*H +
      560*T^2*H*E +
      380*T^2*H*E^2 +
      32*T^3 +
      96*T^3*E +
      64*T^3*E^2 +
      8*T^3*H +
      24*T^3*H*E +
      16*T^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e4_t8_w_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.z*v.B-2*v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      229085 +
      458464*E +
      229376*E^2 +
      57344*H +
      114688*H*E +
      57344*H*E^2 +
      118716*T +
      237500*T*E +
      118784*T*E^2 +
      29696*T*H +
      59392*T*H*E +
      29696*T*H*E^2 +
      23036*T^2 +
      46076*T^2*E +
      23040*T^2*E^2 +
      5760*T^2*H +
      11520*T^2*H*E +
      5760*T^2*H*E^2 +
      1984*T^3 +
      3968*T^3*E +
      1984*T^3*E^2 +
      496*T^3*H +
      992*T^3*H*E +
      496*T^3*H*E^2 +
      64*T^4 +
      128*T^4*E +
      64*T^4*E^2 +
      16*T^4*H +
      32*T^4*H*E +
      16*T^4*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h4_e4_t8 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (4+H)
  let g : ℤ := (1+E)*(4+H)
  let s : ℤ := ((1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.t*v.A-2*s*v.M ∧
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) ∧
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ v.L-2*v.B-g*v.D ∧
  0 ≤ v.z*v.B-2*v.L-1 := by
  exact ⟨cert_h4_e4_t8_old_first_lower Y T H E hY hT hH hE,
    cert_h4_e4_t8_old_first_peak Y T H E hY hT hH hE,
    cert_h4_e4_t8_new_first_lower Y T H E hY hT hH hE,
    cert_h4_e4_t8_new_first_peak Y T H E hY hT hH hE,
    cert_h4_e4_t8_ceil_old_bank Y T H E hY hT hH hE,
    cert_h4_e4_t8_r_capacity Y T H E hY hT hH hE,
    cert_h4_e4_t8_third_width Y T H E hY hT hH hE,
    cert_h4_e4_t8_w_capacity Y T H E hY hT hH hE⟩

private theorem cert_h4_e8_t4_old_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.t*v.A-2*s*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      16500 +
      30832*E +
      14336*E^2 +
      4124*H +
      7708*H*E +
      3584*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_old_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      524 +
      2576*E +
      2048*E^2 +
      132*H +
      644*H*E +
      512*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_new_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      9590 +
      15728*E +
      6144*E^2 +
      2396*H +
      3932*H*E +
      1536*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_new_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      7434 +
      17680*E +
      10240*E^2 +
      1860*H +
      4420*H*E +
      2560*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      567015 +
      1140480*E +
      573440*E^2 +
      327680*H +
      655360*H*E +
      327680*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      6691 +
      15912*E +
      9216*E^2 +
      1674*H +
      3978*H*E +
      2304*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_third_width (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.L-2*v.B-g*v.D := by
  dsimp only
  convert (show (0 : ℤ) ≤
      10351 +
      25720*E +
      15360*E^2 +
      2550*H +
      6390*H*E +
      3840*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h4_e8_t4_w_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.z*v.B-2*v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      48989 +
      98144*E +
      49152*E^2 +
      12288*H +
      24576*H*E +
      12288*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h4_e8_t4 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (8*(1+E)) (4+H)
  let g : ℤ := 2*(1+E)*(4+H)
  let s : ℤ := (2*(1+E)*(4+H))*(2*v.t-3)
  0 ≤ v.t*v.A-2*s*v.M ∧
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) ∧
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ v.L-2*v.B-g*v.D ∧
  0 ≤ v.z*v.B-2*v.L-1 := by
  exact ⟨cert_h4_e8_t4_old_first_lower Y T H E hY hT hH hE,
    cert_h4_e8_t4_old_first_peak Y T H E hY hT hH hE,
    cert_h4_e8_t4_new_first_lower Y T H E hY hT hH hE,
    cert_h4_e8_t4_new_first_peak Y T H E hY hT hH hE,
    cert_h4_e8_t4_ceil_old_bank Y T H E hY hT hH hE,
    cert_h4_e8_t4_r_capacity Y T H E hY hT hH hE,
    cert_h4_e8_t4_third_width Y T H E hY hT hH hE,
    cert_h4_e8_t4_w_capacity Y T H E hY hT hH hE⟩

private theorem cert_h8_e4_t4_old_first_lower_bound (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ 2*(2*v.A-5*(8+H)*v.M-v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      4202 +
      526*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_old_first_peak_bound (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ (10*(8+H)*v.M-3*v.A-1)*v.Mn+2*v.B*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1376750 +
      171978*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_new_first_lower_bound (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ 2*(3*v.A-5*(8+H)*v.Mn-v.B-v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      226 +
      174*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_new_first_peak_bound (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ 10*(8+H)*v.Mn+2*v.B-5*v.A-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      7444 +
      930*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      467815 +
      81920*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2083 +
      261*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_third_width (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ v.L-2*v.B-g*v.D := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2591 +
      315*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h8_e4_t4_w_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ v.z*v.B-2*v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      24493 +
      3072*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h8_e4_t4 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (4) (8+H)
  let g : ℤ := 8+H
  let s : ℤ := 0
  0 ≤ 2*(2*v.A-5*(8+H)*v.M-v.B) ∧
  0 ≤ (10*(8+H)*v.M-3*v.A-1)*v.Mn+2*v.B*v.M ∧
  0 ≤ 2*(3*v.A-5*(8+H)*v.Mn-v.B-v.Mn) ∧
  0 ≤ 10*(8+H)*v.Mn+2*v.B-5*v.A-1 ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ v.L-2*v.B-g*v.D ∧
  0 ≤ v.z*v.B-2*v.L-1 := by
  exact ⟨cert_h8_e4_t4_old_first_lower_bound Y T H E hY hT hH hE,
    cert_h8_e4_t4_old_first_peak_bound Y T H E hY hT hH hE,
    cert_h8_e4_t4_new_first_lower_bound Y T H E hY hT hH hE,
    cert_h8_e4_t4_new_first_peak_bound Y T H E hY hT hH hE,
    cert_h8_e4_t4_ceil_old_bank Y T H E hY hT hH hE,
    cert_h8_e4_t4_r_capacity Y T H E hY hT hH hE,
    cert_h8_e4_t4_third_width Y T H E hY hT hH hE,
    cert_h8_e4_t4_w_capacity Y T H E hY hT hH hE⟩


end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
