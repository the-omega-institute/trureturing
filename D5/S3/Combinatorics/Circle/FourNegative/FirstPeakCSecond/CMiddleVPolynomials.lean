/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/CMiddleVPolynomials
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: none
   digest: 48 exact V1/V2/V3 equality-chart coefficient identities and margins. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddlePolynomials
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
private theorem cert_h2_e2_old_seam_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-r*v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      456 +
      354*T +
      92*T^2 +
      8*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_old_peak_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.L-1-2*(v.L-r*v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      96 +
      48*T +
      6*T^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_seam_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Ln-r*v.Bn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      896 +
      704*T +
      184*T^2 +
      16*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_peak_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.Ln-1-2*(v.Ln-r*v.Bn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      200 +
      98*T +
      12*T^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_old_seam_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.M-C) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      250 +
      190*T +
      48*T^2 +
      4*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_old_peak_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.B-1-2*(v.M-C) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      74 +
      35*T +
      4*T^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_seam_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Mn-2*C-v.z-1) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      408 +
      342*T +
      92*T^2 +
      8*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_peak_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.Bn-1-2*(v.Mn-2*C-v.z-1) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      240 +
      108*T +
      12*T^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_old_seam_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-R*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      116 +
      126*T +
      40*T^2 +
      4*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_old_peak_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.A-1-2*(v.L-R*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      476 +
      294*T +
      60*T^2 +
      4*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_seam_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Ln-R*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      436 +
      350*T +
      92*T^2 +
      8*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_peak_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.A-1-2*(v.Ln-R*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      156 +
      70*T +
      8*T^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_old_peak_3 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.M-1-2*(0) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      164 +
      113*T +
      26*T^2 +
      2*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_e2_new_peak_3 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ v.Mn-1-2*(0) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      292 +
      209*T +
      50*T^2 +
      4*T^3 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h2_e2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+T) (4+T) (2) (2)
  let r : ℤ := 1
  let R : ℤ := 3
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-r*v.B) ∧
  0 ≤ v.L-1-2*(v.L-r*v.B) ∧
  0 ≤ 2*(v.Ln-r*v.Bn) ∧
  0 ≤ v.Ln-1-2*(v.Ln-r*v.Bn) ∧
  0 ≤ 2*(v.M-C) ∧
  0 ≤ v.B-1-2*(v.M-C) ∧
  0 ≤ 2*(v.Mn-2*C-v.z-1) ∧
  0 ≤ v.Bn-1-2*(v.Mn-2*C-v.z-1) ∧
  0 ≤ 2*(v.L-R*v.M) ∧
  0 ≤ v.A-1-2*(v.L-R*v.M) ∧
  0 ≤ 2*(v.Ln-R*v.Mn) ∧
  0 ≤ v.A-1-2*(v.Ln-R*v.Mn) ∧
  0 ≤ 2*(0) ∧
  0 ≤ v.M-1-2*(0) ∧
  0 ≤ 2*(0) ∧
  0 ≤ v.Mn-1-2*(0) := by
  exact ⟨cert_h2_e2_old_seam_0 Y T H E hY hT hH hE,
    cert_h2_e2_old_peak_0 Y T H E hY hT hH hE,
    cert_h2_e2_new_seam_0 Y T H E hY hT hH hE,
    cert_h2_e2_new_peak_0 Y T H E hY hT hH hE,
    cert_h2_e2_old_seam_1 Y T H E hY hT hH hE,
    cert_h2_e2_old_peak_1 Y T H E hY hT hH hE,
    cert_h2_e2_new_seam_1 Y T H E hY hT hH hE,
    cert_h2_e2_new_peak_1 Y T H E hY hT hH hE,
    cert_h2_e2_old_seam_2 Y T H E hY hT hH hE,
    cert_h2_e2_old_peak_2 Y T H E hY hT hH hE,
    cert_h2_e2_new_seam_2 Y T H E hY hT hH hE,
    cert_h2_e2_new_peak_2 Y T H E hY hT hH hE,
    (by norm_num),
    cert_h2_e2_old_peak_3 Y T H E hY hT hH hE,
    (by norm_num),
    cert_h2_e2_new_peak_3 Y T H E hY hT hH hE⟩

private theorem cert_h2_t8_old_seam_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-r*v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      14878 +
      29212*E +
      14336*E^2 +
      5764*T +
      11396*T*E +
      5632*T*E^2 +
      744*T^2 +
      1480*T^2*E +
      736*T^2*E^2 +
      32*T^3 +
      64*T^3*E +
      32*T^3*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_old_peak_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.L-1-2*(v.L-r*v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1794 +
      3844*E +
      2048*E^2 +
      448*T +
      960*T*E +
      512*T*E^2 +
      28*T^2 +
      60*T^2*E +
      32*T^2*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_seam_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Ln-r*v.Bn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      29694 +
      58364*E +
      28672*E^2 +
      11520*T +
      22784*T*E +
      11264*T*E^2 +
      1488*T^2 +
      2960*T^2*E +
      1472*T^2*E^2 +
      64*T^3 +
      128*T^3*E +
      64*T^3*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_peak_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.Ln-1-2*(v.Ln-r*v.Bn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      3618 +
      7716*E +
      4096*E^2 +
      900*T +
      1924*T*E +
      1024*T*E^2 +
      56*T^2 +
      120*T^2*E +
      64*T^2*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_old_seam_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.M-C) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      4050 +
      4032*E +
      1530*T +
      1528*T*E +
      192*T^2 +
      192*T^2*E +
      8*T^3 +
      8*T^3*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_old_peak_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.B-1-2*(v.M-C) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      566 +
      576*E +
      135*T +
      136*T*E +
      8*T^2 +
      8*T^2*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_seam_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Mn-2*C-v.z-1) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      7504 +
      7488*E +
      2922*T +
      2920*T*E +
      376*T^2 +
      376*T^2*E +
      16*T^3 +
      16*T^3*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_peak_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.Bn-1-2*(v.Mn-2*C-v.z-1) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1728 +
      1728*E +
      408*T +
      408*T*E +
      24*T^2 +
      24*T^2*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_old_seam_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-R*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      964 +
      6100*E +
      5120*E^2 +
      762*T +
      3068*T*E +
      2304*T*E^2 +
      144*T^2 +
      480*T^2*E +
      336*T^2*E^2 +
      8*T^3 +
      24*T^3*E +
      16*T^3*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_old_peak_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.A-1-2*(v.L-R*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      15996 +
      27244*E +
      11264*E^2 +
      5518*T +
      9356*T*E +
      3840*T*E^2 +
      632*T^2 +
      1064*T^2*E +
      432*T^2*E^2 +
      24*T^3 +
      40*T^3*E +
      16*T^3*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_seam_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Ln-R*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      5572 +
      18900*E +
      13312*E^2 +
      2426*T +
      7804*T*E +
      5376*T*E^2 +
      344*T^2 +
      1064*T^2*E +
      720*T^2*E^2 +
      16*T^3 +
      48*T^3*E +
      32*T^3*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_peak_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.A-1-2*(v.Ln-R*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      11388 +
      14444*E +
      3072*E^2 +
      3854*T +
      4620*T*E +
      768*T*E^2 +
      432*T^2 +
      480*T^2*E +
      48*T^2*E^2 +
      16*T^3 +
      16*T^3*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_old_peak_3 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.M-1-2*(0) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2312 +
      2304*E +
      833*T +
      832*T*E +
      100*T^2 +
      100*T^2*E +
      4*T^3 +
      4*T^3*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t8_new_peak_3 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.Mn-1-2*(0) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      4360 +
      4352*E +
      1601*T +
      1600*T*E +
      196*T^2 +
      196*T^2*E +
      8*T^3 +
      8*T^3*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h2_t8 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (8+T) (8+T) (4*(1+E)) (2)
  let r : ℤ := 2*(1+E)
  let R : ℤ := 6*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-r*v.B) ∧
  0 ≤ v.L-1-2*(v.L-r*v.B) ∧
  0 ≤ 2*(v.Ln-r*v.Bn) ∧
  0 ≤ v.Ln-1-2*(v.Ln-r*v.Bn) ∧
  0 ≤ 2*(v.M-C) ∧
  0 ≤ v.B-1-2*(v.M-C) ∧
  0 ≤ 2*(v.Mn-2*C-v.z-1) ∧
  0 ≤ v.Bn-1-2*(v.Mn-2*C-v.z-1) ∧
  0 ≤ 2*(v.L-R*v.M) ∧
  0 ≤ v.A-1-2*(v.L-R*v.M) ∧
  0 ≤ 2*(v.Ln-R*v.Mn) ∧
  0 ≤ v.A-1-2*(v.Ln-R*v.Mn) ∧
  0 ≤ 2*(0) ∧
  0 ≤ v.M-1-2*(0) ∧
  0 ≤ 2*(0) ∧
  0 ≤ v.Mn-1-2*(0) := by
  exact ⟨cert_h2_t8_old_seam_0 Y T H E hY hT hH hE,
    cert_h2_t8_old_peak_0 Y T H E hY hT hH hE,
    cert_h2_t8_new_seam_0 Y T H E hY hT hH hE,
    cert_h2_t8_new_peak_0 Y T H E hY hT hH hE,
    cert_h2_t8_old_seam_1 Y T H E hY hT hH hE,
    cert_h2_t8_old_peak_1 Y T H E hY hT hH hE,
    cert_h2_t8_new_seam_1 Y T H E hY hT hH hE,
    cert_h2_t8_new_peak_1 Y T H E hY hT hH hE,
    cert_h2_t8_old_seam_2 Y T H E hY hT hH hE,
    cert_h2_t8_old_peak_2 Y T H E hY hT hH hE,
    cert_h2_t8_new_seam_2 Y T H E hY hT hH hE,
    cert_h2_t8_new_peak_2 Y T H E hY hT hH hE,
    (by norm_num),
    cert_h2_t8_old_peak_3 Y T H E hY hT hH hE,
    (by norm_num),
    cert_h2_t8_new_peak_3 Y T H E hY hT hH hE⟩

private theorem cert_h2_t4_e16_old_seam_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-r*v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      25138 +
      49712*E +
      24576*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_old_peak_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.L-1-2*(v.L-r*v.B) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      7950 +
      16144*E +
      8192*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_seam_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Ln-r*v.Bn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      50162 +
      99312*E +
      49152*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_peak_0 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.Ln-1-2*(v.Ln-r*v.Bn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      15950 +
      32336*E +
      16384*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_old_seam_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.M-C) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1930 +
      1920*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_old_peak_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.B-1-2*(v.M-C) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      634 +
      640*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_seam_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Mn-2*C-v.z-1) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      3208 +
      3200*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_peak_1 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.Bn-1-2*(v.Mn-2*C-v.z-1) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1920 +
      1920*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_old_seam_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-R*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1928 +
      6032*E +
      4096*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_old_peak_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.A-1-2*(v.L-R*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      31480 +
      60144*E +
      28672*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_seam_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.Ln-R*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      16776 +
      37264*E +
      20480*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_peak_2 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.A-1-2*(v.Ln-R*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      16632 +
      28912*E +
      12288*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_old_peak_3 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.M-1-2*(0) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1284 +
      1280*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_h2_t4_e16_new_peak_3 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ v.Mn-1-2*(0) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2308 +
      2304*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_h2_t4_e16 (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4) (4) (16*(1+E)) (2)
  let r : ℤ := 8*(1+E)
  let R : ℤ := 24*(1+E)+1
  let C := (v.t+1)*v.z
  0 ≤ 2*(v.L-r*v.B) ∧
  0 ≤ v.L-1-2*(v.L-r*v.B) ∧
  0 ≤ 2*(v.Ln-r*v.Bn) ∧
  0 ≤ v.Ln-1-2*(v.Ln-r*v.Bn) ∧
  0 ≤ 2*(v.M-C) ∧
  0 ≤ v.B-1-2*(v.M-C) ∧
  0 ≤ 2*(v.Mn-2*C-v.z-1) ∧
  0 ≤ v.Bn-1-2*(v.Mn-2*C-v.z-1) ∧
  0 ≤ 2*(v.L-R*v.M) ∧
  0 ≤ v.A-1-2*(v.L-R*v.M) ∧
  0 ≤ 2*(v.Ln-R*v.Mn) ∧
  0 ≤ v.A-1-2*(v.Ln-R*v.Mn) ∧
  0 ≤ 2*(0) ∧
  0 ≤ v.M-1-2*(0) ∧
  0 ≤ 2*(0) ∧
  0 ≤ v.Mn-1-2*(0) := by
  exact ⟨cert_h2_t4_e16_old_seam_0 Y T H E hY hT hH hE,
    cert_h2_t4_e16_old_peak_0 Y T H E hY hT hH hE,
    cert_h2_t4_e16_new_seam_0 Y T H E hY hT hH hE,
    cert_h2_t4_e16_new_peak_0 Y T H E hY hT hH hE,
    cert_h2_t4_e16_old_seam_1 Y T H E hY hT hH hE,
    cert_h2_t4_e16_old_peak_1 Y T H E hY hT hH hE,
    cert_h2_t4_e16_new_seam_1 Y T H E hY hT hH hE,
    cert_h2_t4_e16_new_peak_1 Y T H E hY hT hH hE,
    cert_h2_t4_e16_old_seam_2 Y T H E hY hT hH hE,
    cert_h2_t4_e16_old_peak_2 Y T H E hY hT hH hE,
    cert_h2_t4_e16_new_seam_2 Y T H E hY hT hH hE,
    cert_h2_t4_e16_new_peak_2 Y T H E hY hT hH hE,
    (by norm_num),
    cert_h2_t4_e16_old_peak_3 Y T H E hY hT hH hE,
    (by norm_num),
    cert_h2_t4_e16_new_peak_3 Y T H E hY hT hH hE⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
