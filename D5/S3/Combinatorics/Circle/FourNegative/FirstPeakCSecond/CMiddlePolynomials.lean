/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/CMiddlePolynomials
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.Basic]
   utility: none
   digest: Row/model and the 16 exact strict S1/S2 coefficient identities. -/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
structure Row where
  x : ℤ
  y : ℤ
  z : ℤ
  t : ℤ
  D : ℤ
  A : ℤ
  B : ℤ
  L : ℤ
  M : ℤ
  Bn : ℤ
  Ln : ℤ
  Mn : ℤ

def model (y t e h : ℤ) : Row :=
  let z := e*t
  let x := e*h*t
  let D := y*z+y+1
  let A := x*D+1
  let B := x*t*(y+1)+t+1
  let L := x*z*t+z*t+z+1
  let M := t*y*z+D
  ⟨x,y,z,t,D,A,B,L,M,2*B-1,2*L-z-1,2*M-D⟩

/- Exact sparse coefficient identities. Each expansion below is a Lean expression;
ring checks the identity and positivity checks its nonnegativity. No JSON premise,
finite sampling, native evaluator, or certificate oracle occurs in the proof. -/

private theorem cert_strict_adjacent_old_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.t*v.A-2*s*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1404 +
      698*H +
      333*T +
      166*T*H +
      20*T^2 +
      10*T^2*H +
      958*Y +
      478*Y*H +
      148*Y*T +
      74*Y*T*H +
      4*Y*T^2 +
      2*Y*T^2*H +
      216*Y^2 +
      108*Y^2*H +
      16*Y^2*T +
      8*Y^2*T*H +
      16*Y^3 +
      8*Y^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_old_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      804 +
      406*H +
      199*T +
      100*T*H +
      12*T^2 +
      6*T^2*H +
      650*Y +
      326*Y*H +
      112*Y*T +
      56*Y*T*H +
      4*Y*T^2 +
      2*Y*T^2*H +
      176*Y^2 +
      88*Y^2*H +
      16*Y^2*T +
      8*Y^2*T*H +
      16*Y^3 +
      8*Y^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_new_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      322 +
      154*H +
      102*T +
      50*T*H +
      8*T^2 +
      4*T^2*H +
      176*Y +
      86*Y*H +
      28*Y*T +
      14*Y*T*H +
      24*Y^2 +
      12*Y^2*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_new_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1886 +
      950*H +
      430*T +
      216*T*H +
      24*T^2 +
      12*T^2*H +
      1432*Y +
      718*Y*H +
      232*Y*T +
      116*Y*T*H +
      8*Y*T^2 +
      4*Y*T^2*H +
      368*Y^2 +
      184*Y^2*H +
      32*Y^2*T +
      16*Y^2*T*H +
      32*Y^3 +
      16*Y^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      24935 +
      327680*H +
      27312*T +
      163840*T*H +
      7696*T^2 +
      30720*T^2*H +
      840*T^3 +
      2560*T^3*H +
      32*T^4 +
      80*T^4*H +
      33590*Y +
      475136*Y*H +
      27740*Y*T +
      196608*Y*T*H +
      5772*Y*T^2 +
      29184*Y*T^2*H +
      418*Y*T^3 +
      1792*Y*T^3*H +
      8*Y*T^4 +
      36*Y*T^4*H +
      17879*Y^2 +
      286720*Y^2*H +
      10540*Y^2*T +
      94208*Y^2*T*H +
      1442*Y^2*T^2 +
      10368*Y^2*T^2*H +
      52*Y^2*T^3 +
      416*Y^2*T^3*H +
      4*Y^2*T^4*H +
      4712*Y^3 +
      92160*Y^3*H +
      1776*Y^3*T +
      22528*Y^3*T*H +
      120*Y^3*T^2 +
      1632*Y^3*T^2*H +
      32*Y^3*T^3*H +
      616*Y^4 +
      16640*Y^4*H +
      112*Y^4*T +
      2688*Y^4*T*H +
      96*Y^4*T^2*H +
      32*Y^5 +
      1600*Y^5*H +
      128*Y^5*T*H +
      64*Y^6*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      897 +
      453*H +
      207*T +
      104*T*H +
      12*T^2 +
      6*T^2*H +
      704*Y +
      353*Y*H +
      116*Y*T +
      58*Y*T*H +
      4*Y*T^2 +
      2*Y*T^2*H +
      184*Y^2 +
      92*Y^2*H +
      16*Y^2*T +
      8*Y^2*T*H +
      16*Y^3 +
      8*Y^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_third_gate_width (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.L-2*v.B-g*v.D := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1525 +
      699*H +
      912*T +
      440*T*H +
      154*T^2 +
      76*T^2*H +
      8*T^3 +
      4*T^3*H +
      1278*Y +
      607*Y*H +
      484*Y*T +
      238*Y*T*H +
      40*Y*T^2 +
      20*Y*T^2*H +
      352*Y^2 +
      172*Y^2*H +
      64*Y^2*T +
      32*Y^2*T*H +
      32*Y^3 +
      16*Y^3*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_adjacent_w_capacity_strict (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.z*v.B-2*v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      12141 +
      6144*H +
      4574*T +
      2304*T*H +
      574*T^2 +
      288*T^2*H +
      24*T^3 +
      12*T^3*H +
      13244*Y +
      6656*Y*H +
      3832*Y*T +
      1920*Y*T*H +
      336*Y*T^2 +
      168*Y*T^2*H +
      8*Y*T^3 +
      4*Y*T^3*H +
      5368*Y^2 +
      2688*Y^2*H +
      1056*Y^2*T +
      528*Y^2*T*H +
      48*Y^2*T^2 +
      24*Y^2*T^2*H +
      960*Y^3 +
      480*Y^3*H +
      96*Y^3*T +
      48*Y^3*T*H +
      64*Y^4 +
      32*Y^4*H from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_strict_adjacent (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) 2 (2+H)
  let g : ℤ := (2+H)
  let s : ℤ := (2+H)*(v.t-1)
  0 ≤ v.t*v.A-2*s*v.M ∧
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) ∧
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ v.L-2*v.B-g*v.D ∧
  0 ≤ v.z*v.B-2*v.L-1 := by
  exact ⟨cert_strict_adjacent_old_first_lower Y T H E hY hT hH hE,
    cert_strict_adjacent_old_first_peak Y T H E hY hT hH hE,
    cert_strict_adjacent_new_first_lower Y T H E hY hT hH hE,
    cert_strict_adjacent_new_first_peak Y T H E hY hT hH hE,
    cert_strict_adjacent_ceil_old_bank Y T H E hY hT hH hE,
    cert_strict_adjacent_r_capacity Y T H E hY hT hH hE,
    cert_strict_adjacent_third_gate_width Y T H E hY hT hH hE,
    cert_strict_adjacent_w_capacity_strict Y T H E hY hT hH hE⟩

private theorem cert_strict_separated_old_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.t*v.A-2*s*v.M := by
  dsimp only
  convert (show (0 : ℤ) ≤
      7940 +
      13564*E +
      5632*E^2 +
      3966*H +
      6782*H*E +
      2816*H*E^2 +
      1817*T +
      3032*T*E +
      1216*T*E^2 +
      908*T*H +
      1516*T*H*E +
      608*T*H*E^2 +
      104*T^2 +
      168*T^2*E +
      64*T^2*E^2 +
      52*T^2*H +
      84*T^2*H*E +
      32*T^2*H*E^2 +
      5502*Y +
      9340*Y*E +
      3840*Y*E^2 +
      2750*Y*H +
      4670*Y*H*E +
      1920*Y*H*E^2 +
      840*Y*T +
      1400*Y*T*E +
      560*Y*T*E^2 +
      420*Y*T*H +
      700*Y*T*H*E +
      280*Y*T*H*E^2 +
      24*Y*T^2 +
      40*Y*T^2*E +
      16*Y*T^2*E^2 +
      12*Y*T^2*H +
      20*Y*T^2*H*E +
      8*Y*T^2*H*E^2 +
      1264*Y^2 +
      2128*Y^2*E +
      864*Y^2*E^2 +
      632*Y^2*H +
      1064*Y^2*H*E +
      432*Y^2*H*E^2 +
      96*Y^2*T +
      160*Y^2*T*E +
      64*Y^2*T*E^2 +
      48*Y^2*T*H +
      80*Y^2*T*H*E +
      32*Y^2*T*H*E^2 +
      96*Y^3 +
      160*Y^3*E +
      64*Y^3*E^2 +
      48*Y^3*H +
      80*Y^3*H*E +
      32*Y^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_separated_old_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      572 +
      3140*E +
      2560*E^2 +
      290*H +
      1570*H*E +
      1280*H*E^2 +
      271*T +
      1104*T*E +
      832*T*E^2 +
      136*T*H +
      552*T*H*E +
      416*T*H*E^2 +
      24*T^2 +
      88*T^2*E +
      64*T^2*E^2 +
      12*T^2*H +
      44*T^2*H*E +
      32*T^2*H*E^2 +
      786*Y +
      3092*Y*E +
      2304*Y*E^2 +
      394*Y*H +
      1546*Y*H*E +
      1152*Y*H*E^2 +
      192*Y*T +
      656*Y*T*E +
      464*Y*T*E^2 +
      96*Y*T*H +
      328*Y*T*H*E +
      232*Y*T*H*E^2 +
      8*Y*T^2 +
      24*Y*T^2*E +
      16*Y*T^2*E^2 +
      4*Y*T^2*H +
      12*Y*T^2*H*E +
      8*Y*T^2*H*E^2 +
      288*Y^2 +
      960*Y^2*E +
      672*Y^2*E^2 +
      144*Y^2*H +
      480*Y^2*H*E +
      336*Y^2*H*E^2 +
      32*Y^2*T +
      96*Y^2*T*E +
      64*Y^2*T*E^2 +
      16*Y^2*T*H +
      48*Y^2*T*H*E +
      32*Y^2*T*H*E^2 +
      32*Y^3 +
      96*Y^3*E +
      64*Y^3*E^2 +
      16*Y^3*H +
      48*Y^3*H*E +
      32*Y^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_separated_new_first_lower (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      5770 +
      7292*E +
      1536*E^2 +
      2878*H +
      3646*H*E +
      768*H*E^2 +
      1354*T +
      1544*T*E +
      192*T*E^2 +
      676*T*H +
      772*T*H*E +
      96*T*H*E^2 +
      80*T^2 +
      80*T^2*E +
      40*T^2*H +
      40*T^2*H*E +
      3936*Y +
      4700*Y*E +
      768*Y*E^2 +
      1966*Y*H +
      2350*Y*H*E +
      384*Y*H*E^2 +
      600*Y*T +
      648*Y*T*E +
      48*Y*T*E^2 +
      300*Y*T*H +
      324*Y*T*H*E +
      24*Y*T*H*E^2 +
      16*Y*T^2 +
      16*Y*T^2*E +
      8*Y*T^2*H +
      8*Y*T^2*H*E +
      880*Y^2 +
      976*Y^2*E +
      96*Y^2*E^2 +
      440*Y^2*H +
      488*Y^2*H*E +
      48*Y^2*H*E^2 +
      64*Y^2*T +
      64*Y^2*T*E +
      32*Y^2*T*H +
      32*Y^2*T*H*E +
      64*Y^3 +
      64*Y^3*E +
      32*Y^3*H +
      32*Y^3*H*E from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_separated_new_first_peak (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) := by
  dsimp only
  convert (show (0 : ℤ) ≤
      2742 +
      9412*E +
      6656*E^2 +
      1378*H +
      4706*H*E +
      3328*H*E^2 +
      734*T +
      2592*T*E +
      1856*T*E^2 +
      368*T*H +
      1296*T*H*E +
      928*T*H*E^2 +
      48*T^2 +
      176*T^2*E +
      128*T^2*E^2 +
      24*T^2*H +
      88*T^2*H*E +
      64*T^2*H*E^2 +
      2352*Y +
      7732*Y*E +
      5376*Y*E^2 +
      1178*Y*H +
      3866*Y*H*E +
      2688*Y*H*E^2 +
      432*Y*T +
      1408*Y*T*E +
      976*Y*T*E^2 +
      216*Y*T*H +
      704*Y*T*H*E +
      488*Y*T*H*E^2 +
      16*Y*T^2 +
      48*Y*T^2*E +
      32*Y*T^2*E^2 +
      8*Y*T^2*H +
      24*Y*T^2*H*E +
      16*Y*T^2*H*E^2 +
      672*Y^2 +
      2112*Y^2*E +
      1440*Y^2*E^2 +
      336*Y^2*H +
      1056*Y^2*H*E +
      720*Y^2*H*E^2 +
      64*Y^2*T +
      192*Y^2*T*E +
      128*Y^2*T*E^2 +
      32*Y^2*T*H +
      96*Y^2*T*H*E +
      64*Y^2*T*H*E^2 +
      64*Y^3 +
      192*Y^3*E +
      128*Y^3*E^2 +
      32*Y^3*H +
      96*Y^3*H*E +
      64*Y^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

set_option maxHeartbeats 2000000 in
private theorem cert_strict_separated_ceil_old_bank (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn := by
  dsimp only
  convert (show (0 : ℤ) ≤
      107239 +
      221952*E +
      114688*E^2 +
      1310720*H +
      2621440*H*E +
      1310720*H*E^2 +
      109920*T +
      220512*T*E +
      110592*T*E^2 +
      655360*T*H +
      1310720*T*H*E +
      655360*T*H*E^2 +
      30624*T^2 +
      61088*T^2*E +
      30464*T^2*E^2 +
      122880*T^2*H +
      245760*T^2*H*E +
      122880*T^2*H*E^2 +
      3344*T^3 +
      6672*T^3*E +
      3328*T^3*E^2 +
      10240*T^3*H +
      20480*T^3*H*E +
      10240*T^3*H*E^2 +
      128*T^4 +
      256*T^4*E +
      128*T^4*E^2 +
      320*T^4*H +
      640*T^4*H*E +
      320*T^4*H*E^2 +
      140918*Y +
      288384*Y*E +
      147456*Y*E^2 +
      1900544*Y*H +
      3801088*Y*H*E +
      1900544*Y*H*E^2 +
      111288*Y*T +
      222904*Y*T*E +
      111616*Y*T*E^2 +
      786432*Y*T*H +
      1572864*Y*T*H*E +
      786432*Y*T*H*E^2 +
      23000*Y*T^2 +
      45912*Y*T^2*E +
      22912*Y*T^2*E^2 +
      116736*Y*T^2*H +
      233472*Y*T^2*H*E +
      116736*Y*T^2*H*E^2 +
      1668*Y*T^3 +
      3332*Y*T^3*E +
      1664*Y*T^3*E^2 +
      7168*Y*T^3*H +
      14336*Y*T^3*H*E +
      7168*Y*T^3*H*E^2 +
      32*Y*T^4 +
      64*Y*T^4*E +
      32*Y*T^4*E^2 +
      144*Y*T^4*H +
      288*Y*T^4*H*E +
      144*Y*T^4*H*E^2 +
      73647*Y^2 +
      149424*Y^2*E +
      75776*Y^2*E^2 +
      1146880*Y^2*H +
      2293760*Y^2*H*E +
      1146880*Y^2*H*E^2 +
      42200*Y^2*T +
      84440*Y^2*T*E +
      42240*Y^2*T*E^2 +
      376832*Y^2*T*H +
      753664*Y^2*T*H*E +
      376832*Y^2*T*H*E^2 +
      5756*Y^2*T^2 +
      11500*Y^2*T^2*E +
      5744*Y^2*T^2*E^2 +
      41472*Y^2*T^2*H +
      82944*Y^2*T^2*H*E +
      41472*Y^2*T^2*H*E^2 +
      208*Y^2*T^3 +
      416*Y^2*T^3*E +
      208*Y^2*T^3*E^2 +
      1664*Y^2*T^3*H +
      3328*Y^2*T^3*H*E +
      1664*Y^2*T^3*H*E^2 +
      16*Y^2*T^4*H +
      32*Y^2*T^4*H*E +
      16*Y^2*T^4*H*E^2 +
      19152*Y^3 +
      38608*Y^3*E +
      19456*Y^3*E^2 +
      368640*Y^3*H +
      737280*Y^3*H*E +
      368640*Y^3*H*E^2 +
      7104*Y^3*T +
      14208*Y^3*T*E +
      7104*Y^3*T*E^2 +
      90112*Y^3*T*H +
      180224*Y^3*T*H*E +
      90112*Y^3*T*H*E^2 +
      480*Y^3*T^2 +
      960*Y^3*T^2*E +
      480*Y^3*T^2*E^2 +
      6528*Y^3*T^2*H +
      13056*Y^3*T^2*H*E +
      6528*Y^3*T^2*H*E^2 +
      128*Y^3*T^3*H +
      256*Y^3*T^3*H*E +
      128*Y^3*T^3*H*E^2 +
      2480*Y^4 +
      4976*Y^4*E +
      2496*Y^4*E^2 +
      66560*Y^4*H +
      133120*Y^4*H*E +
      66560*Y^4*H*E^2 +
      448*Y^4*T +
      896*Y^4*T*E +
      448*Y^4*T*E^2 +
      10752*Y^4*T*H +
      21504*Y^4*T*H*E +
      10752*Y^4*T*H*E^2 +
      384*Y^4*T^2*H +
      768*Y^4*T^2*H*E +
      384*Y^4*T^2*H*E^2 +
      128*Y^5 +
      256*Y^5*E +
      128*Y^5*E^2 +
      6400*Y^5*H +
      12800*Y^5*H*E +
      6400*Y^5*H*E^2 +
      512*Y^5*T*H +
      1024*Y^5*T*H*E +
      512*Y^5*T*H*E^2 +
      256*Y^6*H +
      512*Y^6*H*E +
      256*Y^6*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_separated_r_capacity (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ g*v.Mn-v.B := by
  dsimp only
  convert (show (0 : ℤ) ≤
      1793 +
      6154*E +
      4352*E^2 +
      901*H +
      3077*H*E +
      2176*H*E^2 +
      415*T +
      1472*T*E +
      1056*T*E^2 +
      208*T*H +
      736*T*H*E +
      528*T*H*E^2 +
      24*T^2 +
      88*T^2*E +
      64*T^2*E^2 +
      12*T^2*H +
      44*T^2*H*E +
      32*T^2*H*E^2 +
      1408*Y +
      4610*Y*E +
      3200*Y*E^2 +
      705*Y*H +
      2305*Y*H*E +
      1600*Y*H*E^2 +
      232*Y*T +
      752*Y*T*E +
      520*Y*T*E^2 +
      116*Y*T*H +
      376*Y*T*H*E +
      260*Y*T*H*E^2 +
      8*Y*T^2 +
      24*Y*T^2*E +
      16*Y*T^2*E^2 +
      4*Y*T^2*H +
      12*Y*T^2*H*E +
      8*Y*T^2*H*E^2 +
      368*Y^2 +
      1152*Y^2*E +
      784*Y^2*E^2 +
      184*Y^2*H +
      576*Y^2*H*E +
      392*Y^2*H*E^2 +
      32*Y^2*T +
      96*Y^2*T*E +
      64*Y^2*T*E^2 +
      16*Y^2*T*H +
      48*Y^2*T*H*E +
      32*Y^2*T*H*E^2 +
      32*Y^3 +
      96*Y^3*E +
      64*Y^3*E^2 +
      16*Y^3*H +
      48*Y^3*H*E +
      32*Y^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_separated_third_gate_width (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.L-2*v.B-g*v.D := by
  dsimp only
  convert (show (0 : ℤ) ≤
      11269 +
      27414*E +
      16128*E^2 +
      5499*H +
      13563*H*E +
      8064*H*E^2 +
      4898*T +
      11012*T*E +
      6112*T*E^2 +
      2416*T*H +
      5472*T*H*E +
      3056*T*H*E^2 +
      692*T^2 +
      1460*T^2*E +
      768*T^2*E^2 +
      344*T^2*H +
      728*T^2*H*E +
      384*T^2*H*E^2 +
      32*T^3 +
      64*T^3*E +
      32*T^3*E^2 +
      16*T^3*H +
      32*T^3*H*E +
      16*T^3*H*E^2 +
      8706*Y +
      20870*Y*E +
      12160*Y*E^2 +
      4287*Y*H +
      10367*Y*H*E +
      6080*Y*H*E^2 +
      2504*Y*T +
      5568*Y*T*E +
      3064*Y*T*E^2 +
      1244*Y*T*H +
      2776*Y*T*H*E +
      1532*Y*T*H*E^2 +
      176*Y*T^2 +
      368*Y*T^2*E +
      192*Y*T^2*E^2 +
      88*Y*T^2*H +
      184*Y*T^2*H*E +
      96*Y*T^2*H*E^2 +
      2240*Y^2 +
      5296*Y^2*E +
      3056*Y^2*E^2 +
      1112*Y^2*H +
      2640*Y^2*H*E +
      1528*Y^2*H*E^2 +
      320*Y^2*T +
      704*Y^2*T*E +
      384*Y^2*T*E^2 +
      160*Y^2*T*H +
      352*Y^2*T*H*E +
      192*Y^2*T*H*E^2 +
      192*Y^3 +
      448*Y^3*E +
      256*Y^3*E^2 +
      96*Y^3*H +
      224*Y^3*H*E +
      128*Y^3*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem cert_strict_separated_w_capacity_strict (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.z*v.B-2*v.L-1 := by
  dsimp only
  convert (show (0 : ℤ) ≤
      48861 +
      98016*E +
      49152*E^2 +
      24576*H +
      49152*H*E +
      24576*H*E^2 +
      18364*T +
      36796*T*E +
      18432*T*E^2 +
      9216*T*H +
      18432*T*H*E +
      9216*T*H*E^2 +
      2300*T^2 +
      4604*T^2*E +
      2304*T^2*E^2 +
      1152*T^2*H +
      2304*T^2*H*E +
      1152*T^2*H*E^2 +
      96*T^3 +
      192*T^3*E +
      96*T^3*E^2 +
      48*T^3*H +
      96*T^3*H*E +
      48*T^3*H*E^2 +
      53112*Y +
      106360*Y*E +
      53248*Y*E^2 +
      26624*Y*H +
      53248*Y*H*E +
      26624*Y*H*E^2 +
      15344*Y*T +
      30704*Y*T*E +
      15360*Y*T*E^2 +
      7680*Y*T*H +
      15360*Y*T*H*E +
      7680*Y*T*H*E^2 +
      1344*Y*T^2 +
      2688*Y*T^2*E +
      1344*Y*T^2*E^2 +
      672*Y*T^2*H +
      1344*Y*T^2*H*E +
      672*Y*T^2*H*E^2 +
      32*Y*T^3 +
      64*Y*T^3*E +
      32*Y*T^3*E^2 +
      16*Y*T^3*H +
      32*Y*T^3*H*E +
      16*Y*T^3*H*E^2 +
      21488*Y^2 +
      42992*Y^2*E +
      21504*Y^2*E^2 +
      10752*Y^2*H +
      21504*Y^2*H*E +
      10752*Y^2*H*E^2 +
      4224*Y^2*T +
      8448*Y^2*T*E +
      4224*Y^2*T*E^2 +
      2112*Y^2*T*H +
      4224*Y^2*T*H*E +
      2112*Y^2*T*H*E^2 +
      192*Y^2*T^2 +
      384*Y^2*T^2*E +
      192*Y^2*T^2*E^2 +
      96*Y^2*T^2*H +
      192*Y^2*T^2*H*E +
      96*Y^2*T^2*H*E^2 +
      3840*Y^3 +
      7680*Y^3*E +
      3840*Y^3*E^2 +
      1920*Y^3*H +
      3840*Y^3*H*E +
      1920*Y^3*H*E^2 +
      384*Y^3*T +
      768*Y^3*T*E +
      384*Y^3*T*E^2 +
      192*Y^3*T*H +
      384*Y^3*T*H*E +
      192*Y^3*T*H*E^2 +
      256*Y^4 +
      512*Y^4*E +
      256*Y^4*E^2 +
      128*Y^4*H +
      256*Y^4*H*E +
      128*Y^4*H*E^2 from by positivity) using 1 <;>
    dsimp [model] <;> ring

private theorem margins_strict_separated (Y T H E : ℤ)
    (hY : 0 ≤ Y) (hT : 0 ≤ T) (hH : 0 ≤ H) (hE : 0 ≤ E) :
  let v := model (4+Y) (2*(4+Y)+T) (4*(1+E)) (2+H)
  let g : ℤ := (1+E)*(2+H)
  let s : ℤ := (1+E)*(2+H)*(2*v.t-3)
  0 ≤ v.t*v.A-2*s*v.M ∧
  0 ≤ v.A-1-(v.t*v.A-2*s*v.M) ∧
  0 ≤ 2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0 ≤ v.B*v.t*v.y*v.z-v.M*v.Mn ∧
  0 ≤ g*v.Mn-v.B ∧
  0 ≤ v.L-2*v.B-g*v.D ∧
  0 ≤ v.z*v.B-2*v.L-1 := by
  exact ⟨cert_strict_separated_old_first_lower Y T H E hY hT hH hE,
    cert_strict_separated_old_first_peak Y T H E hY hT hH hE,
    cert_strict_separated_new_first_lower Y T H E hY hT hH hE,
    cert_strict_separated_new_first_peak Y T H E hY hT hH hE,
    cert_strict_separated_ceil_old_bank Y T H E hY hT hH hE,
    cert_strict_separated_r_capacity Y T H E hY hT hH hE,
    cert_strict_separated_third_gate_width Y T H E hY hT hH hE,
    cert_strict_separated_w_capacity_strict Y T H E hY hT hH hE⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
