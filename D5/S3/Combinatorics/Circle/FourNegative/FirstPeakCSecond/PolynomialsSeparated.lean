/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/PolynomialsSeparated
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Nine tight-quotient identities and the separated C3 chart. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials
import Mathlib.Tactic.Linarith.Frontend
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
open private UniformBounds uniformBounds_mk
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials

set_option maxHeartbeats 1600000 in
private theorem separated_old_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ t*A-2*s*M := by
  dsimp only
  calc
    0 ≤ 16284 +
        30616*E +
        14336*E^2 +
        16280*J +
        30616*J*E +
        14336*J*E^2 +
        10657*T +
        19872*T*E +
        9216*T*E^2 +
        10656*T*J +
        19872*T*J*E +
        9216*T*J*E^2 +
        2288*T^2 +
        4208*T^2*E +
        1920*T^2*E^2 +
        2288*T^2*J +
        4208*T^2*J*E +
        1920*T^2*J*E^2 +
        160*T^3 +
        288*T^3*E +
        128*T^3*E^2 +
        160*T^3*J +
        288*T^3*J*E +
        128*T^3*J*E^2 +
        46680*Y +
        89688*Y*E +
        43008*Y*E^2 +
        46680*Y*J +
        89688*Y*J*E +
        43008*Y*J*E^2 +
        30416*Y*T +
        58064*Y*T*E +
        27648*Y*T*E^2 +
        30416*Y*T*J +
        58064*Y*T*J*E +
        27648*Y*T*J*E^2 +
        6480*Y*T^2 +
        12240*Y*T^2*E +
        5760*Y*T^2*E^2 +
        6480*Y*T^2*J +
        12240*Y*T^2*J*E +
        5760*Y*T^2*J*E^2 +
        448*Y*T^3 +
        832*Y*T^3*E +
        384*Y*T^3*E^2 +
        448*Y*T^3*J +
        832*Y*T^3*J*E +
        384*Y*T^3*J*E^2 +
        44736*Y^2 +
        87744*Y^2*E +
        43008*Y^2*E^2 +
        44736*Y^2*J +
        87744*Y^2*J*E +
        43008*Y^2*J*E^2 +
        28976*Y^2*T +
        56624*Y^2*T*E +
        27648*Y^2*T*E^2 +
        28976*Y^2*T*J +
        56624*Y^2*T*J*E +
        27648*Y^2*T*J*E^2 +
        6112*Y^2*T^2 +
        11872*Y^2*T^2*E +
        5760*Y^2*T^2*E^2 +
        6112*Y^2*T^2*J +
        11872*Y^2*T^2*J*E +
        5760*Y^2*T^2*J*E^2 +
        416*Y^2*T^3 +
        800*Y^2*T^3*E +
        384*Y^2*T^3*E^2 +
        416*Y^2*T^3*J +
        800*Y^2*T^3*J*E +
        384*Y^2*T^3*J*E^2 +
        14336*Y^3 +
        28672*Y^3*E +
        14336*Y^3*E^2 +
        14336*Y^3*J +
        28672*Y^3*J*E +
        14336*Y^3*J*E^2 +
        9216*Y^3*T +
        18432*Y^3*T*E +
        9216*Y^3*T*E^2 +
        9216*Y^3*T*J +
        18432*Y^3*T*J*E +
        9216*Y^3*T*J*E^2 +
        1920*Y^3*T^2 +
        3840*Y^3*T^2*E +
        1920*Y^3*T^2*E^2 +
        1920*Y^3*T^2*J +
        3840*Y^3*T^2*J*E +
        1920*Y^3*T^2*J*E^2 +
        128*Y^3*T^3 +
        256*Y^3*T^3*E +
        128*Y^3*T^3*E^2 +
        128*Y^3*T^3*J +
        256*Y^3*T^3*J*E +
        128*Y^3*T^3*J*E^2 := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_old_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ A-1-(t*A-2*s*M) := by
  dsimp only
  calc
    0 ≤ 676 +
        2728*E +
        2048*E^2 +
        680*J +
        2728*J*E +
        2048*J*E^2 +
        1903*T +
        4976*T*E +
        3072*T*E^2 +
        1904*T*J +
        4976*T*J*E +
        3072*T*J*E^2 +
        816*T^2 +
        1968*T^2*E +
        1152*T^2*E^2 +
        816*T^2*J +
        1968*T^2*J*E +
        1152*T^2*J*E^2 +
        96*T^3 +
        224*T^3*E +
        128*T^3*E^2 +
        96*T^3*J +
        224*T^3*J*E +
        128*T^3*J*E^2 +
        3560*Y +
        9704*Y*E +
        6144*Y*E^2 +
        3560*Y*J +
        9704*Y*J*E +
        6144*Y*J*E^2 +
        6976*Y*T +
        16192*Y*T*E +
        9216*Y*T*E^2 +
        6976*Y*T*J +
        16192*Y*T*J*E +
        9216*Y*T*J*E^2 +
        2800*Y*T^2 +
        6256*Y*T^2*E +
        3456*Y*T^2*E^2 +
        2800*Y*T^2*J +
        6256*Y*T^2*J*E +
        3456*Y*T^2*J*E^2 +
        320*Y*T^3 +
        704*Y*T^3*E +
        384*Y*T^3*E^2 +
        320*Y*T^3*J +
        704*Y*T^3*J*E +
        384*Y*T^3*J*E^2 +
        4928*Y^2 +
        11072*Y^2*E +
        6144*Y^2*E^2 +
        4928*Y^2*J +
        11072*Y^2*J*E +
        6144*Y^2*J*E^2 +
        8144*Y^2*T +
        17360*Y^2*T*E +
        9216*Y^2*T*E^2 +
        8144*Y^2*T*J +
        17360*Y^2*T*J*E +
        9216*Y^2*T*J*E^2 +
        3136*Y^2*T^2 +
        6592*Y^2*T^2*E +
        3456*Y^2*T^2*E^2 +
        3136*Y^2*T^2*J +
        6592*Y^2*T^2*J*E +
        3456*Y^2*T^2*J*E^2 +
        352*Y^2*T^3 +
        736*Y^2*T^3*E +
        384*Y^2*T^3*E^2 +
        352*Y^2*T^3*J +
        736*Y^2*T^3*J*E +
        384*Y^2*T^3*J*E^2 +
        2048*Y^3 +
        4096*Y^3*E +
        2048*Y^3*E^2 +
        2048*Y^3*J +
        4096*Y^3*J*E +
        2048*Y^3*J*E^2 +
        3072*Y^3*T +
        6144*Y^3*T*E +
        3072*Y^3*T*E^2 +
        3072*Y^3*T*J +
        6144*Y^3*T*J*E +
        3072*Y^3*T*J*E^2 +
        1152*Y^3*T^2 +
        2304*Y^3*T^2*E +
        1152*Y^3*T^2*E^2 +
        1152*Y^3*T^2*J +
        2304*Y^3*T^2*J*E +
        1152*Y^3*T^2*J*E^2 +
        128*Y^3*T^3 +
        256*Y^3*T^3*E +
        128*Y^3*T^3*E^2 +
        128*Y^3*T^3*J +
        256*Y^3*T^3*J*E +
        128*Y^3*T^3*J*E^2 := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_new_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ 2*(t-1)*A-2*s*Mn := by
  dsimp only
  calc
    0 ≤ 9246 +
        15384*E +
        6144*E^2 +
        9240*J +
        15384*J*E +
        6144*J*E^2 +
        5634*T +
        8704*T*E +
        3072*T*E^2 +
        5632*T*J +
        8704*T*J*E +
        3072*T*J*E^2 +
        1088*T^2 +
        1472*T^2*E +
        384*T^2*E^2 +
        1088*T^2*J +
        1472*T^2*J*E +
        384*T^2*J*E^2 +
        64*T^3 +
        64*T^3*E +
        64*T^3*J +
        64*T^3*J*E +
        24280*Y +
        42712*Y*E +
        18432*Y*E^2 +
        24280*Y*J +
        42712*Y*J*E +
        18432*Y*J*E^2 +
        14128*Y*T +
        23344*Y*T*E +
        9216*Y*T*E^2 +
        14128*Y*T*J +
        23344*Y*T*J*E +
        9216*Y*T*J*E^2 +
        2528*Y*T^2 +
        3680*Y*T^2*E +
        1152*Y*T^2*E^2 +
        2528*Y*T^2*J +
        3680*Y*T^2*J*E +
        1152*Y*T^2*J*E^2 +
        128*Y*T^3 +
        128*Y*T^3*E +
        128*Y*T^3*J +
        128*Y*T^3*J*E +
        21184*Y^2 +
        39616*Y^2*E +
        18432*Y^2*E^2 +
        21184*Y^2*J +
        39616*Y^2*J*E +
        18432*Y^2*J*E^2 +
        11568*Y^2*T +
        20784*Y^2*T*E +
        9216*Y^2*T*E^2 +
        11568*Y^2*T*J +
        20784*Y^2*T*J*E +
        9216*Y^2*T*J*E^2 +
        1824*Y^2*T^2 +
        2976*Y^2*T^2*E +
        1152*Y^2*T^2*E^2 +
        1824*Y^2*T^2*J +
        2976*Y^2*T^2*J*E +
        1152*Y^2*T^2*J*E^2 +
        64*Y^2*T^3 +
        64*Y^2*T^3*E +
        64*Y^2*T^3*J +
        64*Y^2*T^3*J*E +
        6144*Y^3 +
        12288*Y^3*E +
        6144*Y^3*E^2 +
        6144*Y^3*J +
        12288*Y^3*J*E +
        6144*Y^3*J*E^2 +
        3072*Y^3*T +
        6144*Y^3*T*E +
        3072*Y^3*T*E^2 +
        3072*Y^3*T*J +
        6144*Y^3*T*J*E +
        3072*Y^3*T*J*E^2 +
        384*Y^3*T^2 +
        768*Y^3*T^2*E +
        384*Y^3*T^2*E^2 +
        384*Y^3*T^2*J +
        768*Y^3*T^2*J*E +
        384*Y^3*T^2*J*E^2 := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_new_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ A-1-(2*(t-1)*A-2*s*Mn) := by
  dsimp only
  calc
    0 ≤ 7714 +
        17960*E +
        10240*E^2 +
        7720*J +
        17960*J*E +
        10240*J*E^2 +
        6926*T +
        16144*T*E +
        9216*T*E^2 +
        6928*T*J +
        16144*T*J*E +
        9216*T*J*E^2 +
        2016*T^2 +
        4704*T^2*E +
        2688*T^2*E^2 +
        2016*T^2*J +
        4704*T^2*J*E +
        2688*T^2*J*E^2 +
        192*T^3 +
        448*T^3*E +
        256*T^3*E^2 +
        192*T^3*J +
        448*T^3*J*E +
        256*T^3*J*E^2 +
        25960*Y +
        56680*Y*E +
        30720*Y*E^2 +
        25960*Y*J +
        56680*Y*J*E +
        30720*Y*J*E^2 +
        23264*Y*T +
        50912*Y*T*E +
        27648*Y*T*E^2 +
        23264*Y*T*J +
        50912*Y*T*J*E +
        27648*Y*T*J*E^2 +
        6752*Y*T^2 +
        14816*Y*T^2*E +
        8064*Y*T^2*E^2 +
        6752*Y*T^2*J +
        14816*Y*T^2*J*E +
        8064*Y*T^2*J*E^2 +
        640*Y*T^3 +
        1408*Y*T^3*E +
        768*Y*T^3*E^2 +
        640*Y*T^3*J +
        1408*Y*T^3*J*E +
        768*Y*T^3*J*E^2 +
        28480*Y^2 +
        59200*Y^2*E +
        30720*Y^2*E^2 +
        28480*Y^2*J +
        59200*Y^2*J*E +
        30720*Y^2*J*E^2 +
        25552*Y^2*T +
        53200*Y^2*T*E +
        27648*Y^2*T*E^2 +
        25552*Y^2*T*J +
        53200*Y^2*T*J*E +
        27648*Y^2*T*J*E^2 +
        7424*Y^2*T^2 +
        15488*Y^2*T^2*E +
        8064*Y^2*T^2*E^2 +
        7424*Y^2*T^2*J +
        15488*Y^2*T^2*J*E +
        8064*Y^2*T^2*J*E^2 +
        704*Y^2*T^3 +
        1472*Y^2*T^3*E +
        768*Y^2*T^3*E^2 +
        704*Y^2*T^3*J +
        1472*Y^2*T^3*J*E +
        768*Y^2*T^3*J*E^2 +
        10240*Y^3 +
        20480*Y^3*E +
        10240*Y^3*E^2 +
        10240*Y^3*J +
        20480*Y^3*J*E +
        10240*Y^3*J*E^2 +
        9216*Y^3*T +
        18432*Y^3*T*E +
        9216*Y^3*T*E^2 +
        9216*Y^3*T*J +
        18432*Y^3*T*J*E +
        9216*Y^3*T*J*E^2 +
        2688*Y^3*T^2 +
        5376*Y^3*T^2*E +
        2688*Y^3*T^2*E^2 +
        2688*Y^3*T^2*J +
        5376*Y^3*T^2*J*E +
        2688*Y^3*T^2*J*E^2 +
        256*Y^3*T^3 +
        512*Y^3*T^3*E +
        256*Y^3*T^3*E^2 +
        256*Y^3*T^3*J +
        512*Y^3*T^3*J*E +
        256*Y^3*T^3*J*E^2 := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_tight_old_bank (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ B-H*M-1 := by
  dsimp only
  calc
    0 ≤ 1019 +
        1024*E +
        1015*J +
        1024*J*E +
        767*T +
        768*T*E +
        766*T*J +
        768*T*J*E +
        192*T^2 +
        192*T^2*E +
        192*T^2*J +
        192*T^2*J*E +
        16*T^3 +
        16*T^3*E +
        16*T^3*J +
        16*T^3*J*E +
        1784*Y +
        1792*Y*E +
        1784*Y*J +
        1792*Y*J*E +
        1406*Y*T +
        1408*Y*T*E +
        1406*Y*T*J +
        1408*Y*T*J*E +
        368*Y*T^2 +
        368*Y*T^2*E +
        368*Y*T^2*J +
        368*Y*T^2*J*E +
        32*Y*T^3 +
        32*Y*T^3*E +
        32*Y*T^3*J +
        32*Y*T^3*J*E +
        768*Y^2 +
        768*Y^2*E +
        768*Y^2*J +
        768*Y^2*J*E +
        640*Y^2*T +
        640*Y^2*T*E +
        640*Y^2*T*J +
        640*Y^2*T*J*E +
        176*Y^2*T^2 +
        176*Y^2*T^2*E +
        176*Y^2*T^2*J +
        176*Y^2*T^2*J*E +
        16*Y^2*T^3 +
        16*Y^2*T^3*E +
        16*Y^2*T^3*J +
        16*Y^2*T^3*J*E := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_tight_r_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ H*Mn-B := by
  dsimp only
  calc
    0 ≤ 4 +
        9*J +
        1*T +
        2*T*J +
        264*Y +
        256*Y*E +
        264*Y*J +
        256*Y*J*E +
        130*Y*T +
        128*Y*T*E +
        130*Y*T*J +
        128*Y*T*J*E +
        16*Y*T^2 +
        16*Y*T^2*E +
        16*Y*T^2*J +
        16*Y*T^2*J*E +
        256*Y^2 +
        256*Y^2*E +
        256*Y^2*J +
        256*Y^2*J*E +
        128*Y^2*T +
        128*Y^2*T*E +
        128*Y^2*T*J +
        128*Y^2*T*J*E +
        16*Y^2*T^2 +
        16*Y^2*T^2*E +
        16*Y^2*T^2*J +
        16*Y^2*T^2*J*E := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_bit_divisor_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ g-H := by
  dsimp only
  calc
    0 ≤ 3 +
        4*E +
        3*J +
        4*J*E +
        4*Y +
        4*Y*E +
        4*Y*J +
        4*Y*J*E := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_third_gate_width (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ L-2*B-H*D := by
  dsimp only
  calc
    0 ≤ 3470 +
        11680*E +
        8192*E^2 +
        3319*J +
        11520*J*E +
        8192*J*E^2 +
        2756*T +
        8904*T*E +
        6144*T*E^2 +
        2686*T*J +
        8832*T*J*E +
        6144*T*J*E^2 +
        728*T^2 +
        2264*T^2*E +
        1536*T^2*E^2 +
        720*T^2*J +
        2256*T^2*J*E +
        1536*T^2*J*E^2 +
        64*T^3 +
        192*T^3*E +
        128*T^3*E^2 +
        64*T^3*J +
        192*T^3*J*E +
        128*T^3*J*E^2 +
        7320*Y +
        23712*Y*E +
        16384*Y*E^2 +
        7160*Y*J +
        23552*Y*J*E +
        16384*Y*J*E^2 +
        5702*Y*T +
        17992*Y*T*E +
        12288*Y*T*E^2 +
        5630*Y*T*J +
        17920*Y*T*J*E +
        12288*Y*T*J*E^2 +
        1480*Y*T^2 +
        4552*Y*T^2*E +
        3072*Y*T^2*E^2 +
        1472*Y*T^2*J +
        4544*Y*T^2*J*E +
        3072*Y*T^2*J*E^2 +
        128*Y*T^3 +
        384*Y*T^3*E +
        256*Y*T^3*E^2 +
        128*Y*T^3*J +
        384*Y*T^3*J*E +
        256*Y*T^3*J*E^2 +
        3840*Y^2 +
        12032*Y^2*E +
        8192*Y^2*E^2 +
        3840*Y^2*J +
        12032*Y^2*J*E +
        8192*Y^2*J*E^2 +
        2944*Y^2*T +
        9088*Y^2*T*E +
        6144*Y^2*T*E^2 +
        2944*Y^2*T*J +
        9088*Y^2*T*J*E +
        6144*Y^2*T*J*E^2 +
        752*Y^2*T^2 +
        2288*Y^2*T^2*E +
        1536*Y^2*T^2*E^2 +
        752*Y^2*T^2*J +
        2288*Y^2*T^2*J*E +
        1536*Y^2*T^2*J*E^2 +
        64*Y^2*T^3 +
        192*Y^2*T^3*E +
        128*Y^2*T^3*E^2 +
        64*Y^2*T^3*J +
        192*Y^2*T^3*J*E +
        128*Y^2*T^3*J*E^2 := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem separated_w_capacity_strict (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ z*B-2*L-1 := by
  dsimp only
  calc
    0 ≤ 57181 +
        114528*E +
        57344*E^2 +
        57344*J +
        114688*J*E +
        57344*J*E^2 +
        59320*T +
        118712*T*E +
        59392*T*E^2 +
        59392*T*J +
        118784*T*J*E +
        59392*T*J*E^2 +
        23032*T^2 +
        46072*T^2*E +
        23040*T^2*E^2 +
        23040*T^2*J +
        46080*T^2*J*E +
        23040*T^2*J*E^2 +
        3968*T^3 +
        7936*T^3*E +
        3968*T^3*E^2 +
        3968*T^3*J +
        7936*T^3*J*E +
        3968*T^3*J*E^2 +
        256*T^4 +
        512*T^4*E +
        256*T^4*E^2 +
        256*T^4*J +
        512*T^4*J*E +
        256*T^4*J*E^2 +
        180064*Y +
        360288*Y*E +
        180224*Y*E^2 +
        180224*Y*J +
        360448*Y*J*E +
        180224*Y*J*E^2 +
        184248*Y*T +
        368568*Y*T*E +
        184320*Y*T*E^2 +
        184320*Y*T*J +
        368640*Y*T*J*E +
        184320*Y*T*J*E^2 +
        70648*Y*T^2 +
        141304*Y*T^2*E +
        70656*Y*T^2*E^2 +
        70656*Y*T^2*J +
        141312*Y*T^2*J*E +
        70656*Y*T^2*J*E^2 +
        12032*Y*T^3 +
        24064*Y*T^3*E +
        12032*Y*T^3*E^2 +
        12032*Y*T^3*J +
        24064*Y*T^3*J*E +
        12032*Y*T^3*J*E^2 +
        768*Y*T^4 +
        1536*Y*T^4*E +
        768*Y*T^4*E^2 +
        768*Y*T^4*J +
        1536*Y*T^4*J*E +
        768*Y*T^4*J*E^2 +
        188416*Y^2 +
        376832*Y^2*E +
        188416*Y^2*E^2 +
        188416*Y^2*J +
        376832*Y^2*J*E +
        188416*Y^2*J*E^2 +
        190464*Y^2*T +
        380928*Y^2*T*E +
        190464*Y^2*T*E^2 +
        190464*Y^2*T*J +
        380928*Y^2*T*J*E +
        190464*Y^2*T*J*E^2 +
        72192*Y^2*T^2 +
        144384*Y^2*T^2*E +
        72192*Y^2*T^2*E^2 +
        72192*Y^2*T^2*J +
        144384*Y^2*T^2*J*E +
        72192*Y^2*T^2*J*E^2 +
        12160*Y^2*T^3 +
        24320*Y^2*T^3*E +
        12160*Y^2*T^3*E^2 +
        12160*Y^2*T^3*J +
        24320*Y^2*T^3*J*E +
        12160*Y^2*T^3*J*E^2 +
        768*Y^2*T^4 +
        1536*Y^2*T^4*E +
        768*Y^2*T^4*E^2 +
        768*Y^2*T^4*J +
        1536*Y^2*T^4*J*E +
        768*Y^2*T^4*J*E^2 +
        65536*Y^3 +
        131072*Y^3*E +
        65536*Y^3*E^2 +
        65536*Y^3*J +
        131072*Y^3*J*E +
        65536*Y^3*J*E^2 +
        65536*Y^3*T +
        131072*Y^3*T*E +
        65536*Y^3*T*E^2 +
        65536*Y^3*T*J +
        131072*Y^3*T*J*E +
        65536*Y^3*T*J*E^2 +
        24576*Y^3*T^2 +
        49152*Y^3*T^2*E +
        24576*Y^3*T^2*E^2 +
        24576*Y^3*T^2*J +
        49152*Y^3*T^2*J*E +
        24576*Y^3*T^2*J*E^2 +
        4096*Y^3*T^3 +
        8192*Y^3*T^3*E +
        4096*Y^3*T^3*E^2 +
        4096*Y^3*T^3*J +
        8192*Y^3*T^3*J*E +
        4096*Y^3*T^3*J*E^2 +
        256*Y^3*T^4 +
        512*Y^3*T^4*E +
        256*Y^3*T^4*E^2 +
        256*Y^3*T^4*J +
        512*Y^3*T^4*J*E +
        256*Y^3*T^4*J*E^2 := by positivity
    _ = _ := by ring

private theorem chart_separated (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 4*y*(1+E)
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+E)*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  UniformBounds x y z t H g s := by
  dsimp only
  apply uniformBounds_mk
  · exact separated_old_first_lower Y T J E hY hT hJ hE
  · exact separated_old_first_peak Y T J E hY hT hJ hE
  · exact separated_new_first_lower Y T J E hY hT hJ hE
  · exact separated_new_first_peak Y T J E hY hT hJ hE
  · exact separated_tight_old_bank Y T J E hY hT hJ hE
  · exact separated_tight_r_capacity Y T J E hY hT hJ hE
  · exact separated_bit_divisor_capacity Y T J E hY hT hJ hE
  · right
    refine ⟨?_, separated_third_gate_width Y T J E hY hT hJ hE,
      separated_w_capacity_strict Y T J E hY hT hJ hE⟩
    have hy : 0 ≤ 2*(4+T)*(1+Y) := by positivity
    nlinarith only [mul_nonneg hy hE]

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
