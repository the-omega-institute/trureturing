/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/Polynomials
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: UniformBounds and the 18 tight-quotient identities for adjacent charts C1/C2. -/
/- SOURCE_ONLY_UNCOMPILED. Caller construction, tight bound and ordinary proof.
No Pro validation, kernel validation, report or official acceptance is claimed.
Pinned source API: 1add3bcde3f5768e7c5b7c84867d9758df1e6e6b.
All coefficient vectors come from the supplied tight-certificate.json.
Variable order there is Y,T,J,E (its generator called J H).
No loose B*t*y*z-M*Mn inequality is used. -/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond

private structure UniformBounds (x y z t H g s : ℤ) : Prop where
  oldLower : 0 ≤ t*(x*(y*z+y+1)+1)-2*s*(t*y*z+(y*z+y+1))
  oldUpper : 0 ≤ (x*(y*z+y+1)+1)-1-
    (t*(x*(y*z+y+1)+1)-2*s*(t*y*z+(y*z+y+1)))
  newLower : 0 ≤ 2*(t-1)*(x*(y*z+y+1)+1)-2*s*(2*(t*y*z+(y*z+y+1))-(y*z+y+1))
  newUpper : 0 ≤ (x*(y*z+y+1)+1)-1-
    (2*(t-1)*(x*(y*z+y+1)+1)-2*s*(2*(t*y*z+(y*z+y+1))-(y*z+y+1)))
  tightOld : 0 ≤ (x*t*(y+1)+t+1)-H*(t*y*z+(y*z+y+1))-1
  tightCeil : 0 ≤ H*(2*(t*y*z+(y*z+y+1))-(y*z+y+1))-(x*t*(y+1)+t+1)
  grainCapacity : 0 ≤ g-H
  third : (z=2*y ∧ 0 ≤ (x*z*t+z*t+z+1)-(x*t*(y+1)+t+1)-H*(t*y*z+(y*z+y+1)) ∧
    0 ≤ 2*(x*t*(y+1)+t+1)-(x*z*t+z*t+z+1)-1) ∨
    (4*y≤z ∧ 0 ≤ (x*z*t+z*t+z+1)-2*(x*t*(y+1)+t+1)-H*(y*z+y+1) ∧
    0 ≤ z*(x*t*(y+1)+t+1)-2*(x*z*t+z*t+z+1)-1)

private theorem uniformBounds_mk (x y z t H g s : ℤ)
    (oldLower : 0 ≤ t*(x*(y*z+y+1)+1)-2*s*(t*y*z+(y*z+y+1)))
    (oldUpper : 0 ≤ (x*(y*z+y+1)+1)-1-
      (t*(x*(y*z+y+1)+1)-2*s*(t*y*z+(y*z+y+1))))
    (newLower : 0 ≤ 2*(t-1)*(x*(y*z+y+1)+1)-2*s*(2*(t*y*z+(y*z+y+1))-(y*z+y+1)))
    (newUpper : 0 ≤ (x*(y*z+y+1)+1)-1-
      (2*(t-1)*(x*(y*z+y+1)+1)-2*s*(2*(t*y*z+(y*z+y+1))-(y*z+y+1))))
    (tightOld : 0 ≤ (x*t*(y+1)+t+1)-H*(t*y*z+(y*z+y+1))-1)
    (tightCeil : 0 ≤ H*(2*(t*y*z+(y*z+y+1))-(y*z+y+1))-(x*t*(y+1)+t+1))
    (grainCapacity : 0 ≤ g-H)
    (third : (z=2*y ∧ 0 ≤ (x*z*t+z*t+z+1)-(x*t*(y+1)+t+1)-H*(t*y*z+(y*z+y+1)) ∧
      0 ≤ 2*(x*t*(y+1)+t+1)-(x*z*t+z*t+z+1)-1) ∨
      (4*y≤z ∧ 0 ≤ (x*z*t+z*t+z+1)-2*(x*t*(y+1)+t+1)-H*(y*z+y+1) ∧
      0 ≤ z*(x*t*(y+1)+t+1)-2*(x*z*t+z*t+z+1)-1)) :
    UniformBounds x y z t H g s :=
  ⟨oldLower, oldUpper, newLower, newUpper, tightOld, tightCeil, grainCapacity, third⟩


set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_old_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 30356 +
        30348*J +
        10641*T +
        10640*T*J +
        1240*T^2 +
        1240*T^2*J +
        48*T^3 +
        48*T^3*J +
        82764*Y +
        82764*Y*J +
        28840*Y*T +
        28840*Y*T*J +
        3336*Y*T^2 +
        3336*Y*T^2*J +
        128*Y*T^3 +
        128*Y*T^3*J +
        74944*Y^2 +
        74944*Y^2*J +
        25880*Y^2*T +
        25880*Y^2*T*J +
        2960*Y^2*T^2 +
        2960*Y^2*T^2*J +
        112*Y^2*T^3 +
        112*Y^2*T^3*J +
        22528*Y^3 +
        22528*Y^3*J +
        7680*Y^3*T +
        7680*Y^3*T*J +
        864*Y^3*T^2 +
        864*Y^3*T^2*J +
        32*Y^3*T^3 +
        32*Y^3*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_old_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 3500 +
        3508*J +
        1911*T +
        1912*T*J +
        312*T^2 +
        312*T^2*J +
        16*T^3 +
        16*T^3*J +
        17652*Y +
        17652*Y*J +
        8544*Y*T +
        8544*Y*T*J +
        1304*Y*T^2 +
        1304*Y*T^2*J +
        64*Y*T^3 +
        64*Y*T^3*J +
        24384*Y^2 +
        24384*Y^2*J +
        11240*Y^2*T +
        11240*Y^2*T*J +
        1664*Y^2*T^2 +
        1664*Y^2*T^2*J +
        80*Y^2*T^3 +
        80*Y^2*T^3*J +
        10240*Y^3 +
        10240*Y^3*J +
        4608*Y^3*T +
        4608*Y^3*T*J +
        672*Y^3*T^2 +
        672*Y^3*T^2*J +
        32*Y^3*T^3 +
        32*Y^3*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_new_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 20506 +
        20492*J +
        7170*T +
        7168*T*J +
        832*T^2 +
        832*T^2*J +
        32*T^3 +
        32*T^3*J +
        46284*Y +
        46284*Y*J +
        15640*Y*T +
        15640*Y*T*J +
        1744*Y*T^2 +
        1744*Y*T^2*J +
        64*Y*T^3 +
        64*Y*T^3*J +
        31936*Y^2 +
        31936*Y^2*J +
        10008*Y^2*T +
        10008*Y^2*T*J +
        1008*Y^2*T^2 +
        1008*Y^2*T^2*J +
        32*Y^2*T^3 +
        32*Y^2*T^3*J +
        6144*Y^3 +
        6144*Y^3*J +
        1536*Y^3*T +
        1536*Y^3*T*J +
        96*Y^3*T^2 +
        96*Y^3*T^2*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_new_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 13350 +
        13364*J +
        5382*T +
        5384*T*J +
        720*T^2 +
        720*T^2*J +
        32*T^3 +
        32*T^3*J +
        54132*Y +
        54132*Y*J +
        21744*Y*T +
        21744*Y*T*J +
        2896*Y*T^2 +
        2896*Y*T^2*J +
        128*Y*T^3 +
        128*Y*T^3*J +
        67392*Y^2 +
        67392*Y^2*J +
        27112*Y^2*T +
        27112*Y^2*T*J +
        3616*Y^2*T^2 +
        3616*Y^2*T^2*J +
        160*Y^2*T^3 +
        160*Y^2*T^3*J +
        26624*Y^3 +
        26624*Y^3*J +
        10752*Y^3*T +
        10752*Y^3*T*J +
        1440*Y^3*T^2 +
        1440*Y^3*T^2*J +
        64*Y^3*T^3 +
        64*Y^3*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_tight_old_bank (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 4087 +
        4079*J +
        1535*T +
        1534*T*J +
        192*T^2 +
        192*T^2*J +
        8*T^3 +
        8*T^3*J +
        7664*Y +
        7664*Y*J +
        2942*Y*T +
        2942*Y*T*J +
        376*Y*T^2 +
        376*Y*T^2*J +
        16*Y*T^3 +
        16*Y*T^3*J +
        3584*Y^2 +
        3584*Y^2*J +
        1408*Y^2*T +
        1408*Y^2*T*J +
        184*Y^2*T^2 +
        184*Y^2*T^2*J +
        8*Y^2*T^3 +
        8*Y^2*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_tight_r_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 8 +
        17*J +
        1*T +
        2*T*J +
        528*Y +
        528*Y*J +
        130*Y*T +
        130*Y*T*J +
        8*Y*T^2 +
        8*Y*T^2*J +
        512*Y^2 +
        512*Y^2*J +
        128*Y^2*T +
        128*Y^2*T*J +
        8*Y^2*T^2 +
        8*Y^2*T^2*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_bit_divisor_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
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
    0 ≤ 1 +
        1*J +
        2*Y +
        2*Y*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_third_tight_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ L-B-H*M := by
  dsimp only
  calc
    0 ≤ 3335 +
        3055*J +
        1345*T +
        1278*T*J +
        180*T^2 +
        176*T^2*J +
        8*T^3 +
        8*T^3*J +
        6928*Y +
        6640*Y*J +
        2754*Y*T +
        2686*Y*T*J +
        364*Y*T^2 +
        360*Y*T^2*J +
        16*Y*T^3 +
        16*Y*T^3*J +
        3584*Y^2 +
        3584*Y^2*J +
        1408*Y^2*T +
        1408*Y^2*T*J +
        184*Y^2*T^2 +
        184*Y^2*T^2*J +
        8*Y^2*T^3 +
        8*Y^2*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_t8_third_upper (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ 2*B-L-1 := by
  dsimp only
  calc
    0 ≤ 752 +
        1024*J +
        190*T +
        256*T*J +
        12*T^2 +
        16*T^2*J +
        736*Y +
        1024*Y*J +
        188*Y*T +
        256*Y*T*J +
        12*Y*T^2 +
        16*Y*T^2*J := by positivity
    _ = _ := by ring

private theorem chart_adjacent_t8 (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 8+T
  let y : ℤ := 2*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 2*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  UniformBounds x y z t H g s := by
  dsimp only
  refine ⟨adjacent_t8_old_first_lower Y T J E hY hT hJ hE,
    adjacent_t8_old_first_peak Y T J E hY hT hJ hE,
    adjacent_t8_new_first_lower Y T J E hY hT hJ hE,
    adjacent_t8_new_first_peak Y T J E hY hT hJ hE,
    adjacent_t8_tight_old_bank Y T J E hY hT hJ hE,
    adjacent_t8_tight_r_capacity Y T J E hY hT hJ hE,
    adjacent_t8_bit_divisor_capacity Y T J E hY hT hJ hE, ?_⟩
  left
  exact ⟨by ring, adjacent_t8_third_tight_lower Y T J E hY hT hJ hE,
    adjacent_t8_third_upper Y T J E hY hT hJ hE⟩

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_old_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
    0 ≤ 32348 +
        32344*J +
        21201*T +
        21200*T*J +
        4560*T^2 +
        4560*T^2*J +
        320*T^3 +
        320*T^3*J +
        93144*Y +
        93144*Y*J +
        60720*Y*T +
        60720*Y*T*J +
        12944*Y*T^2 +
        12944*Y*T^2*J +
        896*Y*T^3 +
        896*Y*T^3*J +
        89472*Y^2 +
        89472*Y^2*J +
        57952*Y^2*T +
        57952*Y^2*T*J +
        12224*Y^2*T^2 +
        12224*Y^2*T^2*J +
        832*Y^2*T^3 +
        832*Y^2*T^3*J +
        28672*Y^3 +
        28672*Y^3*J +
        18432*Y^3*T +
        18432*Y^3*T*J +
        3840*Y^3*T^2 +
        3840*Y^3*T^2*J +
        256*Y^3*T^3 +
        256*Y^3*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_old_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
    0 ≤ 1508 +
        1512*J +
        3903*T +
        3904*T*J +
        1648*T^2 +
        1648*T^2*J +
        192*T^3 +
        192*T^3*J +
        7272*Y +
        7272*Y*J +
        14048*Y*T +
        14048*Y*T*J +
        5616*Y*T^2 +
        5616*Y*T^2*J +
        640*Y*T^3 +
        640*Y*T^3*J +
        9856*Y^2 +
        9856*Y^2*J +
        16288*Y^2*T +
        16288*Y^2*T*J +
        6272*Y^2*T^2 +
        6272*Y^2*T^2*J +
        704*Y^2*T^3 +
        704*Y^2*T^3*J +
        4096*Y^3 +
        4096*Y^3*J +
        6144*Y^3*T +
        6144*Y^3*T*J +
        2304*Y^3*T^2 +
        2304*Y^3*T^2*J +
        256*Y^3*T^3 +
        256*Y^3*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_new_first_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
    0 ≤ 18142 +
        18136*J +
        11058*T +
        11056*T*J +
        2144*T^2 +
        2144*T^2*J +
        128*T^3 +
        128*T^3*J +
        48216*Y +
        48216*Y*J +
        28048*Y*T +
        28048*Y*T*J +
        5024*Y*T^2 +
        5024*Y*T^2*J +
        256*Y*T^3 +
        256*Y*T^3*J +
        42368*Y^2 +
        42368*Y^2*J +
        23136*Y^2*T +
        23136*Y^2*T*J +
        3648*Y^2*T^2 +
        3648*Y^2*T^2*J +
        128*Y^2*T^3 +
        128*Y^2*T^3*J +
        12288*Y^3 +
        12288*Y^3*J +
        6144*Y^3*T +
        6144*Y^3*T*J +
        768*Y^3*T^2 +
        768*Y^3*T^2*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_new_first_peak (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
    0 ≤ 15714 +
        15720*J +
        14046*T +
        14048*T*J +
        4064*T^2 +
        4064*T^2*J +
        384*T^3 +
        384*T^3*J +
        52200*Y +
        52200*Y*J +
        46720*Y*T +
        46720*Y*T*J +
        13536*Y*T^2 +
        13536*Y*T^2*J +
        1280*Y*T^3 +
        1280*Y*T^3*J +
        56960*Y^2 +
        56960*Y^2*J +
        51104*Y^2*T +
        51104*Y^2*T*J +
        14848*Y^2*T^2 +
        14848*Y^2*T^2*J +
        1408*Y^2*T^3 +
        1408*Y^2*T^3*J +
        20480*Y^3 +
        20480*Y^3*J +
        18432*Y^3*T +
        18432*Y^3*T*J +
        5376*Y^3*T^2 +
        5376*Y^3*T^2*J +
        512*Y^3*T^3 +
        512*Y^3*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_tight_old_bank (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
    0 ≤ 1779 +
        1775*J +
        1405*T +
        1404*T*J +
        368*T^2 +
        368*T^2*J +
        32*T^3 +
        32*T^3*J +
        3312*Y +
        3312*Y*J +
        2684*Y*T +
        2684*Y*T*J +
        720*Y*T^2 +
        720*Y*T^2*J +
        64*Y*T^3 +
        64*Y*T^3*J +
        1536*Y^2 +
        1536*Y^2*J +
        1280*Y^2*T +
        1280*Y^2*T*J +
        352*Y^2*T^2 +
        352*Y^2*T^2*J +
        32*Y^2*T^3 +
        32*Y^2*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_tight_r_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
    0 ≤ 268 +
        273*J +
        131*T +
        132*T*J +
        16*T^2 +
        16*T^2*J +
        784*Y +
        784*Y*J +
        388*Y*T +
        388*Y*T*J +
        48*Y*T^2 +
        48*Y*T^2*J +
        512*Y^2 +
        512*Y^2*J +
        256*Y^2*T +
        256*Y^2*T*J +
        32*Y^2*T^2 +
        32*Y^2*T^2*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_bit_divisor_capacity (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
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
        3*J +
        4*Y +
        4*Y*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_third_tight_lower (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ L-B-H*M := by
  dsimp only
  calc
    0 ≤ 1419 +
        1263*J +
        1219*T +
        1148*T*J +
        344*T^2 +
        336*T^2*J +
        32*T^3 +
        32*T^3*J +
        2960*Y +
        2800*Y*J +
        2500*Y*T +
        2428*Y*T*J +
        696*Y*T^2 +
        688*Y*T^2*J +
        64*Y*T^3 +
        64*Y*T^3*J +
        1536*Y^2 +
        1536*Y^2*J +
        1280*Y^2*T +
        1280*Y^2*T*J +
        352*Y^2*T^2 +
        352*Y^2*T^2*J +
        32*Y^2*T^3 +
        32*Y^2*T^3*J := by positivity
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
private theorem adjacent_y4_third_upper (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  0 ≤ 2*B-L-1 := by
  dsimp only
  calc
    0 ≤ 360 +
        512*J +
        186*T +
        256*T*J +
        24*T^2 +
        32*T^2*J +
        352*Y +
        512*Y*J +
        184*Y*T +
        256*Y*T*J +
        24*Y*T^2 +
        32*Y*T^2*J := by positivity
    _ = _ := by ring

private theorem chart_adjacent_y4 (Y T J E : ℤ)
    (hY : 0≤Y) (hT : 0≤T) (hJ : 0≤J) (hE : 0≤E) :
  let t : ℤ := 4+T
  let y : ℤ := 4*t*(1+Y)
  let z : ℤ := 2*y
  let x : ℤ := 2*z*(1+J)
  let H : ℤ := 1+J
  let g : ℤ := 4*(1+Y)*(1+J)
  let s : ℤ := g*(2*t-3)
  let D : ℤ := y*z+y+1
  let A : ℤ := x*D+1
  let B : ℤ := x*t*(y+1)+t+1
  let L : ℤ := x*z*t+z*t+z+1
  let M : ℤ := t*y*z+D
  let Mn : ℤ := 2*M-D
  UniformBounds x y z t H g s := by
  dsimp only
  refine ⟨adjacent_y4_old_first_lower Y T J E hY hT hJ hE,
    adjacent_y4_old_first_peak Y T J E hY hT hJ hE,
    adjacent_y4_new_first_lower Y T J E hY hT hJ hE,
    adjacent_y4_new_first_peak Y T J E hY hT hJ hE,
    adjacent_y4_tight_old_bank Y T J E hY hT hJ hE,
    adjacent_y4_tight_r_capacity Y T J E hY hT hJ hE,
    adjacent_y4_bit_divisor_capacity Y T J E hY hT hJ hE, ?_⟩
  left
  exact ⟨by ring, adjacent_y4_third_tight_lower Y T J E hY hT hJ hE,
    adjacent_y4_third_upper Y T J E hY hT hJ hE⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
