/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C3Gates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C3Gates
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Source]
   utility: none
   digest: Universal doubled gates for the c3 fixed and parity-tail bank charts. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C3Arithmetic
import Mathlib.Tactic

/-! Universal doubled gates for the c3 fixed and parity-tail bank charts. Original source owners supply the reused proofs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open scoped BigOperators

/- Coefficients/identities: uxwv-c3-a5-full-tail-20261102.py, universal_case. -/
private def c3DoubledGates (h t : ℤ) (M : Fin 4 → Fin 4 → ℤ) : Prop :=
  let x : ℤ := 32
  let z : ℤ := 8
  let w := 32*h
  let y := 64*h*t
  let A := 1+x+x*y+x*y*z
  let B := 1+w+w*x+w*x*y
  let L := 1+z+w*z+w*z*x
  let K := 1+y+y*z+y*w*z
  let N := x*y*z*w-1
  let Q := 2*N+1
  let old : Fin 4 → ℤ := ![A,B,L,K]
  let new : Fin 4 → ℤ := ![2*A,2*B-1,2*L-z-1,2*K-y*(z+1)-1]
  let m := fun i => ∑ j : Fin 4, M i j * old j
  let n := fun i => ∑ j : Fin 4, M i j * new j
  let H : Fin 5 → ℤ := ![0,
    2*m 0+B-N,
    2*(m 0+m 1)+B+A-2*N,
    2*(m 0+m 1+m 2)+B+A+K-3*N,
    2*(m 0+m 1+m 2+m 3)+B+A+K+L-4*N]
  let G : Fin 5 → ℤ := ![2*A,
    2*A+2*n 0+(2*B-1)-Q,
    2*A+2*(n 0+n 1)+(2*B-1)+A-2*Q,
    2*A+2*(n 0+n 1+n 2)+(2*B-1)+A+(2*K-y*(z+1)-1)-3*Q,
    2*A+2*(n 0+n 1+n 2+n 3)+(2*B-1)+A+
      (2*K-y*(z+1)-1)+(2*L-z-1)-4*Q]
  H 4 = 0 ∧ G 4 = 0 ∧
    (∀ i : Fin 4, 0 ≤ H i.succ) ∧
    (∀ i : Fin 4, G i.castSucc+2*n i ≤ 2*N)

private theorem c3_fixed2 (t : ℤ)
    (ht : 1 ≤ t) :
    c3DoubledGates 4 t
      ![![10, 0, (100 * t), 0], ![0, 0, (16 * t), 12], ![53, 0, (8 * t), 0], ![0, 3, ((-1) + (4 * t)), 3]] := by
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((4886 + (894728 * t)) : ℤ) := by
    calc
      0 ≤ (899614 + (894728 * (t-1))) := by positivity
      _ = (4886 + (894728 * t)) := by ring
  have g1 : 0 ≤ ((4944 + (8232 * t)) : ℤ) := by
    calc
      0 ≤ (13176 + (8232 * (t-1))) := by positivity
      _ = (4944 + (8232 * t)) := by ring
  have g2 : 0 ≤ ((8444 + (240056 * t)) : ℤ) := by
    calc
      0 ≤ (248500 + (240056 * (t-1))) := by positivity
      _ = (8444 + (240056 * t)) := by ring
  have g3 : 0 ≤ (((-1388) + (162040 * t)) : ℤ) := by
    calc
      0 ≤ (160652 + (162040 * (t-1))) := by positivity
      _ = ((-1388) + (162040 * t)) := by ring
  have g4 : 0 ≤ (((-9862) + (40920 * t)) : ℤ) := by
    calc
      0 ≤ (31058 + (40920 * (t-1))) := by positivity
      _ = ((-9862) + (40920 * t)) := by ring
  have g5 : 0 ≤ (((-16892) + (32584 * t)) : ℤ) := by
    calc
      0 ≤ (15692 + (32584 * (t-1))) := by positivity
      _ = ((-16892) + (32584 * t)) := by ring
  have g6 : 0 ≤ (67592 : ℤ) := by norm_num
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_fixed3 (t : ℤ)
    (ht : 1 ≤ t) :
    c3DoubledGates 8 t
      ![![14, 0, (208 * t), 0], ![0, 0, (39 * t), 12], ![113, 0, 0, 0], ![0, 3, ((-1) + (9 * t)), 3]] := by
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((9374 + (2887328 * t)) : ℤ) := by
    calc
      0 ≤ (2896702 + (2887328 * (t-1))) := by positivity
      _ = (9374 + (2887328 * t)) := by ring
  have g1 : 0 ≤ ((9432 + (29022 * t)) : ℤ) := by
    calc
      0 ≤ (38454 + (29022 * (t-1))) := by positivity
      _ = (9432 + (29022 * t)) := by ring
  have g2 : 0 ≤ ((16892 + (852830 * t)) : ℤ) := by
    calc
      0 ≤ (869722 + (852830 * (t-1))) := by positivity
      _ = (16892 + (852830 * t)) := by ring
  have g3 : 0 ≤ (((-1916) + (2322784 * t)) : ℤ) := by
    calc
      0 ≤ (2320868 + (2322784 * (t-1))) := by positivity
      _ = ((-1916) + (2322784 * t)) := by ring
  have g4 : 0 ≤ (((-18838) + (56994 * t)) : ℤ) := by
    calc
      0 ≤ (38156 + (56994 * (t-1))) := by positivity
      _ = ((-18838) + (56994 * t)) := by ring
  have g5 : 0 ≤ (((-33788) + (368290 * t)) : ℤ) := by
    calc
      0 ≤ (334502 + (368290 * (t-1))) := by positivity
      _ = ((-33788) + (368290 * t)) := by ring
  have g6 : 0 ≤ (135176 : ℤ) := by norm_num
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_fixed4 (t : ℤ)
    (ht : 1 ≤ t) :
    c3DoubledGates 16 t
      ![![32, 0, (416 * t), 0], ![0, 0, (71 * t), 12], ![223, 0, 0, 0], ![0, 3, ((-1) + (25 * t)), 3]] := by
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((19010 + (13901120 * t)) : ℤ) := by
    calc
      0 ≤ (13920130 + (13901120 * (t-1))) := by positivity
      _ = (19010 + (13901120 * t)) := by ring
  have g1 : 0 ≤ ((19068 + (57918 * t)) : ℤ) := by
    calc
      0 ≤ (76986 + (57918 * (t-1))) := by positivity
      _ = (19068 + (57918 * t)) := by ring
  have g2 : 0 ≤ ((33788 + (1574462 * t)) : ℤ) := by
    calc
      0 ≤ (1608250 + (1574462 * (t-1))) := by positivity
      _ = (33788 + (1574462 * t)) := by ring
  have g3 : 0 ≤ (((-4292) + (5169856 * t)) : ℤ) := by
    calc
      0 ≤ (5165564 + (5169856 * (t-1))) := by positivity
      _ = ((-4292) + (5169856 * t)) := by ring
  have g4 : 0 ≤ (((-38110) + (114114 * t)) : ℤ) := by
    calc
      0 ≤ (76004 + (114114 * (t-1))) := by positivity
      _ = ((-38110) + (114114 * t)) := by ring
  have g5 : 0 ≤ (((-67580) + (5193154 * t)) : ℤ) := by
    calc
      0 ≤ (5125574 + (5193154 * (t-1))) := by positivity
      _ = ((-67580) + (5193154 * t)) := by ring
  have g6 : 0 ≤ (270344 : ℤ) := by norm_num
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_fixed5 (t : ℤ)
    (ht : 1 ≤ t) :
    c3DoubledGates 32 t
      ![![68, 0, (832 * t), 0], ![0, 0, (135 * t), 12], ![443, 0, 0, 0], ![0, 3, ((-1) + (57 * t)), 3]] := by
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((38282 + (60308096 * t)) : ℤ) := by
    calc
      0 ≤ (60346378 + (60308096 * (t-1))) := by positivity
      _ = (38282 + (60308096 * t)) := by ring
  have g1 : 0 ≤ ((38340 + (115710 * t)) : ℤ) := by
    calc
      0 ≤ (154050 + (115710 * (t-1))) := by positivity
      _ = (38340 + (115710 * t)) := by ring
  have g2 : 0 ≤ ((67580 + (2624510 * t)) : ℤ) := by
    calc
      0 ≤ (2692090 + (2624510 * (t-1))) := by positivity
      _ = (67580 + (2624510 * t)) := by ring
  have g3 : 0 ≤ (((-9044) + (12436864 * t)) : ℤ) := by
    calc
      0 ≤ (12427820 + (12436864 * (t-1))) := by positivity
      _ = ((-9044) + (12436864 * t)) := by ring
  have g4 : 0 ≤ (((-76654) + (228354 * t)) : ℤ) := by
    calc
      0 ≤ (151700 + (228354 * (t-1))) := by positivity
      _ = ((-76654) + (228354 * t)) := by ring
  have g5 : 0 ≤ (((-135164) + (28212226 * t)) : ℤ) := by
    calc
      0 ≤ (28077062 + (28212226 * (t-1))) := by positivity
      _ = ((-135164) + (28212226 * t)) := by ring
  have g6 : 0 ≤ (540680 : ℤ) := by norm_num
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_fixed6 (t : ℤ)
    (ht : 1 ≤ t) :
    c3DoubledGates 64 t
      ![![140, 0, (1664 * t), 0], ![0, 0, (263 * t), 12], ![883, 0, 0, 0], ![0, 3, ((-1) + (121 * t)), 3]] := by
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((76826 + (250639616 * t)) : ℤ) := by
    calc
      0 ≤ (250716442 + (250639616 * (t-1))) := by positivity
      _ = (76826 + (250639616 * t)) := by ring
  have g1 : 0 ≤ ((76884 + (231294 * t)) : ℤ) := by
    calc
      0 ≤ (308178 + (231294 * (t-1))) := by positivity
      _ = (76884 + (231294 * t)) := by ring
  have g2 : 0 ≤ ((135164 + (3151742 * t)) : ℤ) := by
    calc
      0 ≤ (3286906 + (3151742 * (t-1))) := by positivity
      _ = (135164 + (3151742 * t)) := by ring
  have g3 : 0 ≤ (((-18548) + (33262336 * t)) : ℤ) := by
    calc
      0 ≤ (33243788 + (33262336 * (t-1))) := by positivity
      _ = ((-18548) + (33262336 * t)) := by ring
  have g4 : 0 ≤ (((-153742) + (456834 * t)) : ℤ) := by
    calc
      0 ≤ (303092 + (456834 * (t-1))) := by positivity
      _ = ((-153742) + (456834 * t)) := by ring
  have g5 : 0 ≤ (((-270332) + (127727746 * t)) : ℤ) := by
    calc
      0 ≤ (127457414 + (127727746 * (t-1))) := by positivity
      _ = ((-270332) + (127727746 * t)) := by ring
  have g6 : 0 ≤ (1081352 : ℤ) := by norm_num
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_fixed7 (t : ℤ)
    (ht : 1 ≤ t) :
    c3DoubledGates 128 t
      ![![228, 0, (3456 * t), 0], ![0, 0, (513 * t), 12], ![1819, 0, 0, 0], ![0, 3, ((-1) + (127 * t)), 3]] := by
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((150218 + (1033958144 * t)) : ℤ) := by
    calc
      0 ≤ (1034108362 + (1033958144 * (t-1))) := by positivity
      _ = (150218 + (1033958144 * t)) := by ring
  have g1 : 0 ≤ ((150276 + (71442 * t)) : ℤ) := by
    calc
      0 ≤ (221718 + (71442 * (t-1))) := by positivity
      _ = (150276 + (71442 * t)) := by ring
  have g2 : 0 ≤ ((270332 + (261764882 * t)) : ℤ) := by
    calc
      0 ≤ (262035214 + (261764882 * (t-1))) := by positivity
      _ = (270332 + (261764882 * t)) := by ring
  have g3 : 0 ≤ (((-30164) + (74910976 * t)) : ℤ) := by
    calc
      0 ≤ (74880812 + (74910976 * (t-1))) := by positivity
      _ = ((-30164) + (74910976 * t)) := by ring
  have g4 : 0 ≤ (((-300526) + (1698030 * t)) : ℤ) := by
    calc
      0 ≤ (1397504 + (1698030 * (t-1))) := by positivity
      _ = ((-300526) + (1698030 * t)) := by ring
  have g5 : 0 ≤ (((-540668) + (12970222 * t)) : ℤ) := by
    calc
      0 ≤ (12429554 + (12970222 * (t-1))) := by positivity
      _ = ((-540668) + (12970222 * t)) := by ring
  have g6 : 0 ≤ (2162696 : ℤ) := by norm_num
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_even (h t a : ℤ)
    (hh : 256 ≤ h) (ht : 1 ≤ t) (ha : 24*a+40=43*h) :
    c3DoubledGates h t
      ![![a, 0, (27 * h * t), 0], ![0, 0, ((2 * t) + (4 * h * t)), 12], ![((-1) + ((-1) * a) + (16 * h)), 0, 0, 0], ![0, 3, ((-1) + ((-2) * t) + (h * t)), 3]] := by
  have hH : 0 ≤ h-256 := by omega
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((2 + (66 * a) + (1056 * h) + ((-2560) * t * (h ^ 2)) + (486 * h * t) + (36864 * a * h * t)) : ℤ) := by
    have heq : 24 * (2 + (66 * a) + (1056 * h) + ((-2560) * t * (h ^ 2)) + (486 * h * t) + (36864 * a * h * t)) = ((-2592) + (28182 * h) + ((-1462896) * h * t) + (1523712 * t * (h ^ 2))) := by
      linear_combination (66 + (36864 * h * t)) * ha
    have hp : 0 ≤ (((-2592) + (28182 * h) + ((-1462896) * h * t) + (1523712 * t * (h ^ 2))) : ℤ) := by
      calc
        0 ≤ (99490700256 + (1523712 * ((h-256) ^ 2)) + (778705830 * (h-256)) + (99483488256 * (t-1)) + (1523712 * (t-1) * ((h-256) ^ 2)) + (778677648 * (h-256) * (t-1))) := by positivity
        _ = ((-2592) + (28182 * h) + ((-1462896) * h * t) + (1523712 * t * (h ^ 2))) := by ring
    nlinarith only [heq, hp]
  have g1 : 0 ≤ ((60 + (36 * t) + (66 * a) + (1056 * h) + ((-66048) * t * (h ^ 2)) + (66606 * h * t) + (36864 * a * h * t)) : ℤ) := by
    have heq : 24 * (60 + (36 * t) + (66 * a) + (1056 * h) + ((-66048) * t * (h ^ 2)) + (66606 * h * t) + (36864 * a * h * t)) = ((-1200) + (864 * t) + (28182 * h) + (123984 * h * t)) := by
      linear_combination (66 + (36864 * h * t)) * ha
    have hp : 0 ≤ (((-1200) + (864 * t) + (28182 * h) + (123984 * h * t)) : ℤ) := by
      calc
        0 ≤ (38954160 + (152166 * (h-256)) + (31740768 * (t-1)) + (123984 * (h-256) * (t-1))) := by positivity
        _ = ((-1200) + (864 * t) + (28182 * h) + (123984 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g2 : 0 ≤ (((-4) + (36 * t) + (2112 * h) + (15872 * t * (h ^ 2)) + (30318 * h * t)) : ℤ) := by
    have heq : 24 * ((-4) + (36 * t) + (2112 * h) + (15872 * t * (h ^ 2)) + (30318 * h * t)) = ((-96) + (864 * t) + (50688 * h) + (380928 * t * (h ^ 2)) + (727632 * h * t)) := by
      linear_combination 0 * ha
    have hp : 0 ≤ (((-96) + (864 * t) + (50688 * h) + (380928 * t * (h ^ 2)) + (727632 * h * t)) : ℤ) := by
      calc
        0 ≤ (25163748096 + (380928 * ((h-256) ^ 2)) + (195813456 * (h-256)) + (25150772064 * (t-1)) + (380928 * (t-1) * ((h-256) ^ 2)) + (195762768 * (h-256) * (t-1))) := by positivity
        _ = ((-96) + (864 * t) + (50688 * h) + (380928 * t * (h ^ 2)) + (727632 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g3 : 0 ≤ (((-68) + ((-132) * a) + ((-37350) * h * t) + (136192 * t * (h ^ 2)) + ((-73728) * a * h * t)) : ℤ) := by
    have heq : 24 * ((-68) + ((-132) * a) + ((-37350) * h * t) + (136192 * t * (h ^ 2)) + ((-73728) * a * h * t)) = (3648 + ((-5676) * h) + (98304 * t * (h ^ 2)) + (2052720 * h * t)) := by
      linear_combination ((-132) + ((-73728) * h * t)) * ha
    have hp : 0 ≤ ((3648 + ((-5676) * h) + (98304 * t * (h ^ 2)) + (2052720 * h * t)) : ℤ) := by
      calc
        0 ≤ (6966497856 + (98304 * ((h-256) ^ 2)) + (52378692 * (h-256)) + (6967947264 * (t-1)) + (98304 * (t-1) * ((h-256) ^ 2)) + (52384368 * (h-256) * (t-1))) := by positivity
        _ = (3648 + ((-5676) * h) + (98304 * t * (h ^ 2)) + (2052720 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g4 : 0 ≤ (((-94) + ((-2112) * h) + ((-132) * a) + ((-36) * t) + ((-118830) * h * t) + (132096 * t * (h ^ 2)) + ((-73728) * a * h * t)) : ℤ) := by
    have heq : 24 * ((-94) + ((-2112) * h) + ((-132) * a) + ((-36) * t) + ((-118830) * h * t) + (132096 * t * (h ^ 2)) + ((-73728) * a * h * t)) = (3024 + ((-56364) * h) + ((-864) * t) + (97200 * h * t)) := by
      linear_combination ((-132) + ((-73728) * h * t)) * ha
    have hp : 0 ≤ ((3024 + ((-56364) * h) + ((-864) * t) + (97200 * h * t)) : ℤ) := by
      calc
        0 ≤ (10456176 + (40836 * (h-256)) + (24882336 * (t-1)) + (97200 * (h-256) * (t-1))) := by positivity
        _ = (3024 + ((-56364) * h) + ((-864) * t) + (97200 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g5 : 0 ≤ ((4 + ((-4224) * h) + ((-36) * t) + ((-63534) * h * t) + (1024 * t * (h ^ 2))) : ℤ) := by
    have heq : 24 * (4 + ((-4224) * h) + ((-36) * t) + ((-63534) * h * t) + (1024 * t * (h ^ 2))) = (96 + ((-101376) * h) + ((-864) * t) + ((-1524816) * h * t) + (24576 * t * (h ^ 2))) := by
      linear_combination 0 * ha
    have hp : 0 ≤ ((96 + ((-101376) * h) + ((-864) * t) + ((-1524816) * h * t) + (24576 * t * (h ^ 2))) : ℤ) := by
      calc
        0 ≤ (1194306816 + (24576 * ((h-256) ^ 2)) + (10956720 * (h-256)) + (1220258976 * (t-1)) + (24576 * (t-1) * ((h-256) ^ 2)) + (11058096 * (h-256) * (t-1))) := by positivity
        _ = (96 + ((-101376) * h) + ((-864) * t) + ((-1524816) * h * t) + (24576 * t * (h ^ 2))) := by ring
    nlinarith only [heq, hp]
  have g6 : 0 ≤ ((8 + (16896 * h)) : ℤ) := by
    have heq : 24 * (8 + (16896 * h)) = (192 + (405504 * h)) := by
      linear_combination 0 * ha
    have hp : 0 ≤ ((192 + (405504 * h)) : ℤ) := by
      calc
        0 ≤ (103809216 + (405504 * (h-256))) := by positivity
        _ = (192 + (405504 * h)) := by ring
    nlinarith only [heq, hp]
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]

private theorem c3_odd (h t a : ℤ)
    (hh : 512 ≤ h) (ht : 1 ≤ t) (ha : 24*a+128=43*h) :
    c3DoubledGates h t
      ![![a, 0, (27 * h * t), 0], ![0, 0, ((10 * t) + (4 * h * t)), 12], ![((-1) + ((-1) * a) + (16 * h)), 0, 0, 0], ![0, 3, ((-1) + ((-10) * t) + (h * t)), 3]] := by
  have hH : 0 ≤ h-512 := by omega
  have hT : 0 ≤ t-1 := by omega
  have g0 : 0 ≤ ((2 + (66 * a) + (1056 * h) + ((-2560) * t * (h ^ 2)) + (486 * h * t) + (36864 * a * h * t)) : ℤ) := by
    have heq : 24 * (2 + (66 * a) + (1056 * h) + ((-2560) * t * (h ^ 2)) + (486 * h * t) + (36864 * a * h * t)) = ((-8400) + (28182 * h) + ((-4706928) * h * t) + (1523712 * t * (h ^ 2))) := by
      linear_combination (66 + (36864 * h * t)) * ha
    have hp : 0 ≤ (((-8400) + (28182 * h) + ((-4706928) * h * t) + (1523712 * t * (h ^ 2))) : ℤ) := by
      calc
        0 ≤ (397036432176 + (1523712 * ((h-512) ^ 2)) + (1555602342 * (h-512)) + (397022011392 * (t-1)) + (1523712 * (t-1) * ((h-512) ^ 2)) + (1555574160 * (h-512) * (t-1))) := by positivity
        _ = ((-8400) + (28182 * h) + ((-4706928) * h * t) + (1523712 * t * (h ^ 2))) := by ring
    nlinarith only [heq, hp]
  have g1 : 0 ≤ ((60 + (66 * a) + (180 * t) + (1056 * h) + ((-66048) * t * (h ^ 2)) + (201774 * h * t) + (36864 * a * h * t)) : ℤ) := by
    have heq : 24 * (60 + (66 * a) + (180 * t) + (1056 * h) + ((-66048) * t * (h ^ 2)) + (201774 * h * t) + (36864 * a * h * t)) = ((-7008) + (4320 * t) + (28182 * h) + (123984 * h * t)) := by
      linear_combination (66 + (36864 * h * t)) * ha
    have hp : 0 ≤ (((-7008) + (4320 * t) + (28182 * h) + (123984 * h * t)) : ℤ) := by
      calc
        0 ≤ (77906304 + (152166 * (h-512)) + (63484128 * (t-1)) + (123984 * (h-512) * (t-1))) := by positivity
        _ = ((-7008) + (4320 * t) + (28182 * h) + (123984 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g2 : 0 ≤ (((-4) + (180 * t) + (2112 * h) + (15872 * t * (h ^ 2)) + (165486 * h * t)) : ℤ) := by
    have heq : 24 * ((-4) + (180 * t) + (2112 * h) + (15872 * t * (h ^ 2)) + (165486 * h * t)) = ((-96) + (4320 * t) + (50688 * h) + (380928 * t * (h ^ 2)) + (3971664 * h * t)) := by
      linear_combination 0 * ha
    have hp : 0 ≤ (((-96) + (4320 * t) + (50688 * h) + (380928 * t * (h ^ 2)) + (3971664 * h * t)) : ℤ) := by
      calc
        0 ≤ (101917438080 + (380928 * ((h-512) ^ 2)) + (394092624 * (h-512)) + (101891485920 * (t-1)) + (380928 * (t-1) * ((h-512) ^ 2)) + (394041936 * (h-512) * (t-1))) := by positivity
        _ = ((-96) + (4320 * t) + (50688 * h) + (380928 * t * (h ^ 2)) + (3971664 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g3 : 0 ≤ (((-68) + ((-132) * a) + ((-37350) * h * t) + (136192 * t * (h ^ 2)) + ((-73728) * a * h * t)) : ℤ) := by
    have heq : 24 * ((-68) + ((-132) * a) + ((-37350) * h * t) + (136192 * t * (h ^ 2)) + ((-73728) * a * h * t)) = (15264 + ((-5676) * h) + (98304 * t * (h ^ 2)) + (8540784 * h * t)) := by
      linear_combination ((-132) + ((-73728) * h * t)) * ha
    have hp : 0 ≤ ((15264 + ((-5676) * h) + (98304 * t * (h ^ 2)) + (8540784 * h * t)) : ℤ) := by
      calc
        0 ≤ (30139794336 + (98304 * ((h-512) ^ 2)) + (109198404 * (h-512)) + (30142685184 * (t-1)) + (98304 * (t-1) * ((h-512) ^ 2)) + (109204080 * (h-512) * (t-1))) := by positivity
        _ = (15264 + ((-5676) * h) + (98304 * t * (h ^ 2)) + (8540784 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g4 : 0 ≤ (((-94) + ((-2112) * h) + ((-180) * t) + ((-132) * a) + ((-389166) * h * t) + (132096 * t * (h ^ 2)) + ((-73728) * a * h * t)) : ℤ) := by
    have heq : 24 * ((-94) + ((-2112) * h) + ((-180) * t) + ((-132) * a) + ((-389166) * h * t) + (132096 * t * (h ^ 2)) + ((-73728) * a * h * t)) = (14640 + ((-56364) * h) + ((-4320) * t) + (97200 * h * t)) := by
      linear_combination ((-132) + ((-73728) * h * t)) * ha
    have hp : 0 ≤ ((14640 + ((-56364) * h) + ((-4320) * t) + (97200 * h * t)) : ℤ) := by
      calc
        0 ≤ (20918352 + (40836 * (h-512)) + (49762080 * (t-1)) + (97200 * (h-512) * (t-1))) := by positivity
        _ = (14640 + ((-56364) * h) + ((-4320) * t) + (97200 * h * t)) := by ring
    nlinarith only [heq, hp]
  have g5 : 0 ≤ ((4 + ((-4224) * h) + ((-180) * t) + ((-333870) * h * t) + (1024 * t * (h ^ 2))) : ℤ) := by
    have heq : 24 * (4 + ((-4224) * h) + ((-180) * t) + ((-333870) * h * t) + (1024 * t * (h ^ 2))) = (96 + ((-101376) * h) + ((-4320) * t) + ((-8012880) * h * t) + (24576 * t * (h ^ 2))) := by
      linear_combination 0 * ha
    have hp : 0 ≤ ((96 + ((-101376) * h) + ((-4320) * t) + ((-8012880) * h * t) + (24576 * t * (h ^ 2))) : ℤ) := by
      calc
        0 ≤ (2287947648 + (24576 * ((h-512) ^ 2)) + (17051568 * (h-512)) + (2339852064 * (t-1)) + (24576 * (t-1) * ((h-512) ^ 2)) + (17152944 * (h-512) * (t-1))) := by positivity
        _ = (96 + ((-101376) * h) + ((-4320) * t) + ((-8012880) * h * t) + (24576 * t * (h ^ 2))) := by ring
    nlinarith only [heq, hp]
  have g6 : 0 ≤ ((8 + (16896 * h)) : ℤ) := by
    have heq : 24 * (8 + (16896 * h)) = (192 + (405504 * h)) := by
      linear_combination 0 * ha
    have hp : 0 ≤ ((192 + (405504 * h)) : ℤ) := by
      calc
        0 ≤ (207618240 + (405504 * (h-512))) := by positivity
        _ = (192 + (405504 * h)) := by ring
    nlinarith only [heq, hp]
  dsimp only [c3DoubledGates]
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ] <;> ring
  · norm_num [Fin.sum_univ_succ] <;> ring
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g0, g1, g2]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;>
      nlinarith only [g3, g4, g5, g6]


/- Cast the actual masks only after the two truncated subtractions have
   been justified by the original capacities.  No integral-alpha parameter
   is introduced in the public theorem. -/
private theorem c3_cast_banks (e ell : ℕ) (he : 2 ≤ e) :
    (fun i j => (c3Banks e ell i j : ℤ)) =
      ![![(c3Alpha e : ℤ),0,(c3High e 0 : ℤ)*(2^e : ℕ)*(2^ell : ℕ),0],
        ![0,0,4*(2^e : ℕ)*(2^ell : ℕ)+(c3R e : ℤ)*(2^ell : ℕ),12],
        ![16*(2^e : ℕ)-1-(c3Alpha e : ℤ),0,
          (c3High e 2 : ℤ)*(2^e : ℕ)*(2^ell : ℕ),0],
        ![0,3,(c3High e 3 : ℤ)*(2^e : ℕ)*(2^ell : ℕ)+
          (2^e : ℕ)*(2^ell : ℕ)-1-(c3R e : ℤ)*(2^ell : ℕ),3]] := by
  let h := (2 : ℕ)^e
  let t := (2 : ℕ)^ell
  let q := h*t
  have ht : 1 ≤ t := by
    have hp : 0 < t := by dsimp only [t]; positivity
    omega
  have hc := c3_capacities e (by omega)
  have hu : (16*h-1-c3Alpha e)+1+c3Alpha e = 16*h := by
    dsimp only [h]
    omega
  have hrt : c3R e*t+1 ≤ q := by
    have hr : c3R e+1 ≤ h := by dsimp only [h]; omega
    have hm := Nat.mul_le_mul_right t hr
    dsimp only [q]
    nlinarith only [hm, ht]
  have hw : (c3High e 3*q+q-1-c3R e*t)+1+c3R e*t = c3High e 3*q+q := by omega
  have hu' : ((16*h-1-c3Alpha e : ℕ) : ℤ) = 16*(h : ℤ)-1-(c3Alpha e : ℤ) := by
    have hx : ((16*h-1-c3Alpha e : ℕ) : ℤ)+1+(c3Alpha e : ℤ)=16*(h : ℤ) := by
      exact_mod_cast hu
    linarith only [hx]
  have hw' : ((c3High e 3*q+q-1-c3R e*t : ℕ) : ℤ) =
      (c3High e 3 : ℤ)*(q : ℤ)+(q : ℤ)-1-(c3R e : ℤ)*(t : ℤ) := by
    have hx : ((c3High e 3*q+q-1-c3R e*t : ℕ) : ℤ)+1+
        (c3R e : ℤ)*(t : ℤ) = (c3High e 3 : ℤ)*(q : ℤ)+(q : ℤ) := by
      exact_mod_cast hw
    linarith only [hx]
  dsimp only [h, t, q] at hu' hw'
  have hp1 : c3High e 1 = 4 := by
    unfold c3High
    split_ifs
    · split <;> rfl
    · rfl
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [c3Banks, hu', hw', hp1, Nat.cast_add, Nat.cast_mul] <;> ring

/--   Actual c3 banks, public e>=2 and every ell.
    All four old lower seams and new upper peaks are doubled integer
    inequalities; both complete telescopes are zero with separate fresh A.
    No centered-source or DataCertificate assertion is made here. -/
theorem c3_doubled_gates (e ell : ℕ) (he : 2 ≤ e) :
  let h : ℤ := ((2^e : ℕ) : ℤ)
  let t : ℤ := ((2^ell : ℕ) : ℤ)
  let M := fun i j => (c3Banks e ell i j : ℤ)
  let x : ℤ := 32
  let z : ℤ := 8
  let w := 32*h
  let y := 64*h*t
  let A := 1+x+x*y+x*y*z
  let B := 1+w+w*x+w*x*y
  let L := 1+z+w*z+w*z*x
  let K := 1+y+y*z+y*w*z
  let N := x*y*z*w-1
  let Q := 2*N+1
  let old : Fin 4 → ℤ := ![A,B,L,K]
  let new : Fin 4 → ℤ := ![2*A,2*B-1,2*L-z-1,2*K-y*(z+1)-1]
  let m := fun i => ∑ j : Fin 4, M i j * old j
  let n := fun i => ∑ j : Fin 4, M i j * new j
  let H : Fin 5 → ℤ := ![0,
    2*m 0+B-N,
    2*(m 0+m 1)+B+A-2*N,
    2*(m 0+m 1+m 2)+B+A+K-3*N,
    2*(m 0+m 1+m 2+m 3)+B+A+K+L-4*N]
  let G : Fin 5 → ℤ := ![2*A,
    2*A+2*n 0+(2*B-1)-Q,
    2*A+2*(n 0+n 1)+(2*B-1)+A-2*Q,
    2*A+2*(n 0+n 1+n 2)+(2*B-1)+A+(2*K-y*(z+1)-1)-3*Q,
    2*A+2*(n 0+n 1+n 2+n 3)+(2*B-1)+A+
      (2*K-y*(z+1)-1)+(2*L-z-1)-4*Q]
  H 4 = 0 ∧ G 4 = 0 ∧
    (∀ i : Fin 4, 0 ≤ H i.succ) ∧
    (∀ i : Fin 4, G i.castSucc+2*n i ≤ 2*N)
 := by
  change c3DoubledGates ((2^e : ℕ) : ℤ) ((2^ell : ℕ) : ℤ)
    (fun i j => (c3Banks e ell i j : ℤ))
  rw [c3_cast_banks e ell he]
  have htNat : 1 ≤ (2 : ℕ)^ell := by
    have hp : 0 < (2 : ℕ)^ell := by positivity
    omega
  have ht : (1 : ℤ) ≤ ((2^ell : ℕ) : ℤ) := by exact_mod_cast htNat
  by_cases hs : e < 8
  · have he7 : e ≤ 7 := by omega
    interval_cases e
    · convert c3_fixed2 ((2^ell : ℕ) : ℤ) ht using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [c3Alpha, c3R, c3High] <;> ring
    · convert c3_fixed3 ((2^ell : ℕ) : ℤ) ht using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [c3Alpha, c3R, c3High] <;> ring
    · convert c3_fixed4 ((2^ell : ℕ) : ℤ) ht using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [c3Alpha, c3R, c3High] <;> ring
    · convert c3_fixed5 ((2^ell : ℕ) : ℤ) ht using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [c3Alpha, c3R, c3High] <;> ring
    · convert c3_fixed6 ((2^ell : ℕ) : ℤ) ht using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [c3Alpha, c3R, c3High] <;> ring
    · convert c3_fixed7 ((2^ell : ℕ) : ℤ) ht using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [c3Alpha, c3R, c3High] <;> ring
  · have he8 : 8 ≤ e := by omega
    have hx := c3_tail_exact e he8
    by_cases hp : e % 2 = 0
    · simp only [hp, ite_true] at hx
      have hh : (256 : ℤ) ≤ ((2^e : ℕ) : ℤ) := by
        exact_mod_cast (show 256 ≤ (2 : ℕ)^e from
          by simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he8)
      have ha : 24*(c3Alpha e : ℤ)+40=43*((2^e : ℕ) : ℤ) := by exact_mod_cast hx.2
      convert c3_even ((2^e : ℕ) : ℤ) ((2^ell : ℕ) : ℤ) (c3Alpha e : ℤ) hh ht ha using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> simp [c3High, hs, hx.1] <;> ring
    · simp only [hp, ite_false] at hx
      have hh : (512 : ℤ) ≤ ((2^e : ℕ) : ℤ) := by
        exact_mod_cast (show 512 ≤ (2 : ℕ)^e from
          by simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hx.1)
      have ha : 24*(c3Alpha e : ℤ)+128=43*((2^e : ℕ) : ℤ) := by exact_mod_cast hx.2.2
      convert c3_odd ((2^e : ℕ) : ℤ) ((2^ell : ℕ) : ℤ) (c3Alpha e : ℤ) hh ht ha using 1 <;>
        ext i j <;> fin_cases i <;> fin_cases j <;> simp [c3High, hs, hx.2.1] <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
