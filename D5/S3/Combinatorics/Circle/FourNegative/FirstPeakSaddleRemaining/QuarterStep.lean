/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/QuarterStep
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:consumed-unbounded-polynomial-margins)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Four unbounded quarter-step phases, exact margins and native dyadic masks. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.ModTen

/-! SOURCE_ONLY_UNCOMPILED. Each sparse certificate is factored by Horner's
identity. `ring` must prove its equality to the original source margin;
`positivity` must prove its sign for unbounded nonnegative parameters.
No JSON, generator exit status or sampled parameter bound is a Lean premise.
The shared ModTen owner supplies the exact four exhaustive residue phases. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
open private rectangle scaled_margin grain_q high_margin half_margin quarter_margin from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic

set_option linter.unusedVariables false in
private theorem quarter_K1F2_t8 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 1 2 (1+Z) (8+10*T) (5*(1+Z)) 1 (1+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6080) * T + (8664)) * T + (3030)) * Z + (((6080) * T + (8792)) * T + (3148)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6720) * T + (8936)) * T + (2826)) * Z + (((6720) * T + (8848)) * T + (2746)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (2844)) * T + (1467)) * Z + (((1280) * T + (2932)) * T + (1541)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((320) * T + (1076)) * T + (661)) * Z + (((320) * T + (988)) * T + (585)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (5) * Z + (4) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (11) * Z + (11) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (1) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (4) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 1 exact coefficients
    convert (show (0 : ℤ) ≤
      (10) * T by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K1F2_t16 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 1 2 (1+Z) (16+10*T) (1*(1+Z)) 1 (2+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6080) * T + (19128)) * T + (15038)) * Z + (((6080) * T + (19256)) * T + (15258)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6720) * T + (18952)) * T + (13090)) * Z + (((6720) * T + (18864)) * T + (12940)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (5228)) * T + (5103)) * Z + (((1280) * T + (5316)) * T + (5247)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((320) * T + (1252)) * T + (1185)) * Z + (((320) * T + (1164)) * T + (1039)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 1 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * Z by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (15) * Z + (15) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (2) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (10) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (10) * T + (8) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K1F2_t32 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 1 2 (1+Z) (32+10*T) (5*(1+Z)) 0 (3+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6080) * T + (37976)) * T + (59254)) * Z + (((6080) * T + (38024)) * T + (59414)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6720) * T + (41064)) * T + (62570)) * Z + (((6720) * T + (41056)) * T + (62544)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (9116)) * T + (16075)) * Z + (((1280) * T + (9124)) * T + (16100)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((320) * T + (2484)) * T + (4677)) * Z + (((320) * T + (2476)) * T + (4650)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (5) * Z + (4) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (11) * Z + (11) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (3) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (24) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (10) * T + (28) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K1F2_t64 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 1 2 (1+Z) (64+10*T) (5*(1+Z)) 2 (7+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6080) * T + (76632)) * T + (241398)) * Z + (((6080) * T + (76840)) * T + (242754)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((6720) * T + (84328)) * T + (264426)) * Z + (((6720) * T + (84160)) * T + (263332)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (17052)) * T + (56715)) * Z + (((1280) * T + (17220)) * T + (57798)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((320) * T + (4788)) * T + (17541)) * Z + (((320) * T + (4620)) * T + (16456)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (5) * Z + (4) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (11) * Z + (11) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (7) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (48) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (10) * T + (52) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K2F1_t8 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 2 1 (1+Z) (8+10*T) (1*(1+Z)) 1 (1+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((4480) * T + (6704)) * T + (2494)) * Z + (((4480) * T + (6832)) * T + (2612)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((14720) * T + (17936)) * T + (4898)) * Z + (((14720) * T + (17848)) * T + (4818)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (4744)) * T + (2991)) * Z + (((1280) * T + (4832)) * T + (3065)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1920) * T + (3336)) * T + (1441)) * Z + (((1920) * T + (3248)) * T + (1365)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 1 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * Z by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (15) * Z + (15) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (1) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (4) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (20) * T + (8) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K2F1_t16 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 2 1 (1+Z) (16+10*T) (1*(1+Z)) 2 (2+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((4480) * T + (13808)) * T + (10622)) * Z + (((4480) * T + (14016)) * T + (10980)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((14720) * T + (41552)) * T + (28770)) * Z + (((14720) * T + (41384)) * T + (28482)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (6728)) * T + (7503)) * Z + (((1280) * T + (6896)) * T + (7780)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1920) * T + (6472)) * T + (5441)) * Z + (((1920) * T + (6304)) * T + (5162)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 1 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * Z by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (15) * Z + (15) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (2) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (10) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (20) * T + (20) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K2F1_t32 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 2 1 (1+Z) (32+10*T) (5*(1+Z)) 0 (3+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((4480) * T + (26736)) * T + (39670)) * Z + (((4480) * T + (26784)) * T + (39830)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((14720) * T + (90064)) * T + (137450)) * Z + (((14720) * T + (90056)) * T + (137424)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (10216)) * T + (19595)) * Z + (((1280) * T + (10224)) * T + (19620)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1920) * T + (13224)) * T + (22661)) * Z + (((1920) * T + (13216)) * T + (22634)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (5) * Z + (4) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (11) * Z + (11) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (3) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (24) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (20) * T + (60) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem quarter_K2F1_t64 (Z T : ℤ) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤quarter_margin 2 1 (1+Z) (64+10*T) (1*(1+Z)) 3 (7+T) i := by
  intro i
  fin_cases i
  · -- E_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((4480) * T + (56752)) * T + (179710)) * Z + (((4480) * T + (57040)) * T + (181588)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- E_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((14720) * T + (182928)) * T + (567778)) * Z + (((14720) * T + (182680)) * T + (566162)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_lower: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1280) * T + (18952)) * T + (68879)) * Z + (((1280) * T + (19200)) * T + (70479)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- H_upper: 6 exact coefficients
    convert (show (0 : ℤ) ≤
      (((1920) * T + (24968)) * T + (81153)) * Z + (((1920) * T + (24720)) * T + (79551)) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_lower: 1 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * Z by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- r_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (15) * Z + (15) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_lower: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (1) * T + (7) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- v_upper: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (8) * T + (48) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring
  · -- h_capacity: 2 exact coefficients
    convert (show (0 : ℤ) ≤
      (20) * T + (112) by positivity) using 1 <;>
      dsimp [quarter_margin,rectangle,grain_q] <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining

namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
open private rectangle grain_q quarter_margin ArithmeticSelection ArithmeticSelection.mk NativeChoice
  native_of_selection from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic
private def quarter_of_margins (K F f t r h v : ℤ) (hh : 0≤h)
    (hm : ∀ i, 0≤quarter_margin K F f t r h v i) :
    ArithmeticSelection t 4 K (2*F*f) := by
  have hr0 := hm 4
  have hr1 := hm 5
  have hv0 := hm 6
  have hv1 := hm 7
  have hhc := hm 8
  dsimp [quarter_margin] at hr0 hr1 hv0 hv1 hhc
  refine ArithmeticSelection.mk r h v ⟨by omega,by nlinarith only [hr1]⟩
    ⟨hh,by nlinarith only [hhc]⟩ ⟨hv0,by omega⟩ ?_
  intro i
  fin_cases i
  · exact hm 0
  · exact hm 1
  · exact hm 2
  · exact hm 3

open private quarter_phase_cover from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle.ModTen

private theorem quarter_arithmetic (d : ℕ) (K F f : ℤ)
    (hd : 3≤d) (hf : 1≤f)
    (hpair : (K=1 ∧ F=2) ∨ (K=2 ∧ F=1)) :
    Nonempty (ArithmeticSelection (2^d) 4 K (2*F*f)) := by
  have phases := quarter_phase_cover d hd
  rcases hpair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases phases with ⟨T,hT⟩|⟨T,hT⟩|⟨T,hT⟩|⟨T,hT⟩
    · have ht : (2:ℤ)^d=8+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 1 2 f (8+10*(T:ℤ))
        (5*f) 1 (1+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K1F2_t8 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
    · have ht : (2:ℤ)^d=16+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 1 2 f (16+10*(T:ℤ))
        (1*f) 1 (2+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K1F2_t16 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
    · have ht : (2:ℤ)^d=32+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 1 2 f (32+10*(T:ℤ))
        (5*f) 0 (3+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K1F2_t32 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
    · have ht : (2:ℤ)^d=64+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 1 2 f (64+10*(T:ℤ))
        (5*f) 2 (7+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K1F2_t64 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
  · rcases phases with ⟨T,hT⟩|⟨T,hT⟩|⟨T,hT⟩|⟨T,hT⟩
    · have ht : (2:ℤ)^d=8+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 2 1 f (8+10*(T:ℤ))
        (1*f) 1 (1+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K2F1_t8 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
    · have ht : (2:ℤ)^d=16+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 2 1 f (16+10*(T:ℤ))
        (1*f) 2 (2+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K2F1_t16 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
    · have ht : (2:ℤ)^d=32+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 2 1 f (32+10*(T:ℤ))
        (5*f) 0 (3+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K2F1_t32 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring
    · have ht : (2:ℤ)^d=64+10*(T:ℤ) := by exact_mod_cast hT
      rw [ht]
      refine ⟨quarter_of_margins 2 1 f (64+10*(T:ℤ))
        (1*f) 3 (7+(T:ℤ)) (by norm_num) ?_⟩
      intro i
      convert quarter_K2F1_t64 (f-1) (T:ℤ) (by omega)
        (by positivity) i using 1 <;> congr 1 <;> ring

/-- Consuming interface for c=2, b<=d+2 and a>=d+4. -/
private theorem quarter_step_choice_exists (a b d : ℕ)
    (hd : 3≤d) (hdb : d<b) (hba : b<a) (hb : b≤d+2) (ha : d+4≤a) :
    Nonempty (NativeChoice a b 2 d) := by
  let f : ℤ := 2^(a-d-4)
  have hf : 1≤f := by dsimp [f]; exact one_le_pow₀ (by norm_num)
  have hbcase : b=d+1 ∨ b=d+2 := by omega
  rcases hbcase with hb1|hb2
  · have hK : (2:ℤ)^(b-d-1)=1 := by rw [hb1]; simp
    have hJ : (2:ℤ)^(a-b-1)=2*2*f := by
      dsimp [f]
      have he : a-b-1=(a-d-4)+2 := by omega
      rw [he,pow_add]
      ring
    obtain ⟨sel⟩ := quarter_arithmetic d 1 2 f hd hf (Or.inl ⟨rfl,rfl⟩)
    refine ⟨native_of_selection a b 2 d (by omega) (by omega) hdb hba ?_⟩
    simpa only [hK,hJ,show (2:ℤ)^2=4 by norm_num] using sel
  · have hK : (2:ℤ)^(b-d-1)=2 := by rw [hb2]; simp
    have hJ : (2:ℤ)^(a-b-1)=2*1*f := by
      dsimp [f]
      have he : a-b-1=(a-d-4)+1 := by omega
      rw [he,pow_add]
      ring
    obtain ⟨sel⟩ := quarter_arithmetic d 2 1 f hd hf (Or.inr ⟨rfl,rfl⟩)
    refine ⟨native_of_selection a b 2 d (by omega) (by omega) hdb hba ?_⟩
    simpa only [hK,hJ,show (2:ℤ)^2=4 by norm_num] using sel

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
