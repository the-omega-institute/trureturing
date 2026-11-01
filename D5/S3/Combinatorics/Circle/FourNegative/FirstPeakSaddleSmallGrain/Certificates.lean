/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Fifteen direct c2 charts and all 285 native polynomial margin proofs. -/
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! SOURCE_ONLY_UNCOMPILED. Original nineteen margins: twelve paired seams
and seven capacity bounds. Every polynomial proof term is preserved. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain

private def margin (t x y s r h v : ℤ) : Fin 19 → ℤ :=
  let D := 5*y+1
  let A := x*D+1
  let B := x*t*(y+1)+t+1
  let L := 4*x*t+4*t+5
  let M := 4*t*y+D
  let Bn := 2*B-1
  let Ln := 2*L-5
  let Mn := 2*M-D
  let E1 := (t-2*v)*A-2*s*M+2*h*L
  let F1 := 2*((t-1-2*v)*A-s*Mn+h*Ln)
  let E2 := B+L-2*v*A-2*r*M+2*h*L
  let F2 := Bn+Ln-4*v*A-2*r*Mn+2*h*Ln
  let E3 := 2*(h+1)*L-2*M
  let F3 := 2*((h+1)*Ln-Mn)
  ![E1,A-1-E1,F1,A-1-F1,E2,L-1-E2,F2,Ln-1-F2,
    E3,B-1-E3,F3,Bn-1-F3,s-1,x-2*s,r-1,s-r,v,t-2*v-2,y-8*(h+1)]

private def Margins (t x y s r h v : ℤ) : Prop :=
  ∀ i : Fin 19, 0 ≤ margin t x y s r h v i

set_option linter.unusedVariables false in
private theorem chart_K1_J1_t8 :
    Margins 8 (4*1*1*8) (2*1*8) (16*1*1) (4*1*1) (0) 0 := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 1768 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 824 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 942 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 1650 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 678 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 382 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 1998 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 118 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 936 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 3424 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 2024 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 6696 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 15 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 3 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 12 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 6 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 8 by norm_num) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J1_0 (T : ℤ) (hT : 0≤T) :
    Margins (16+10*T) (4*1*1*(16+10*T)) (2*1*(16+10*T)) (1*1*(2*(16+10*T)-4)) (1) (1) (2+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 8286+9520*T+2720*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 2018+3320*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 4968+5400*T+1440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 5336+7440*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 666+920*T+320*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 3498+4240*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 1638+2040*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 6686+8280*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 12242+15320*T+4800*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 21566+47410*T+34000*T^2+8000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 24786+30840*T+9600*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 42830+94620*T+68000*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 27+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 8 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 27+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 2+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 10+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 16+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J1_1 (T : ℤ) (hT : 0≤T) :
    Margins (32+10*T) (4*1*1*(32+10*T)) (2*1*(32+10*T)) (1*1*(2*(32+10*T)-4)) (1) (2*1) (4+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 30644+18272*T+2720*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 10444+7368*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 17610+10104*T+1440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 23478+15536*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 3120+1992*T+320*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 13396+8288*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 6856+4184*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 26172+16376*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 82076+51240*T+8000*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 184196+197090*T+69200*T^2+8000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 164764+102680*T+16000*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 367780+393980*T+138400*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 59+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 8 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 59+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 4+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 22+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 40+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J1_2 (T : ℤ) (hT : 0≤T) :
    Margins (64+10*T) (4*1*1*(64+10*T)) (2*1*(64+10*T)) (1*1*(2*(64+10*T))) (1*(4*1+1)) (1) (6+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 111934+34896*T+2720*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 52162+16344*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 59760+18552*T+1440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 104336+32688*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 7738+3256*T+320*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 58058+17264*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 21870+7512*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 109718+33528*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 196370+61400*T+4800*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 1917230+926770*T+149200*T^2+8000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 394002+123000*T+9600*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 3833198+1853340*T+298400*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 127+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 4 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 123+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 6+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 50+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 112+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J1_3 (T : ℤ) (hT : 0≤T) :
    Margins (128+10*T) (4*1*1*(128+10*T)) (2*1*(128+10*T)) (1*1*(2*(128+10*T))) (1*(4*1+1)) (0) (12+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 446056+69664*T+2720*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 209816+32776*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 236238+36888*T+1440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 419634+65552*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 41060+7304*T+320*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 221600+33696*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 94924+15608*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 430392+66392*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 260616+40840*T+1600*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 16582264+3901570*T+306000*T^2+8000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 523784+81880*T+3200*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 33161976+7802940*T+612000*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 255+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 4 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 251+20*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 12+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 102+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 248+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J2_t8 :
    Margins 8 (4*1*2*8) (2*1*8) (16*1*2) (4*1*2) (0) 0 := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 3528 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 1656 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 1870 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 3314 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 1310 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 774 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 3910 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 254 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 2984 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 5728 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 6120 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 11304 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 31 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 7 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 24 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 6 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 8 by norm_num) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J2_0 (T : ℤ) (hT : 0≤T) :
    Margins (16+10*T) (4*1*2*(16+10*T)) (2*1*(16+10*T)) (1*2*(2*(16+10*T)-4)) (2) (1) (2+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 16422+18952*T+5440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 4186+6728*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 9648+10624*T+2880*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 10960+15056*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 1112+1712*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 7148+8568*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 2852+3824*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 13664+16736*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 28626+35800*T+11200*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 38974+89650*T+66400*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 57554+71800*T+22400*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 77646+179100*T+132800*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 55+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 16 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 1 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 54+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 2+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 10+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 16+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J2_1 (T : ℤ) (hT : 0≤T) :
    Margins (32+10*T) (4*1*2*(32+10*T)) (2*1*(32+10*T)) (1*2*(2*(32+10*T)-4)) (2) (2*1) (4+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 60732+36376*T+5440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 21444+14904*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 34130+19872*T+2880*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 48046+31408*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 5550+3776*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 27350+16744*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 12358+7952*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 53438+33088*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 180380+112680*T+17600*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 352132+383970*T+136800*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 361372+225560*T+35200*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 703652+767740*T+273600*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 119+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 16 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 1 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 118+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 4+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 22+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 40+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J2_2 (T : ℤ) (hT : 0≤T) :
    Margins (64+10*T) (4*1*2*(64+10*T)) (2*1*(64+10*T)) (1*2*(2*(64+10*T))) (2*(4*1+1)) (1) (6+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 223294+69704*T+5440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 104898+32776*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 118384+36928*T+2880*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 209808+65552*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 14640+6384*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 116692+34616*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 42084+14768*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 220576+67232*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 458514+143320*T+11200*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 3768622+1833010*T+296800*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 918290+286840*T+22400*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 7535982+3665820*T+593600*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 255+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 9 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 246+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 6+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 50+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 112+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K1_J2_3 (T : ℤ) (hT : 0≤T) :
    Margins (128+10*T) (4*1*2*(128+10*T)) (2*1*(128+10*T)) (1*2*(2*(128+10*T))) (2*(4*1+1)) (0) (12+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 892008+139320*T+5440*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 419736+65560*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 472270+73760*T+2880*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 839474+131120*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 81498+14560*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 443306+67400*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 188610+31120*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 860994+132800*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 784904+122760*T+4800*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 32900728+7762050*T+610400*T^2+16000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 1572360+245720*T+9600*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 65798904+15523900*T+1220800*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 511+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 9 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 502+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 12+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 102+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 248+20*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K2_J1_t8 :
    Margins 8 (4*2*1*8) (2*2*8) (16*2*1) (4*2*1) (0) 0 := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 6600 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 3704 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 2894 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 7410 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 30 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 2054 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 2630 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 1534 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 1800 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 15104 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 3912 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 29896 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 31 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 7 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 24 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 6 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 24 by norm_num) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K2_J1_0 (T : ℤ) (hT : 0≤T) :
    Margins (16+10*T) (4*2*1*(16+10*T)) (2*2*(16+10*T)) (2*1*(2*(16+10*T)-4)) (1) (2) (2+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 31408+35992*T+10240*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 9680+15288*T+5760*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 16570+17504*T+4480*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 24518+33776*T+11520*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 1252+1792*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 7008+8488*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 3120+3984*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 13396+16576*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 40732+51040*T+16000*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 92404+197290*T+138400*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 82076+102480*T+32000*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 184196+394180*T+276800*T^2+64000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 55+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 16 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 55+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 2+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 10+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 40+40*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K2_J1_1 (T : ℤ) (hT : 0≤T) :
    Margins (32+10*T) (4*2*1*(32+10*T)) (2*2*(32+10*T)) (2*1*(2*(32+10*T)-4)) (1) (2*2) (4+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 115536+68856*T+10240*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 48560+33624*T+5760*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 56678+32032*T+4480*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 107418+70448*T+11520*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 6084+3936*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 26816+16584*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 13404+8272*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 52392+32768*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 294960+184320*T+28800*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 761840+803850*T+279200*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 591152+369040*T+57600*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 1522448+1607300*T+558400*T^2+64000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 119+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 16 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 119+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 4+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 22+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 88+40*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K2_J1_2 (T : ℤ) (hT : 0≤T) :
    Margins (64+10*T) (4*2*1*(64+10*T)) (2*2*(64+10*T)) (2*1*(2*(64+10*T))) (1*(4*2+1)) (2) (6+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 420424+131224*T+10240*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 235448+73656*T+5760*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 184954+57568*T+4480*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 470918+147312*T+11520*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 4924+4864*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 126408+36136*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 32880+13328*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 229780+68672*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 654364+204640*T+16000*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 7767076+3737770*T+599200*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 1311260+409680*T+32000*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 15531620+7475140*T+1198400*T^2+64000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 255+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 8 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 247+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 6+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 50+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 232+40*T by positivity) using 1 <;> dsimp [margin] <;> ring

set_option linter.unusedVariables false in
private theorem chart_K2_J1_3 (T : ℤ) (hT : 0≤T) :
    Margins (128+10*T) (4*2*1*(128+10*T)) (2*2*(128+10*T)) (2*1*(2*(128+10*T))) (1*(4*2+1)) (0) (12+T) := by
  intro i
  fin_cases i
  · -- old_first_lower
    convert (show (0 : ℤ) ≤ 1678440+262200*T+10240*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_first_upper
    convert (show (0 : ℤ) ≤ 944024+147480*T+5760*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_lower
    convert (show (0 : ℤ) ≤ 734414+114720*T+4480*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_first_upper
    convert (show (0 : ℤ) ≤ 1888050+294960*T+11520*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_lower
    convert (show (0 : ℤ) ≤ 61020+12960*T+640*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_second_upper
    convert (show (0 : ℤ) ≤ 463784+69000*T+2560*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_lower
    convert (show (0 : ℤ) ≤ 168132+29520*T+1280*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_second_upper
    convert (show (0 : ℤ) ≤ 881472+134400*T+5120*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_lower
    convert (show (0 : ℤ) ≤ 520200+81600*T+3200*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- old_third_upper
    convert (show (0 : ℤ) ≤ 66719864+15667530*T+1226400*T^2+32000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_lower
    convert (show (0 : ℤ) ≤ 1045512+163600*T+6400*T^2 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- new_third_upper
    convert (show (0 : ℤ) ≤ 133434616+31334660*T+2452800*T^2+64000*T^3 by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_positive
    convert (show (0 : ℤ) ≤ 511+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- s_capacity
    convert (show (0 : ℤ) ≤ 0 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_positive
    convert (show (0 : ℤ) ≤ 8 by norm_num) using 1 <;> dsimp [margin] <;> ring
  · -- r_capacity
    convert (show (0 : ℤ) ≤ 503+40*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_positive
    convert (show (0 : ℤ) ≤ 12+1*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- v_capacity
    convert (show (0 : ℤ) ≤ 102+8*T by positivity) using 1 <;> dsimp [margin] <;> ring
  · -- h_capacity
    convert (show (0 : ℤ) ≤ 504+40*T by positivity) using 1 <;> dsimp [margin] <;> ring


end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain
