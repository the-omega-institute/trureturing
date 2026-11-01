/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Chart0
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Exact positive polynomial identities for the low-bit c2 chart. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private qHead qNewHead qMask qMass qNegative qPeak qExpr chartExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
private theorem chart0_0_0_0 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 0 0 := by
  have identity : chartExpr 0 Z V T R 0 0 0 =
      (559673 + (579653)*R + (1106462 + (1126400)*R)*T + (546816 + (546816)*R)*T^2 + (3145258 + (3184704)*R + (6264336 + (6303744)*R)*T + (3119104 + (3119104)*R)*T^2)*V + (4682752 + (4702208)*R + (9352192 + (9371648)*R)*T + (4669440 + (4669440)*R)*T^2)*V^2 + (2097152 + (2097152)*R + (4194304 + (4194304)*R)*T + (2097152 + (2097152)*R)*T^2)*V^3) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 1 0 := by
  have identity : chartExpr 0 Z V T R 0 1 0 =
      (3638735 + (3614651)*R + (7286242 + (7262208)*R)*T + (3647488 + (3647488)*R)*T^2 + (9445854 + (9398208)*R + (18909680 + (18862080)*R)*T + (9463808 + (9463808)*R)*T^2)*V + (7904256 + (7880704)*R + (15817728 + (15794176)*R)*T + (7913472 + (7913472)*R)*T^2)*V^2 + (2097152 + (2097152)*R + (4194304 + (4194304)*R)*T + (2097152 + (2097152)*R)*T^2)*V^3) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 0 1 := by
  have identity : chartExpr 0 Z V T R 0 0 1 =
      (103294 + (120901)*R + (191326 + (208896)*R)*T + (88064 + (88064)*R)*T^2 + (135022 + (170048)*R + (239440 + (274432)*R)*T + (104448 + (104448)*R)*T^2)*V + (31744 + (49152)*R + (48128 + (65536)*R)*T + (16384 + (16384)*R)*T^2)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 1 1 := by
  have identity : chartExpr 0 Z V T R 0 1 1 =
      (1207682 + (1189819)*R + (2430370 + (2412544)*R)*T + (1222656 + (1222656)*R)*T^2 + (2486674 + (2451392)*R + (5003696 + (4968448)*R)*T + (2516992 + (2516992)*R)*T^2)*V + (1278976 + (1261568)*R + (2573312 + (2555904)*R)*T + (1294336 + (1294336)*R)*T^2)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_2 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 0 2 := by
  have identity : chartExpr 0 Z V T R 0 0 2 =
      (8944 + (25364)*R + (8704 + (25088)*R)*T + (25312 + (58112)*R + (25088 + (57856)*R)*T)*V + (16384 + (32768)*R + (16384 + (32768)*R)*T)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_2 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 1 2 := by
  have identity : chartExpr 0 Z V T R 0 1 2 =
      (26384 + (9964)*R + (26624 + (10240)*R)*T + (42784 + (9984)*R + (43008 + (10240)*R)*T)*V + (16384 + (16384)*T)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_3 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 0 3 := by
  have identity : chartExpr 0 Z V T R 0 0 3 =
      (0) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_3 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 0 1 3 := by
  have identity : chartExpr 0 Z V T R 0 1 3 =
      (16418 + (16384)*T + (32800 + (32768)*T)*V + (16384 + (16384)*T)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 0 0 := by
  have identity : chartExpr 0 Z V T R 1 0 0 =
      (3587667 + (3627141)*R + (7149086 + (7188480)*R)*T + (3561472 + (3561472)*R)*T^2 + (11298372 + (11376768)*R + (22543888 + (22622208)*R)*T + (11245568 + (11245568)*R)*T^2)*V + (11905024 + (11943936)*R + (23783424 + (23822336)*R)*T + (11878400 + (11878400)*R)*T^2)*V^2 + (4194304 + (4194304)*R + (8388608 + (8388608)*R)*T + (4194304 + (4194304)*R)*T^2)*V^3) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 1 0 := by
  have identity : chartExpr 0 Z V T R 1 1 0 =
      (4809149 + (4761467)*R + (9636322 + (9588736)*R)*T + (4827136 + (4827136)*R)*T^2 + (13883852 + (13789056)*R + (27804144 + (27709440)*R)*T + (13920256 + (13920256)*R)*T^2)*V + (13268992 + (13221888)*R + (26556416 + (26509312)*R)*T + (13287424 + (13287424)*R)*T^2)*V^2 + (4194304 + (4194304)*R + (8388608 + (8388608)*R)*T + (4194304 + (4194304)*R)*T^2)*V^3) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 0 1 := by
  have identity : chartExpr 0 Z V T R 1 0 1 =
      (1036188 + (1071237)*R + (2041694 + (2076672)*R)*T + (1005568 + (1005568)*R)*T^2 + (2000780 + (2070656)*R + (3940176 + (4009984)*R)*T + (1939456 + (1939456)*R)*T^2)*V + (964608 + (999424)*R + (1898496 + (1933312)*R)*T + (933888 + (933888)*R)*T^2)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 1 1 := by
  have identity : chartExpr 0 Z V T R 1 1 1 =
      (274788 + (239483)*R + (580002 + (544768)*R)*T + (305152 + (305152)*R)*T^2 + (620916 + (550784)*R + (1302960 + (1232896)*R)*T + (681984 + (681984)*R)*T^2)*V + (346112 + (311296)*R + (722944 + (688128)*R)*T + (376832 + (376832)*R)*T^2)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_2 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 0 2 := by
  have identity : chartExpr 0 Z V T R 1 0 2 =
      (25552 + (58388)*R + (25088 + (57856)*R)*T + (58304 + (123904)*R + (57856 + (123392)*R)*T)*V + (32768 + (65536)*R + (32768 + (65536)*R)*T)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_2 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 1 2 := by
  have identity : chartExpr 0 Z V T R 1 1 2 =
      (42544 + (9708)*R + (43008 + (10240)*R)*T + (75328 + (9728)*R + (75776 + (10240)*R)*T)*V + (32768 + (32768)*T)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_3 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 0 3 := by
  have identity : chartExpr 0 Z V T R 1 0 3 =
      (0) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_3 (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ chartExpr 0 Z V T R 1 1 3 := by
  have identity : chartExpr 0 Z V T R 1 1 3 =
      (32834 + (32768)*T + (65600 + (65536)*T)*V + (32768 + (32768)*T)*V^2) / 1 := by
    norm_num [chartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_nonnegative (Z V T R : ℚ)
    (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (row kind bank : Fin 4) (hr : row.val < 2) (hk : kind.val < 2) :
    0 ≤ chartExpr 0 Z V T R row kind bank := by
  fin_cases row <;> fin_cases kind <;> fin_cases bank
  all_goals first | omega | skip
  all_goals first
    | exact chart0_0_0_0 Z V T R hZ hV hT hR
    | exact chart0_0_1_0 Z V T R hZ hV hT hR
    | exact chart0_0_0_1 Z V T R hZ hV hT hR
    | exact chart0_0_1_1 Z V T R hZ hV hT hR
    | exact chart0_0_0_2 Z V T R hZ hV hT hR
    | exact chart0_0_1_2 Z V T R hZ hV hT hR
    | exact chart0_0_0_3 Z V T R hZ hV hT hR
    | exact chart0_0_1_3 Z V T R hZ hV hT hR
    | exact chart0_1_0_0 Z V T R hZ hV hT hR
    | exact chart0_1_1_0 Z V T R hZ hV hT hR
    | exact chart0_1_0_1 Z V T R hZ hV hT hR
    | exact chart0_1_1_1 Z V T R hZ hV hT hR
    | exact chart0_1_0_2 Z V T R hZ hV hT hR
    | exact chart0_1_1_2 Z V T R hZ hV hT hR
    | exact chart0_1_0_3 Z V T R hZ hV hT hR
    | exact chart0_1_1_3 Z V T R hZ hV hT hR
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
