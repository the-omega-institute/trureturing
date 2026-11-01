/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Chart1
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Exact positive polynomial identities for the low-bit c3plus chart. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private qHead qNewHead qMask qMass qNegative qPeak qExpr boundaryChartExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
private theorem chart1_0_0_0_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 0 0 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 0 0 =
      (7212 + (9748)*R + (47004 + (51968)*R)*V + (72576 + (75008)*R)*V^2 + (32768 + (32768)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 1 0 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 1 0 =
      (58844 + (55788)*R + (150636 + (144640)*R)*V + (124544 + (121600)*R)*V^2 + (32768 + (32768)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 0 1 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 0 1 =
      (345 + (2580)*R + (456 + (4864)*R)*V + (128 + (2304)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 1 1 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 1 1 =
      (20167 + (17900)*R + (40536 + (36096)*R)*V + (20352 + (18176)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 0 2 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 0 2 =
      (1328 + (3412)*R + (3360 + (7488)*R)*V + (2048 + (4096)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 1 2 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 1 2 =
      (3088 + (1004)*R + (5152 + (1024)*R)*V + (2048)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 0 3 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_0_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 0 1 3 := by
  have identity : boundaryChartExpr 0 0 Z V R 0 1 3 =
      (2082 + (4128)*V + (2048)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 0 0 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 0 0 =
      (54150 + (59156)*R + (173430 + (183296)*R)*V + (184832 + (189696)*R)*V^2 + (65536 + (65536)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 1 0 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 1 0 =
      (77962 + (71916)*R + (221850 + (209920)*R)*V + (209408 + (203520)*R)*V^2 + (65536 + (65536)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 0 1 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 0 1 =
      (14775 + (19220)*R + (29094 + (37888)*R)*V + (14336 + (18688)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 1 1 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 1 1 =
      (5737 + (1260)*R + (11898 + (3072)*R)*V + (6144 + (1792)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 0 2 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 0 2 =
      (3600 + (7764)*R + (7680 + (15936)*R)*V + (4096 + (8192)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 1 2 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 1 2 =
      (4912 + (748)*R + (9024 + (768)*R)*V + (4096)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 0 3 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_0_1_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 0 Z V R 1 1 3 := by
  have identity : boundaryChartExpr 0 0 Z V R 1 1 3 =
      (4162 + (8256)*V + (4096)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 0 0 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 0 0 =
      (7212 + (9748)*R + (47004 + (51968)*R)*V + (72576 + (75008)*R)*V^2 + (32768 + (32768)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 1 0 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 1 0 =
      (58844 + (55788)*R + (150636 + (144640)*R)*V + (124544 + (121600)*R)*V^2 + (32768 + (32768)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 0 1 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 0 1 =
      (345 + (2580)*R + (456 + (4864)*R)*V + (128 + (2304)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 1 1 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 1 1 =
      (20167 + (17900)*R + (40536 + (36096)*R)*V + (20352 + (18176)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 0 2 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 0 2 =
      (1328 + (3412)*R + (3360 + (7488)*R)*V + (2048 + (4096)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 1 2 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 1 2 =
      (3088 + (1004)*R + (5152 + (1024)*R)*V + (2048)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 0 3 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_0_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 0 1 3 := by
  have identity : boundaryChartExpr 0 1 Z V R 0 1 3 =
      (2082 + (4128)*V + (2048)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 0 0 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 0 0 =
      (54150 + (59156)*R + (173430 + (183296)*R)*V + (184832 + (189696)*R)*V^2 + (65536 + (65536)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 1 0 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 1 0 =
      (77962 + (71916)*R + (221850 + (209920)*R)*V + (209408 + (203520)*R)*V^2 + (65536 + (65536)*R)*V^3) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 0 1 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 0 1 =
      (14775 + (19220)*R + (29094 + (37888)*R)*V + (14336 + (18688)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 1 1 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 1 1 =
      (5737 + (1260)*R + (11898 + (3072)*R)*V + (6144 + (1792)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 0 2 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 0 2 =
      (3600 + (7764)*R + (7680 + (15936)*R)*V + (4096 + (8192)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 1 2 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 1 2 =
      (4912 + (748)*R + (9024 + (768)*R)*V + (4096)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 0 3 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_0_1_1_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 0 1 Z V R 1 1 3 := by
  have identity : boundaryChartExpr 0 1 Z V R 1 1 3 =
      (4162 + (8256)*V + (4096)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 0 0 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 0 0 =
      (2540069 + (2613055)*R + (6632940 + (6778624)*R)*V + (5665792 + (5738496)*R)*V^2 + (1572864 + (1572864)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 1 0 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 1 0 =
      (1662459 + (1581249)*R + (5966388 + (5804288)*R)*V + (6925312 + (6844416)*R)*V^2 + (2621440 + (2621440)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 0 1 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 0 1 =
      (87417 + (155455)*R + (154944 + (290560)*R)*V + (67584 + (135168)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 1 1 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 1 1 =
      (1092487 + (1024193)*R + (2204608 + (2068736)*R)*V + (1112064 + (1044480)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 0 2 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 0 2 =
      (26782 + (59684)*R + (59520 + (125184)*R)*V + (32768 + (65536)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 1 2 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 1 2 =
      (41058 + (8156)*R + (73856 + (8192)*R)*V + (32768)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 0 3 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_0_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 0 1 3 := by
  have identity : boundaryChartExpr 1 0 Z V R 0 1 3 =
      (32900 + (65664)*V + (32768)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 0 0 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 0 0 =
      (7384587 + (7530047)*R + (17892816 + (18183680)*R)*V + (13654016 + (13799424)*R)*V^2 + (3145728 + (3145728)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 1 0 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 1 0 =
      (1020469 + (858561)*R + (7305840 + (6982144)*R)*V + (11528192 + (11366400)*R)*V^2 + (5242880 + (5242880)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 0 1 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 0 1 =
      (1004401 + (1140287)*R + (1987384 + (2258432)*R)*V + (983040 + (1118208)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 1 1 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 1 1 =
      (175503 + (39361)*R + (372168 + (100864)*R)*V + (196608 + (61440)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 0 2 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 0 2 =
      (60446 + (126244)*R + (125952 + (257280)*R)*V + (65536 + (131072)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 1 2 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 1 2 =
      (72930 + (7132)*R + (138496 + (7168)*R)*V + (65536)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 0 3 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_0_1_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 0 Z V R 1 1 3 := by
  have identity : boundaryChartExpr 1 0 Z V R 1 1 3 =
      (65796 + (131328)*V + (65536)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 0 0 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 0 0 =
      (2474268 + (2613055)*R + (6501612 + (6778624)*R)*V + (5600256 + (5738496)*R)*V^2 + (1572864 + (1572864)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 1 0 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 1 0 =
      (1728260 + (1581249)*R + (6097716 + (5804288)*R)*V + (6990848 + (6844416)*R)*V^2 + (2621440 + (2621440)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 0 1 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 0 1 =
      (21616 + (155455)*R + (23616 + (290560)*R)*V + (2048 + (135168)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 1 1 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 1 1 =
      (1158288 + (1024193)*R + (2335936 + (2068736)*R)*V + (1177600 + (1044480)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 0 2 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 0 2 =
      (26782 + (59684)*R + (59520 + (125184)*R)*V + (32768 + (65536)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 1 2 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 1 2 =
      (41058 + (8156)*R + (73856 + (8192)*R)*V + (32768)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 0 3 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_0_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 0 1 3 := by
  have identity : boundaryChartExpr 1 1 Z V R 0 1 3 =
      (32900 + (65664)*V + (32768)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 0 0 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 0 0 =
      (7252994 + (7530047)*R + (17630160 + (18183680)*R)*V + (13522944 + (13799424)*R)*V^2 + (3145728 + (3145728)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 1 0 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 1 0 =
      (1152062 + (858561)*R + (7568496 + (6982144)*R)*V + (11659264 + (11366400)*R)*V^2 + (5242880 + (5242880)*R)*V^3) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 0 1 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 0 1 =
      (872808 + (1140287)*R + (1724728 + (2258432)*R)*V + (851968 + (1118208)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 1 1 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 1 1 =
      (307096 + (39361)*R + (634824 + (100864)*R)*V + (327680 + (61440)*R)*V^2) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 0 2 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 0 2 =
      (60446 + (126244)*R + (125952 + (257280)*R)*V + (65536 + (131072)*R)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 1 2 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 1 2 =
      (72930 + (7132)*R + (138496 + (7168)*R)*V + (65536)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 0 3 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_1_1_1_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 1 1 Z V R 1 1 3 := by
  have identity : boundaryChartExpr 1 1 Z V R 1 1 3 =
      (65796 + (131328)*V + (65536)*V^2) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 0 0 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 0 0 =
      (280485892 + (284930252)*R + (727064400 + (735948800)*R)*V + (614350848 + (618790912)*R)*V^2 + (167772160 + (167772160)*R)*V^3 + (84800511 + (85896716)*R + (219519988 + (221711872)*R)*V + (185051136 + (186146816)*R)*V^2 + (50331648 + (50331648)*R)*V^3)*Z + (10243808 + (10345136)*R + (26478880 + (26681520)*R)*V + (22264384 + (22365696)*R)*V^2 + (6029312 + (6029312)*R)*V^3)*Z^2 + (617976 + (622136)*R + (1594840 + (1603160)*R)*V + (1337312 + (1341472)*R)*V^2 + (360448 + (360448)*R)*V^3)*Z^3 + (18616 + (18680)*R + (47960 + (48088)*R)*V + (40096 + (40160)*R)*V^2 + (10752 + (10752)*R)*V^3)*Z^4 + (224 + (224)*R + (576 + (576)*R)*V + (480 + (480)*R)*V^2 + (128 + (128)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 1 0 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 1 0 =
      (256647420 + (251940660)*R + (884072880 + (874663936)*R)*V + (996524032 + (991821824)*R)*V^2 + (369098752 + (369098752)*R)*V^3 + (83020817 + (81875444)*R + (283894812 + (281604608)*R)*V + (318314496 + (317169664)*R)*V^2 + (117440512 + (117440512)*R)*V^3)*Z + (10730784 + (10626384)*R + (36441824 + (36233040)*R)*V + (40653248 + (40548864)*R)*V^2 + (14942208 + (14942208)*R)*V^3)*Z^2 + (692808 + (688584)*R + (2337448 + (2329000)*R)*V + (2594912 + (2590688)*R)*V^2 + (950272 + (950272)*R)*V^3)*Z^3 + (22344 + (22280)*R + (74920 + (74792)*R)*V + (82784 + (82720)*R)*V^2 + (30208 + (30208)*R)*V^3)*Z^4 + (288 + (288)*R + (960 + (960)*R)*V + (1056 + (1056)*R)*V^2 + (384 + (384)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 0 1 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 0 1 =
      (5936308 + (10203340)*R + (10195968 + (18722816)*R)*V + (4259840 + (8519680)*R)*V^2 + (1473163 + (2534924)*R + (2534016 + (4656640)*R)*V + (1060864 + (2121728)*R)*V^2)*Z + (137108 + (236208)*R + (236180 + (434352)*R)*V + (99072 + (198144)*R)*V^2)*Z^2 + (5672 + (9784)*R + (9784 + (18008)*R)*V + (4112 + (8224)*R)*V^2)*Z^3 + (88 + (152)*R + (152 + (280)*R)*V + (64 + (128)*R)*V^2)*Z^4) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 1 1 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 1 1 =
      (136674124 + (132402996)*R + (275020800 + (266489856)*R)*V + (138346496 + (134086656)*R)*V^2 + (42567541 + (41505268)*R + (85546880 + (83423744)*R)*V + (42979328 + (41918464)*R)*V^2)*Z + (5302396 + (5203280)*R + (10642812 + (10444624)*R)*V + (5340416 + (5241344)*R)*V^2)*Z^2 + (330200 + (326088)*R + (661960 + (653736)*R)*V + (331760 + (327648)*R)*V^2)*Z^3 + (10280 + (10216)*R + (20584 + (20456)*R)*V + (10304 + (10240)*R)*V^2)*Z^4 + (128 + (128)*R + (256 + (256)*R)*V + (128 + (128)*R)*V^2)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 0 2 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 0 2 =
      (951412 + (2001032)*R + (1999872 + (4098048)*R)*V + (1048576 + (2097152)*R)*V^2 + (243847 + (506120)*R + (505984 + (1030400)*R)*V + (262144 + (524288)*R)*V^2)*Z + (23428 + (48008)*R + (48004 + (97160)*R)*V + (24576 + (49152)*R)*V^2)*Z^2 + (1000 + (2024)*R + (2024 + (4072)*R)*V + (1024 + (2048)*R)*V^2)*Z^3 + (16 + (32)*R + (32 + (64)*R)*V + (16 + (32)*R)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 1 2 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 1 2 =
      (1180556 + (130936)*R + (2229248 + (131072)*R)*V + (1048576)*V^2 + (286841 + (24568)*R + (548992 + (24576)*R)*V + (262144)*V^2)*Z + (26116 + (1536)*R + (50692 + (1536)*R)*V + (24576)*V^2)*Z^2 + (1056 + (32)*R + (2080 + (32)*R)*V + (1024)*V^2)*Z^3 + (16 + (32)*V + (16)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 0 3 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_0_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 0 1 3 := by
  have identity : boundaryChartExpr 2 0 Z V R 0 1 3 =
      (1049616 + (2098176)*V + (1048576)*V^2 + (262273 + (524416)*V + (262144)*V^2)*Z + (24580 + (49156)*V + (24576)*V^2)*Z^2 + (1024 + (2048)*V + (1024)*V^2)*Z^3 + (16 + (32)*V + (16)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 0 0 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 0 0 =
      (842293020 + (851173580)*R + (2018434656 + (2036195328)*R)*V + (1511686144 + (1520566272)*R)*V^2 + (335544320 + (335544320)*R)*V^3 + (256721903 + (258913292)*R + (613692388 + (618075136)*R)*V + (457633792 + (459825152)*R)*V^2 + (100663296 + (100663296)*R)*V^3)*Z + (31277920 + (31480544)*R + (74576352 + (74981600)*R)*V + (55357056 + (55559680)*R)*V^2 + (12058624 + (12058624)*R)*V^3)*Z^2 + (1904056 + (1912376)*R + (4527448 + (4544088)*R)*V + (3344288 + (3352608)*R)*V^2 + (720896 + (720896)*R)*V^3)*Z^3 + (57912 + (58040)*R + (137304 + (137560)*R)*V + (100896 + (101024)*R)*V^2 + (21504 + (21504)*R)*V^3)*Z^4 + (704 + (704)*R + (1664 + (1664)*R)*V + (1216 + (1216)*R)*V^2 + (256 + (256)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 1 0 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 1 0 =
      (231973604 + (222568244)*R + (1203839904 + (1185030144)*R)*V + (1710063616 + (1700659200)*R)*V^2 + (738197504 + (738197504)*R)*V^3 + (78920753 + (76631028)*R + (393137212 + (388557824)*R)*V + (549097472 + (546807808)*R)*V^2 + (234881024 + (234881024)*R)*V^3)*Z + (10671264 + (10462496)*R + (51265056 + (50847520)*R)*V + (70478208 + (70269440)*R)*V^2 + (29884416 + (29884416)*R)*V^3)*Z^2 + (717512 + (709064)*R + (3337128 + (3320232)*R)*V + (4520160 + (4511712)*R)*V^2 + (1900544 + (1900544)*R)*V^3)*Z^3 + (24008 + (23880)*R + (108456 + (108200)*R)*V + (144864 + (144736)*R)*V^2 + (60416 + (60416)*R)*V^3)*Z^4 + (320 + (320)*R + (1408 + (1408)*R)*V + (1856 + (1856)*R)*V^2 + (768 + (768)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 0 1 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 0 1 =
      (114930804 + (123461836)*R + (228176832 + (245227520)*R)*V + (113246208 + (121765888)*R)*V^2 + (35016327 + (37139468)*R + (69619324 + (73864192)*R)*V + (34603008 + (36724736)*R)*V^2)*Z + (4265140 + (4463328)*R + (8492212 + (8888544)*R)*V + (4227072 + (4425216)*R)*V^2)*Z^2 + (259608 + (267832)*R + (517656 + (534104)*R)*V + (258048 + (266272)*R)*V^2)*Z^3 + (7896 + (8024)*R + (15768 + (16024)*R)*V + (7872 + (8000)*R)*V^2)*Z^4 + (96 + (96)*R + (192 + (192)*R)*V + (96 + (96)*R)*V^2)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 1 1 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 1 1 =
      (27679628 + (19144500)*R + (57039936 + (39985152)*R)*V + (29360128 + (20840448)*R)*V^2 + (9024377 + (6900724)*R + (18461572 + (14216192)*R)*V + (9437184 + (7315456)*R)*V^2)*Z + (1174364 + (976160)*R + (2386780 + (1990432)*R)*V + (1212416 + (1014272)*R)*V^2)*Z^2 + (76264 + (68040)*R + (154088 + (137640)*R)*V + (77824 + (69600)*R)*V^2)*Z^3 + (2472 + (2344)*R + (4968 + (4712)*R)*V + (2496 + (2368)*R)*V^2)*Z^4 + (32 + (32)*R + (64 + (64)*R)*V + (32 + (32)*R)*V^2)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 0 2 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 0 2 =
      (2007156 + (4106376)*R + (4104192 + (8300544)*R)*V + (2097152 + (4194304)*R)*V^2 + (506887 + (1031432)*R + (1031168 + (2080000)*R)*V + (524288 + (1048576)*R)*V^2)*Z + (48032 + (97192)*R + (97184 + (195496)*R)*V + (49152 + (98304)*R)*V^2)*Z^2 + (2024 + (4072)*R + (4072 + (8168)*R)*V + (2048 + (4096)*R)*V^2)*Z^3 + (32 + (64)*R + (64 + (128)*R)*V + (32 + (64)*R)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 1 2 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 1 2 =
      (2221964 + (122744)*R + (4319232 + (122880)*R)*V + (2097152)*V^2 + (548089 + (23544)*R + (1072384 + (23552)*R)*V + (524288)*V^2)*Z + (50664 + (1504)*R + (99816 + (1504)*R)*V + (49152)*V^2)*Z^2 + (2080 + (32)*R + (4128 + (32)*R)*V + (2048)*V^2)*Z^3 + (32 + (64)*V + (32)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 0 3 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_0_1_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 0 Z V R 1 1 3 := by
  have identity : boundaryChartExpr 2 0 Z V R 1 1 3 =
      (2099216 + (4196352)*V + (2097152)*V^2 + (524545 + (1048832)*V + (524288)*V^2)*Z + (49160 + (98312)*V + (49152)*V^2)*Z^2 + (2048 + (4096)*V + (2048)*V^2)*Z^3 + (32 + (64)*V + (32)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 0 0 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 0 0 =
      (276287424 + (284930252)*R + (718671696 + (735948800)*R)*V + (610156544 + (618790912)*R)*V^2 + (167772160 + (167772160)*R)*V^3 + (83751419 + (85896716)*R + (217422324 + (221711872)*R)*V + (184002560 + (186146816)*R)*V^2 + (50331648 + (50331648)*R)*V^3)*Z + (10145488 + (10345136)*R + (26282256 + (26681520)*R)*V + (22166080 + (22365696)*R)*V^2 + (6029312 + (6029312)*R)*V^3)*Z^2 + (613880 + (622136)*R + (1586648 + (1603160)*R)*V + (1333216 + (1341472)*R)*V^2 + (360448 + (360448)*R)*V^3)*Z^3 + (18552 + (18680)*R + (47832 + (48088)*R)*V + (40032 + (40160)*R)*V^2 + (10752 + (10752)*R)*V^3)*Z^4 + (224 + (224)*R + (576 + (576)*R)*V + (480 + (480)*R)*V^2 + (128 + (128)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 1 0 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 1 0 =
      (260845888 + (251940660)*R + (892465584 + (874663936)*R)*V + (1000718336 + (991821824)*R)*V^2 + (369098752 + (369098752)*R)*V^3 + (84069909 + (81875444)*R + (285992476 + (281604608)*R)*V + (319363072 + (317169664)*R)*V^2 + (117440512 + (117440512)*R)*V^3)*Z + (10829104 + (10626384)*R + (36638448 + (36233040)*R)*V + (40751552 + (40548864)*R)*V^2 + (14942208 + (14942208)*R)*V^3)*Z^2 + (696904 + (688584)*R + (2345640 + (2329000)*R)*V + (2599008 + (2590688)*R)*V^2 + (950272 + (950272)*R)*V^3)*Z^3 + (22408 + (22280)*R + (75048 + (74792)*R)*V + (82848 + (82720)*R)*V^2 + (30208 + (30208)*R)*V^3)*Z^4 + (288 + (288)*R + (960 + (960)*R)*V + (1056 + (1056)*R)*V^2 + (384 + (384)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 0 1 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 0 1 =
      (1737840 + (10203340)*R + (1803264 + (18722816)*R)*V + (65536 + (8519680)*R)*V^2 + (424071 + (2534924)*R + (436352 + (4656640)*R)*V + (12288 + (2121728)*R)*V^2)*Z + (38788 + (236208)*R + (39556 + (434352)*R)*V + (768 + (198144)*R)*V^2)*Z^2 + (1576 + (9784)*R + (1592 + (18008)*R)*V + (16 + (8224)*R)*V^2)*Z^3 + (24 + (152)*R + (24 + (280)*R)*V + ((128)*R)*V^2)*Z^4) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 1 1 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 1 1 =
      (140872592 + (132402996)*R + (283413504 + (266489856)*R)*V + (142540800 + (134086656)*R)*V^2 + (43616633 + (41505268)*R + (87644544 + (83423744)*R)*V + (44027904 + (41918464)*R)*V^2)*Z + (5400716 + (5203280)*R + (10839436 + (10444624)*R)*V + (5438720 + (5241344)*R)*V^2)*Z^2 + (334296 + (326088)*R + (670152 + (653736)*R)*V + (335856 + (327648)*R)*V^2)*Z^3 + (10344 + (10216)*R + (20712 + (20456)*R)*V + (10368 + (10240)*R)*V^2)*Z^4 + (128 + (128)*R + (256 + (256)*R)*V + (128 + (128)*R)*V^2)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 0 2 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 0 2 =
      (951412 + (2001032)*R + (1999872 + (4098048)*R)*V + (1048576 + (2097152)*R)*V^2 + (243847 + (506120)*R + (505984 + (1030400)*R)*V + (262144 + (524288)*R)*V^2)*Z + (23428 + (48008)*R + (48004 + (97160)*R)*V + (24576 + (49152)*R)*V^2)*Z^2 + (1000 + (2024)*R + (2024 + (4072)*R)*V + (1024 + (2048)*R)*V^2)*Z^3 + (16 + (32)*R + (32 + (64)*R)*V + (16 + (32)*R)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 1 2 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 1 2 =
      (1180556 + (130936)*R + (2229248 + (131072)*R)*V + (1048576)*V^2 + (286841 + (24568)*R + (548992 + (24576)*R)*V + (262144)*V^2)*Z + (26116 + (1536)*R + (50692 + (1536)*R)*V + (24576)*V^2)*Z^2 + (1056 + (32)*R + (2080 + (32)*R)*V + (1024)*V^2)*Z^3 + (16 + (32)*V + (16)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 0 3 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_0_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 0 1 3 := by
  have identity : boundaryChartExpr 2 1 Z V R 0 1 3 =
      (1049616 + (2098176)*V + (1048576)*V^2 + (262273 + (524416)*V + (262144)*V^2)*Z + (24580 + (49156)*V + (24576)*V^2)*Z^2 + (1024 + (2048)*V + (1024)*V^2)*Z^3 + (16 + (32)*V + (16)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_0_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 0 0 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 0 0 =
      (833896152 + (851173580)*R + (2001649248 + (2036195328)*R)*V + (1503297536 + (1520566272)*R)*V^2 + (335544320 + (335544320)*R)*V^3 + (254623723 + (258913292)*R + (609497060 + (618075136)*R)*V + (455536640 + (459825152)*R)*V^2 + (100663296 + (100663296)*R)*V^3)*Z + (31081280 + (31480544)*R + (74183104 + (74981600)*R)*V + (55160448 + (55559680)*R)*V^2 + (12058624 + (12058624)*R)*V^3)*Z^2 + (1895864 + (1912376)*R + (4511064 + (4544088)*R)*V + (3336096 + (3352608)*R)*V^2 + (720896 + (720896)*R)*V^3)*Z^3 + (57784 + (58040)*R + (137048 + (137560)*R)*V + (100768 + (101024)*R)*V^2 + (21504 + (21504)*R)*V^3)*Z^4 + (704 + (704)*R + (1664 + (1664)*R)*V + (1216 + (1216)*R)*V^2 + (256 + (256)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_1_0 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 1 0 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 1 0 =
      (240370472 + (222568244)*R + (1220625312 + (1185030144)*R)*V + (1718452224 + (1700659200)*R)*V^2 + (738197504 + (738197504)*R)*V^3 + (81018933 + (76631028)*R + (397332540 + (388557824)*R)*V + (551194624 + (546807808)*R)*V^2 + (234881024 + (234881024)*R)*V^3)*Z + (10867904 + (10462496)*R + (51658304 + (50847520)*R)*V + (70674816 + (70269440)*R)*V^2 + (29884416 + (29884416)*R)*V^3)*Z^2 + (725704 + (709064)*R + (3353512 + (3320232)*R)*V + (4528352 + (4511712)*R)*V^2 + (1900544 + (1900544)*R)*V^3)*Z^3 + (24136 + (23880)*R + (108712 + (108200)*R)*V + (144992 + (144736)*R)*V^2 + (60416 + (60416)*R)*V^3)*Z^4 + (320 + (320)*R + (1408 + (1408)*R)*V + (1856 + (1856)*R)*V^2 + (768 + (768)*R)*V^3)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_0_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 0 1 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 0 1 =
      (106533936 + (123461836)*R + (211391424 + (245227520)*R)*V + (104857600 + (121765888)*R)*V^2 + (32918147 + (37139468)*R + (65423996 + (73864192)*R)*V + (32505856 + (36724736)*R)*V^2)*Z + (4068500 + (4463328)*R + (8098964 + (8888544)*R)*V + (4030464 + (4425216)*R)*V^2)*Z^2 + (251416 + (267832)*R + (501272 + (534104)*R)*V + (249856 + (266272)*R)*V^2)*Z^3 + (7768 + (8024)*R + (15512 + (16024)*R)*V + (7744 + (8000)*R)*V^2)*Z^4 + (96 + (96)*R + (192 + (192)*R)*V + (96 + (96)*R)*V^2)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_1_1 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 1 1 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 1 1 =
      (36076496 + (19144500)*R + (73825344 + (39985152)*R)*V + (37748736 + (20840448)*R)*V^2 + (11122557 + (6900724)*R + (22656900 + (14216192)*R)*V + (11534336 + (7315456)*R)*V^2)*Z + (1371004 + (976160)*R + (2780028 + (1990432)*R)*V + (1409024 + (1014272)*R)*V^2)*Z^2 + (84456 + (68040)*R + (170472 + (137640)*R)*V + (86016 + (69600)*R)*V^2)*Z^3 + (2600 + (2344)*R + (5224 + (4712)*R)*V + (2624 + (2368)*R)*V^2)*Z^4 + (32 + (32)*R + (64 + (64)*R)*V + (32 + (32)*R)*V^2)*Z^5) / 8 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_0_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 0 2 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 0 2 =
      (2007156 + (4106376)*R + (4104192 + (8300544)*R)*V + (2097152 + (4194304)*R)*V^2 + (506887 + (1031432)*R + (1031168 + (2080000)*R)*V + (524288 + (1048576)*R)*V^2)*Z + (48032 + (97192)*R + (97184 + (195496)*R)*V + (49152 + (98304)*R)*V^2)*Z^2 + (2024 + (4072)*R + (4072 + (8168)*R)*V + (2048 + (4096)*R)*V^2)*Z^3 + (32 + (64)*R + (64 + (128)*R)*V + (32 + (64)*R)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_1_2 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 1 2 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 1 2 =
      (2221964 + (122744)*R + (4319232 + (122880)*R)*V + (2097152)*V^2 + (548089 + (23544)*R + (1072384 + (23552)*R)*V + (524288)*V^2)*Z + (50664 + (1504)*R + (99816 + (1504)*R)*V + (49152)*V^2)*Z^2 + (2080 + (32)*R + (4128 + (32)*R)*V + (2048)*V^2)*Z^3 + (32 + (64)*V + (32)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_0_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 0 3 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 0 3 =
      (0) / 1 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_2_1_1_1_3 (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R) :
    0 ≤ boundaryChartExpr 2 1 Z V R 1 1 3 := by
  have identity : boundaryChartExpr 2 1 Z V R 1 1 3 =
      (2099216 + (4196352)*V + (2097152)*V^2 + (524545 + (1048832)*V + (524288)*V^2)*Z + (49160 + (98312)*V + (49152)*V^2)*Z^2 + (2048 + (4096)*V + (2048)*V^2)*Z^3 + (32 + (64)*V + (32)*V^2)*Z^4) / 2 := by
    norm_num [boundaryChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart1_nonnegative (mode : Fin 3) (endpoint : Fin 2)
    (Z V R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hR : 0 ≤ R)
    (row kind bank : Fin 4) (hr : row.val < 2) (hk : kind.val < 2) :
    0 ≤ boundaryChartExpr mode endpoint Z V R row kind bank := by
  fin_cases mode <;> fin_cases endpoint <;> fin_cases row <;> fin_cases kind <;> fin_cases bank
  all_goals first | omega | skip
  all_goals first
    | exact chart1_0_0_0_0_0 Z V R hZ hV hR
    | exact chart1_0_0_0_1_0 Z V R hZ hV hR
    | exact chart1_0_0_0_0_1 Z V R hZ hV hR
    | exact chart1_0_0_0_1_1 Z V R hZ hV hR
    | exact chart1_0_0_0_0_2 Z V R hZ hV hR
    | exact chart1_0_0_0_1_2 Z V R hZ hV hR
    | exact chart1_0_0_0_0_3 Z V R hZ hV hR
    | exact chart1_0_0_0_1_3 Z V R hZ hV hR
    | exact chart1_0_0_1_0_0 Z V R hZ hV hR
    | exact chart1_0_0_1_1_0 Z V R hZ hV hR
    | exact chart1_0_0_1_0_1 Z V R hZ hV hR
    | exact chart1_0_0_1_1_1 Z V R hZ hV hR
    | exact chart1_0_0_1_0_2 Z V R hZ hV hR
    | exact chart1_0_0_1_1_2 Z V R hZ hV hR
    | exact chart1_0_0_1_0_3 Z V R hZ hV hR
    | exact chart1_0_0_1_1_3 Z V R hZ hV hR
    | exact chart1_0_1_0_0_0 Z V R hZ hV hR
    | exact chart1_0_1_0_1_0 Z V R hZ hV hR
    | exact chart1_0_1_0_0_1 Z V R hZ hV hR
    | exact chart1_0_1_0_1_1 Z V R hZ hV hR
    | exact chart1_0_1_0_0_2 Z V R hZ hV hR
    | exact chart1_0_1_0_1_2 Z V R hZ hV hR
    | exact chart1_0_1_0_0_3 Z V R hZ hV hR
    | exact chart1_0_1_0_1_3 Z V R hZ hV hR
    | exact chart1_0_1_1_0_0 Z V R hZ hV hR
    | exact chart1_0_1_1_1_0 Z V R hZ hV hR
    | exact chart1_0_1_1_0_1 Z V R hZ hV hR
    | exact chart1_0_1_1_1_1 Z V R hZ hV hR
    | exact chart1_0_1_1_0_2 Z V R hZ hV hR
    | exact chart1_0_1_1_1_2 Z V R hZ hV hR
    | exact chart1_0_1_1_0_3 Z V R hZ hV hR
    | exact chart1_0_1_1_1_3 Z V R hZ hV hR
    | exact chart1_1_0_0_0_0 Z V R hZ hV hR
    | exact chart1_1_0_0_1_0 Z V R hZ hV hR
    | exact chart1_1_0_0_0_1 Z V R hZ hV hR
    | exact chart1_1_0_0_1_1 Z V R hZ hV hR
    | exact chart1_1_0_0_0_2 Z V R hZ hV hR
    | exact chart1_1_0_0_1_2 Z V R hZ hV hR
    | exact chart1_1_0_0_0_3 Z V R hZ hV hR
    | exact chart1_1_0_0_1_3 Z V R hZ hV hR
    | exact chart1_1_0_1_0_0 Z V R hZ hV hR
    | exact chart1_1_0_1_1_0 Z V R hZ hV hR
    | exact chart1_1_0_1_0_1 Z V R hZ hV hR
    | exact chart1_1_0_1_1_1 Z V R hZ hV hR
    | exact chart1_1_0_1_0_2 Z V R hZ hV hR
    | exact chart1_1_0_1_1_2 Z V R hZ hV hR
    | exact chart1_1_0_1_0_3 Z V R hZ hV hR
    | exact chart1_1_0_1_1_3 Z V R hZ hV hR
    | exact chart1_1_1_0_0_0 Z V R hZ hV hR
    | exact chart1_1_1_0_1_0 Z V R hZ hV hR
    | exact chart1_1_1_0_0_1 Z V R hZ hV hR
    | exact chart1_1_1_0_1_1 Z V R hZ hV hR
    | exact chart1_1_1_0_0_2 Z V R hZ hV hR
    | exact chart1_1_1_0_1_2 Z V R hZ hV hR
    | exact chart1_1_1_0_0_3 Z V R hZ hV hR
    | exact chart1_1_1_0_1_3 Z V R hZ hV hR
    | exact chart1_1_1_1_0_0 Z V R hZ hV hR
    | exact chart1_1_1_1_1_0 Z V R hZ hV hR
    | exact chart1_1_1_1_0_1 Z V R hZ hV hR
    | exact chart1_1_1_1_1_1 Z V R hZ hV hR
    | exact chart1_1_1_1_0_2 Z V R hZ hV hR
    | exact chart1_1_1_1_1_2 Z V R hZ hV hR
    | exact chart1_1_1_1_0_3 Z V R hZ hV hR
    | exact chart1_1_1_1_1_3 Z V R hZ hV hR
    | exact chart1_2_0_0_0_0 Z V R hZ hV hR
    | exact chart1_2_0_0_1_0 Z V R hZ hV hR
    | exact chart1_2_0_0_0_1 Z V R hZ hV hR
    | exact chart1_2_0_0_1_1 Z V R hZ hV hR
    | exact chart1_2_0_0_0_2 Z V R hZ hV hR
    | exact chart1_2_0_0_1_2 Z V R hZ hV hR
    | exact chart1_2_0_0_0_3 Z V R hZ hV hR
    | exact chart1_2_0_0_1_3 Z V R hZ hV hR
    | exact chart1_2_0_1_0_0 Z V R hZ hV hR
    | exact chart1_2_0_1_1_0 Z V R hZ hV hR
    | exact chart1_2_0_1_0_1 Z V R hZ hV hR
    | exact chart1_2_0_1_1_1 Z V R hZ hV hR
    | exact chart1_2_0_1_0_2 Z V R hZ hV hR
    | exact chart1_2_0_1_1_2 Z V R hZ hV hR
    | exact chart1_2_0_1_0_3 Z V R hZ hV hR
    | exact chart1_2_0_1_1_3 Z V R hZ hV hR
    | exact chart1_2_1_0_0_0 Z V R hZ hV hR
    | exact chart1_2_1_0_1_0 Z V R hZ hV hR
    | exact chart1_2_1_0_0_1 Z V R hZ hV hR
    | exact chart1_2_1_0_1_1 Z V R hZ hV hR
    | exact chart1_2_1_0_0_2 Z V R hZ hV hR
    | exact chart1_2_1_0_1_2 Z V R hZ hV hR
    | exact chart1_2_1_0_0_3 Z V R hZ hV hR
    | exact chart1_2_1_0_1_3 Z V R hZ hV hR
    | exact chart1_2_1_1_0_0 Z V R hZ hV hR
    | exact chart1_2_1_1_1_0 Z V R hZ hV hR
    | exact chart1_2_1_1_0_1 Z V R hZ hV hR
    | exact chart1_2_1_1_1_1 Z V R hZ hV hR
    | exact chart1_2_1_1_0_2 Z V R hZ hV hR
    | exact chart1_2_1_1_1_2 Z V R hZ hV hR
    | exact chart1_2_1_1_0_3 Z V R hZ hV hR
    | exact chart1_2_1_1_1_3 Z V R hZ hV hR
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
