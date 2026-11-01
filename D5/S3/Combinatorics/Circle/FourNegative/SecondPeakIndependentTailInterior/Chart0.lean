/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Chart0
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Exact positive polynomial identities at both even-rounding endpoints. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private qHead qNewHead qMask qMass qNegative qPeak qExpr evenChartExpr from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Model
private theorem chart0_0_0_0_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 0 0 := by
  have identity : evenChartExpr 0 0 Z V T R 0 0 0 =
      (74821 + (84874)*R + (143119 + (153088)*R)*T + (68352 + (68352)*R)*T^2 + (403004 + (422784)*R + (792840 + (812544)*R)*T + (389888 + (389888)*R)*T^2)*V + (590336 + (600064)*R + (1174016 + (1183744)*R)*T + (583680 + (583680)*R)*T^2)*V^2 + (262144 + (262144)*R + (524288 + (524288)*R)*T + (262144 + (262144)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 1 0 := by
  have identity : evenChartExpr 0 0 Z V T R 0 1 0 =
      (451531 + (439414)*R + (907505 + (895488)*R)*T + (455936 + (455936)*R)*T^2 + (1173972 + (1150080)*R + (2356984 + (2333184)*R)*T + (1182976 + (1182976)*R)*T^2)*V + (984576 + (972800)*R + (1973760 + (1961984)*R)*T + (989184 + (989184)*R)*T^2)*V^2 + (262144 + (262144)*R + (524288 + (524288)*R)*T + (262144 + (262144)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 0 1 := by
  have identity : evenChartExpr 0 0 Z V T R 0 0 1 =
      (18671 + (27530)*R + (29615 + (38400)*R)*T + (11008 + (11008)*R)*T^2 + (28388 + (45952)*R + (41384 + (58880)*R)*T + (13056 + (13056)*R)*T^2)*V + (9728 + (18432)*R + (11776 + (20480)*R)*T + (2048 + (2048)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 1 1 := by
  have identity : evenChartExpr 0 0 Z V T R 0 1 1 =
      (145297 + (136310)*R + (298193 + (289280)*R)*T + (152832 + (152832)*R)*T^2 + (299420 + (281728)*R + (614104 + (596480)*R)*T + (314624 + (314624)*R)*T^2)*V + (154112 + (145408)*R + (315904 + (307200)*R)*T + (161792 + (161792)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 0 2 := by
  have identity : evenChartExpr 0 0 Z V T R 0 0 2 =
      (2416 + (6548)*R + (2176 + (6272)*R)*T + (6496 + (14720)*R + (6272 + (14464)*R)*T)*V + (4096 + (8192)*R + (4096 + (8192)*R)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 1 2 := by
  have identity : evenChartExpr 0 0 Z V T R 0 1 2 =
      (6416 + (2284)*R + (6656 + (2560)*R)*T + (10528 + (2304)*R + (10752 + (2560)*R)*T)*V + (4096 + (4096)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 0 3 := by
  have identity : evenChartExpr 0 0 Z V T R 0 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_0_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 0 1 3 := by
  have identity : evenChartExpr 0 0 Z V T R 0 1 3 =
      (4130 + (4096)*T + (8224 + (8192)*T)*V + (4096 + (4096)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 0 0 := by
  have identity : evenChartExpr 0 0 Z V T R 1 0 0 =
      (458361 + (478218)*R + (903439 + (923136)*R)*T + (445184 + (445184)*R)*T^2 + (1432176 + (1471488)*R + (2837768 + (2876928)*R)*T + (1405696 + (1405696)*R)*T^2)*V + (1498112 + (1517568)*R + (2982912 + (3002368)*R)*T + (1484800 + (1484800)*R)*T^2)*V^2 + (524288 + (524288)*R + (1048576 + (1048576)*R)*T + (524288 + (524288)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 1 0 := by
  have identity : evenChartExpr 0 0 Z V T R 1 1 0 =
      (594343 + (570358)*R + (1197809 + (1174016)*R)*T + (603392 + (603392)*R)*T^2 + (1721776 + (1674240)*R + (3461880 + (3414528)*R)*T + (1740032 + (1740032)*R)*T^2)*V + (1651712 + (1628160)*R + (3312640 + (3289088)*R)*T + (1660928 + (1660928)*R)*T^2)*V^2 + (524288 + (524288)*R + (1048576 + (1048576)*R)*T + (524288 + (524288)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 0 1 := by
  have identity : evenChartExpr 0 0 Z V T R 1 0 1 =
      (141099 + (158730)*R + (266671 + (284160)*R)*T + (125696 + (125696)*R)*T^2 + (273184 + (308224)*R + (515496 + (550400)*R)*T + (242432 + (242432)*R)*T^2)*V + (132096 + (149504)*R + (248832 + (266240)*R)*T + (116736 + (116736)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 1 1 := by
  have identity : evenChartExpr 0 0 Z V T R 1 1 1 =
      (22869 + (5110)*R + (61137 + (43520)*R)*T + (38144 + (38144)*R)*T^2 + (54624 + (19456)*R + (139992 + (104960)*R)*T + (85248 + (85248)*R)*T^2)*V + (31744 + (14336)*R + (78848 + (61440)*R)*T + (47104 + (47104)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 0 2 := by
  have identity : evenChartExpr 0 0 Z V T R 1 0 2 =
      (6736 + (14996)*R + (6272 + (14464)*R)*T + (14912 + (31360)*R + (14464 + (30848)*R)*T)*V + (8192 + (16384)*R + (8192 + (16384)*R)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 1 2 := by
  have identity : evenChartExpr 0 0 Z V T R 1 1 2 =
      (10288 + (2028)*R + (10752 + (2560)*R)*T + (18496 + (2048)*R + (18944 + (2560)*R)*T)*V + (8192 + (8192)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 0 3 := by
  have identity : evenChartExpr 0 0 Z V T R 1 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_0_1_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 0 Z V T R 1 1 3 := by
  have identity : evenChartExpr 0 0 Z V T R 1 1 3 =
      (8258 + (8192)*T + (16448 + (16384)*T)*V + (8192 + (8192)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 0 0 := by
  have identity : evenChartExpr 0 1 Z V T R 0 0 0 =
      (71392 + (81448)*R + (139279 + (149248)*R)*T + (68352 + (68352)*R)*T^2 + (399548 + (419328)*R + (789000 + (808704)*R)*T + (389888 + (389888)*R)*T^2)*V + (590336 + (600064)*R + (1174016 + (1183744)*R)*T + (583680 + (583680)*R)*T^2)*V^2 + (262144 + (262144)*R + (524288 + (524288)*R)*T + (262144 + (262144)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 1 0 := by
  have identity : evenChartExpr 0 1 Z V T R 0 1 0 =
      (454960 + (442840)*R + (911345 + (899328)*R)*T + (455936 + (455936)*R)*T^2 + (1177428 + (1153536)*R + (2360824 + (2337024)*R)*T + (1182976 + (1182976)*R)*T^2)*V + (984576 + (972800)*R + (1973760 + (1961984)*R)*T + (989184 + (989184)*R)*T^2)*V^2 + (262144 + (262144)*R + (524288 + (524288)*R)*T + (262144 + (262144)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 0 1 := by
  have identity : evenChartExpr 0 1 Z V T R 0 0 1 =
      (15242 + (24104)*R + (25775 + (34560)*R)*T + (11008 + (11008)*R)*T^2 + (24932 + (42496)*R + (37544 + (55040)*R)*T + (13056 + (13056)*R)*T^2)*V + (9728 + (18432)*R + (11776 + (20480)*R)*T + (2048 + (2048)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 1 1 := by
  have identity : evenChartExpr 0 1 Z V T R 0 1 1 =
      (148726 + (139736)*R + (302033 + (293120)*R)*T + (152832 + (152832)*R)*T^2 + (302876 + (285184)*R + (617944 + (600320)*R)*T + (314624 + (314624)*R)*T^2)*V + (154112 + (145408)*R + (315904 + (307200)*R)*T + (161792 + (161792)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 0 2 := by
  have identity : evenChartExpr 0 1 Z V T R 0 0 2 =
      (2416 + (6548)*R + (2176 + (6272)*R)*T + (6496 + (14720)*R + (6272 + (14464)*R)*T)*V + (4096 + (8192)*R + (4096 + (8192)*R)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 1 2 := by
  have identity : evenChartExpr 0 1 Z V T R 0 1 2 =
      (6416 + (2284)*R + (6656 + (2560)*R)*T + (10528 + (2304)*R + (10752 + (2560)*R)*T)*V + (4096 + (4096)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 0 3 := by
  have identity : evenChartExpr 0 1 Z V T R 0 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_0_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 0 1 3 := by
  have identity : evenChartExpr 0 1 Z V T R 0 1 3 =
      (4130 + (4096)*T + (8224 + (8192)*T)*V + (4096 + (4096)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 0 0 := by
  have identity : evenChartExpr 0 1 Z V T R 1 0 0 =
      (455316 + (475176)*R + (899599 + (919296)*R)*T + (445184 + (445184)*R)*T^2 + (1429104 + (1468416)*R + (2833928 + (2873088)*R)*T + (1405696 + (1405696)*R)*T^2)*V + (1498112 + (1517568)*R + (2982912 + (3002368)*R)*T + (1484800 + (1484800)*R)*T^2)*V^2 + (524288 + (524288)*R + (1048576 + (1048576)*R)*T + (524288 + (524288)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 1 0 := by
  have identity : evenChartExpr 0 1 Z V T R 1 1 0 =
      (597388 + (573400)*R + (1201649 + (1177856)*R)*T + (603392 + (603392)*R)*T^2 + (1724848 + (1677312)*R + (3465720 + (3418368)*R)*T + (1740032 + (1740032)*R)*T^2)*V + (1651712 + (1628160)*R + (3312640 + (3289088)*R)*T + (1660928 + (1660928)*R)*T^2)*V^2 + (524288 + (524288)*R + (1048576 + (1048576)*R)*T + (524288 + (524288)*R)*T^2)*V^3) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 0 1 := by
  have identity : evenChartExpr 0 1 Z V T R 1 0 1 =
      (138054 + (155688)*R + (262831 + (280320)*R)*T + (125696 + (125696)*R)*T^2 + (270112 + (305152)*R + (511656 + (546560)*R)*T + (242432 + (242432)*R)*T^2)*V + (132096 + (149504)*R + (248832 + (266240)*R)*T + (116736 + (116736)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 1 1 := by
  have identity : evenChartExpr 0 1 Z V T R 1 1 1 =
      (25914 + (8152)*R + (64977 + (47360)*R)*T + (38144 + (38144)*R)*T^2 + (57696 + (22528)*R + (143832 + (108800)*R)*T + (85248 + (85248)*R)*T^2)*V + (31744 + (14336)*R + (78848 + (61440)*R)*T + (47104 + (47104)*R)*T^2)*V^2) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 0 2 := by
  have identity : evenChartExpr 0 1 Z V T R 1 0 2 =
      (6736 + (14996)*R + (6272 + (14464)*R)*T + (14912 + (31360)*R + (14464 + (30848)*R)*T)*V + (8192 + (16384)*R + (8192 + (16384)*R)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 1 2 := by
  have identity : evenChartExpr 0 1 Z V T R 1 1 2 =
      (10288 + (2028)*R + (10752 + (2560)*R)*T + (18496 + (2048)*R + (18944 + (2560)*R)*T)*V + (8192 + (8192)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 0 3 := by
  have identity : evenChartExpr 0 1 Z V T R 1 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_0_1_1_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 0 1 Z V T R 1 1 3 := by
  have identity : evenChartExpr 0 1 Z V T R 1 1 3 =
      (8258 + (8192)*T + (16448 + (16384)*T)*V + (8192 + (8192)*T)*V^2) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 0 0 := by
  have identity : evenChartExpr 1 0 Z V T R 0 0 0 =
      (20167186 + (20458532)*R + (40099898 + (40390656)*R)*T + (19933184 + (19933184)*R)*T^2 + (52677096 + (53259264)*R + (104886304 + (105467904)*R)*T + (52209664 + (52209664)*R)*T^2)*V + (45092864 + (45383680)*R + (89952256 + (90243072)*R)*T + (44859392 + (44859392)*R)*T^2)*V^2 + (12582912 + (12582912)*R + (25165824 + (25165824)*R)*T + (12582912 + (12582912)*R)*T^2)*V^3 + (11911809 + (12054276)*R + (23703559 + (23845888)*R)*T + (11791872 + (11791872)*R)*T^2 + (31049340 + (31334144)*R + (61858820 + (62143488)*R)*T + (30809600 + (30809600)*R)*T^2)*V + (26477568 + (26619904)*R + (52835328 + (52977664)*R)*T + (26357760 + (26357760)*R)*T^2)*V^2 + (7340032 + (7340032)*R + (14680064 + (14680064)*R)*T + (7340032 + (7340032)*R)*T^2)*V^3)*Z + (2805736 + (2831792)*R + (5588352 + (5614400)*R)*T + (2782624 + (2782624)*R)*T^2 + (7295016 + (7347120)*R + (14543808 + (14595904)*R)*T + (7248800 + (7248800)*R)*T^2)*V + (6193216 + (6219264)*R + (12363328 + (12389376)*R)*T + (6170112 + (6170112)*R)*T^2)*V^2 + (1703936 + (1703936)*R + (3407872 + (3407872)*R)*T + (1703936 + (1703936)*R)*T^2)*V^3)*Z^2 + (329296 + (331408)*R + (656608 + (658720)*R)*T + (327312 + (327312)*R)*T^2 + (853584 + (857808)*R + (1703200 + (1707424)*R)*T + (849616 + (849616)*R)*T^2)*V + (720896 + (723008)*R + (1439808 + (1441920)*R)*T + (718912 + (718912)*R)*T^2)*V^2 + (196608 + (196608)*R + (393216 + (393216)*R)*T + (196608 + (196608)*R)*T^2)*V^3)*Z^3 + (19248 + (19312)*R + (38432 + (38496)*R)*T + (19184 + (19184)*R)*T^2 + (49712 + (49840)*R + (99296 + (99424)*R)*T + (49584 + (49584)*R)*T^2)*V + (41728 + (41792)*R + (83392 + (83456)*R)*T + (41664 + (41664)*R)*T^2)*V^2 + (11264 + (11264)*R + (22528 + (22528)*R)*T + (11264 + (11264)*R)*T^2)*V^3)*Z^4 + (448 + (448)*R + (896 + (896)*R)*T + (448 + (448)*R)*T^2 + (1152 + (1152)*R + (2304 + (2304)*R)*T + (1152 + (1152)*R)*T^2)*V + (960 + (960)*R + (1920 + (1920)*R)*T + (960 + (960)*R)*T^2)*V^2 + (256 + (256)*R + (512 + (512)*R)*T + (256 + (256)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 1 0 := by
  have identity : evenChartExpr 1 0 Z V T R 0 1 0 =
      (13420078 + (13095900)*R + (27041734 + (26718208)*R)*T + (13621248 + (13621248)*R)*T^2 + (48051800 + (47404032)*R + (96505824 + (95858688)*R)*T + (48453632 + (48453632)*R)*T^2)*V + (55603200 + (55279616)*R + (111407104 + (111083520)*R)*T + (55803904 + (55803904)*R)*T^2)*V^2 + (20971520 + (20971520)*R + (41943040 + (41943040)*R)*T + (20971520 + (20971520)*R)*T^2)*V^3 + (9072007 + (8917244)*R + (18251769 + (18097152)*R)*T + (9179648 + (9179648)*R)*T^2 + (31889804 + (31580416)*R + (63994876 + (63685632)*R)*T + (32104960 + (32104960)*R)*T^2)*V + (36449280 + (36294656)*R + (73006080 + (72851456)*R)*T + (36556800 + (36556800)*R)*T^2)*V^2 + (13631488 + (13631488)*R + (27262976 + (27262976)*R)*T + (13631488 + (13631488)*R)*T^2)*V^3)*Z + (2438680 + (2411088)*R + (4898944 + (4871360)*R)*T + (2460256 + (2460256)*R)*T^2 + (8436696 + (8381520)*R + (16916544 + (16861376)*R)*T + (8479840 + (8479840)*R)*T^2)*V + (9536960 + (9509376)*R + (19095488 + (19067904)*R)*T + (9558528 + (9558528)*R)*T^2)*V^2 + (3538944 + (3538944)*R + (7077888 + (7077888)*R)*T + (3538944 + (3538944)*R)*T^2)*V^3)*Z^2 + (326128 + (323952)*R + (654176 + (652000)*R)*T + (328048 + (328048)*R)*T^2 + (1112624 + (1108272)*R + (2229088 + (2224736)*R)*T + (1116464 + (1116464)*R)*T^2)*V + (1245248 + (1243072)*R + (2492416 + (2490240)*R)*T + (1247168 + (1247168)*R)*T^2)*V^2 + (458752 + (458752)*R + (917504 + (917504)*R)*T + (458752 + (458752)*R)*T^2)*V^3)*Z^3 + (21712 + (21648)*R + (43488 + (43424)*R)*T + (21776 + (21776)*R)*T^2 + (73168 + (73040)*R + (146464 + (146336)*R)*T + (73296 + (73296)*R)*T^2)*V + (81152 + (81088)*R + (162368 + (162304)*R)*T + (81216 + (81216)*R)*T^2)*V^2 + (29696 + (29696)*R + (59392 + (59392)*R)*T + (29696 + (29696)*R)*T^2)*V^3)*Z^4 + (576 + (576)*R + (1152 + (1152)*R)*T + (576 + (576)*R)*T^2 + (1920 + (1920)*R + (3840 + (3840)*R)*T + (1920 + (1920)*R)*T^2)*V + (2112 + (2112)*R + (4224 + (4224)*R)*T + (2112 + (2112)*R)*T^2)*V^2 + (768 + (768)*R + (1536 + (1536)*R)*T + (768 + (768)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 0 1 := by
  have identity : evenChartExpr 1 0 Z V T R 0 0 1 =
      (526138 + (797732)*R + (798010 + (1069056)*R)*T + (272384 + (272384)*R)*T^2 + (812816 + (1354752)*R + (1117472 + (1658880)*R)*T + (305152 + (305152)*R)*T^2)*V + (286720 + (557056)*R + (319488 + (589824)*R)*T + (32768 + (32768)*R)*T^2)*V^2 + (254407 + (388868)*R + (380743 + (515072)*R)*T + (126464 + (126464)*R)*T^2 + (394690 + (663296)*R + (533316 + (801792)*R)*T + (138752 + (138752)*R)*T^2)*V + (140288 + (274432)*R + (152576 + (286720)*R)*T + (12288 + (12288)*R)*T^2)*V^2)*Z + (46108 + (71088)*R + (68020 + (92992)*R)*T + (21920 + (21920)*R)*T^2 + (71836 + (121776)*R + (95284 + (145216)*R)*T + (23456 + (23456)*R)*T^2)*V + (25728 + (50688)*R + (27264 + (52224)*R)*T + (1536 + (1536)*R)*T^2)*V^2)*Z^2 + (3712 + (5776)*R + (5392 + (7456)*R)*T + (1680 + (1680)*R)*T^2 + (5808 + (9936)*R + (7552 + (11680)*R)*T + (1744 + (1744)*R)*T^2)*V + (2096 + (4160)*R + (2160 + (4224)*R)*T + (64 + (64)*R)*T^2)*V^2)*Z^3 + (112 + (176)*R + (160 + (224)*R)*T + (48 + (48)*R)*T^2 + (176 + (304)*R + (224 + (352)*R)*T + (48 + (48)*R)*T^2)*V + (64 + (128)*R + (64 + (128)*R)*T)*V^2)*Z^4) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 1 1 := by
  have identity : evenChartExpr 1 0 Z V T R 0 1 1 =
      (8912070 + (8639452)*R + (18077382 + (17805312)*R)*T + (9164800 + (9164800)*R)*T^2 + (18062576 + (17519616)*R + (36632288 + (36089856)*R)*T + (18569216 + (18569216)*R)*T^2)*V + (9150464 + (8880128)*R + (18554880 + (18284544)*R)*T + (9404416 + (9404416)*R)*T^2)*V^2 + (5513017 + (5378300)*R + (11153849 + (11019264)*R)*T + (5640704 + (5640704)*R)*T^2 + (11139902 + (10871040)*R + (22535612 + (22266880)*R)*T + (11395584 + (11395584)*R)*T^2)*V + (5626880 + (5492736)*R + (11381760 + (11247616)*R)*T + (5754880 + (5754880)*R)*T^2)*V^2)*Z + (1362932 + (1337936)*R + (2750044 + (2725056)*R)*T + (1387104 + (1387104)*R)*T^2 + (2746228 + (2696272)*R + (5540828 + (5490880)*R)*T + (2794592 + (2794592)*R)*T^2)*V + (1383296 + (1358336)*R + (2790784 + (2765824)*R)*T + (1407488 + (1407488)*R)*T^2)*V^2)*Z^2 + (168320 + (166256)*R + (338672 + (336608)*R)*T + (170352 + (170352)*R)*T^2 + (338256 + (334128)*R + (680576 + (676448)*R)*T + (342320 + (342320)*R)*T^2)*V + (169936 + (167872)*R + (341904 + (339840)*R)*T + (171968 + (171968)*R)*T^2)*V^2)*Z^3 + (10384 + (10320)*R + (20832 + (20768)*R)*T + (10448 + (10448)*R)*T^2 + (20816 + (20688)*R + (41760 + (41632)*R)*T + (20944 + (20944)*R)*T^2)*V + (10432 + (10368)*R + (20928 + (20864)*R)*T + (10496 + (10496)*R)*T^2)*V^2)*Z^4 + (256 + (256)*R + (512 + (512)*R)*T + (256 + (256)*R)*T^2 + (512 + (512)*R + (1024 + (1024)*R)*T + (512 + (512)*R)*T^2)*V + (256 + (256)*R + (512 + (512)*R)*T + (256 + (256)*R)*T^2)*V^2)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 0 2 := by
  have identity : evenChartExpr 1 0 Z V T R 0 0 2 =
      (105276 + (236616)*R + (103424 + (234496)*R)*T + (236288 + (498688)*R + (234496 + (496640)*R)*T)*V + (131072 + (262144)*R + (131072 + (262144)*R)*T)*V^2 + (56007 + (121608)*R + (55552 + (121088)*R)*T + (121536 + (252672)*R + (121088 + (252160)*R)*T)*V + (65536 + (131072)*R + (65536 + (131072)*R)*T)*V^2)*Z + (11116 + (23408)*R + (11088 + (23376)*R)*T + (23404 + (47984)*R + (23376 + (47952)*R)*T)*V + (12288 + (24576)*R + (12288 + (24576)*R)*T)*V^2)*Z^2 + (976 + (2000)*R + (976 + (2000)*R)*T + (2000 + (4048)*R + (2000 + (4048)*R)*T)*V + (1024 + (2048)*R + (1024 + (2048)*R)*T)*V^2)*Z^3 + (32 + (64)*R + (32 + (64)*R)*T + (64 + (128)*R + (64 + (128)*R)*T)*V + (32 + (64)*R + (32 + (64)*R)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 1 2 := by
  have identity : evenChartExpr 1 0 Z V T R 0 1 2 =
      (166084 + (34744)*R + (167936 + (36864)*R)*T + (297216 + (34816)*R + (299008 + (36864)*R)*T)*V + (131072 + (131072)*T)*V^2 + (78393 + (12792)*R + (78848 + (13312)*R)*T + (143936 + (12800)*R + (144384 + (13312)*R)*T)*V + (65536 + (65536)*T)*V^2)*Z + (13860 + (1568)*R + (13888 + (1600)*R)*T + (26148 + (1568)*R + (26176 + (1600)*R)*T)*V + (12288 + (12288)*T)*V^2)*Z^2 + (1088 + (64)*R + (1088 + (64)*R)*T + (2112 + (64)*R + (2112 + (64)*R)*T)*V + (1024 + (1024)*T)*V^2)*Z^3 + (32 + (32)*T + (64 + (64)*T)*V + (32 + (32)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 0 3 := by
  have identity : evenChartExpr 1 0 Z V T R 0 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_0_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 0 1 3 := by
  have identity : evenChartExpr 1 0 Z V T R 0 1 3 =
      (131336 + (131072)*T + (262400 + (262144)*T)*V + (131072 + (131072)*T)*V^2 + (65601 + (65536)*T + (131136 + (131072)*T)*V + (65536 + (65536)*T)*V^2)*Z + (12292 + (12288)*T + (24580 + (24576)*T)*V + (12288 + (12288)*T)*V^2)*Z^2 + (1024 + (1024)*T + (2048 + (2048)*T)*V + (1024 + (1024)*T)*V^2)*Z^3 + (32 + (32)*T + (64 + (64)*T)*V + (32 + (32)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 0 0 := by
  have identity : evenChartExpr 1 0 Z V T R 1 0 0 =
      (58676190 + (59256868)*R + (116881466 + (117460992)*R)*T + (58206208 + (58206208)*R)*T^2 + (142275504 + (143437824)*R + (283613216 + (284774400)*R)*T + (141338624 + (141338624)*R)*T^2)*V + (108765184 + (109346816)*R + (217063424 + (217645056)*R)*T + (108298240 + (108298240)*R)*T^2)*V^2 + (25165824 + (25165824)*R + (50331648 + (50331648)*R)*T + (25165824 + (25165824)*R)*T^2)*V^3 + (35100921 + (35385348)*R + (69961223 + (70245376)*R)*T + (34860544 + (34860544)*R)*T^2 + (84766964 + (85336064)*R + (169053700 + (169622528)*R)*T + (84286976 + (84286976)*R)*T^2)*V + (64346112 + (64630784)*R + (128452608 + (128737280)*R)*T + (64106496 + (64106496)*R)*T^2)*V^2 + (14680064 + (14680064)*R + (29360128 + (29360128)*R)*T + (14680064 + (14680064)*R)*T^2)*V^3)*Z + (8383056 + (8435136)*R + (16719840 + (16771904)*R)*T + (8336800 + (8336800)*R)*T^2 + (20153552 + (20257728)*R + (40214624 + (40318784)*R)*T + (20061088 + (20061088)*R)*T^2)*V + (15178368 + (15230464)*R + (30310528 + (30362624)*R)*T + (15132160 + (15132160)*R)*T^2)*V^2 + (3407872 + (3407872)*R + (6815744 + (6815744)*R)*T + (3407872 + (3407872)*R)*T^2)*V^3)*Z^2 + (998928 + (1003152)*R + (1993888 + (1998112)*R)*T + (994960 + (994960)*R)*T^2 + (2389456 + (2397904)*R + (4770976 + (4779424)*R)*T + (2381520 + (2381520)*R)*T^2)*V + (1783744 + (1787968)*R + (3563520 + (3567744)*R)*T + (1779776 + (1779776)*R)*T^2)*V^2 + (393216 + (393216)*R + (786432 + (786432)*R)*T + (393216 + (393216)*R)*T^2)*V^3)*Z^3 + (59376 + (59504)*R + (118624 + (118752)*R)*T + (59248 + (59248)*R)*T^2 + (141232 + (141488)*R + (282208 + (282464)*R)*T + (140976 + (140976)*R)*T^2)*V + (104384 + (104512)*R + (208640 + (208768)*R)*T + (104256 + (104256)*R)*T^2)*V^2 + (22528 + (22528)*R + (45056 + (45056)*R)*T + (22528 + (22528)*R)*T^2)*V^3)*Z^4 + (1408 + (1408)*R + (2816 + (2816)*R)*T + (1408 + (1408)*R)*T^2 + (3328 + (3328)*R + (6656 + (6656)*R)*T + (3328 + (3328)*R)*T^2)*V + (2432 + (2432)*R + (4864 + (4864)*R)*T + (2432 + (2432)*R)*T^2)*V^2 + (512 + (512)*R + (1024 + (1024)*R)*T + (512 + (512)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 1 0 := by
  have identity : evenChartExpr 1 0 Z V T R 1 1 0 =
      (8498338 + (7851996)*R + (17401798 + (16756736)*R)*T + (8902656 + (8902656)*R)*T^2 + (59182288 + (57888768)*R + (119171040 + (117878784)*R)*T + (59987968 + (59987968)*R)*T^2)*V + (92626944 + (91979776)*R + (185655296 + (185008128)*R)*T + (93028352 + (93028352)*R)*T^2)*V^2 + (41943040 + (41943040)*R + (83886080 + (83886080)*R)*T + (41943040 + (41943040)*R)*T^2)*V^3 + (6866711 + (6557692)*R + (13949433 + (13640704)*R)*T + (7082496 + (7082496)*R)*T^2 + (41111324 + (40493056)*R + (82653692 + (82035712)*R)*T + (41542144 + (41542144)*R)*T^2)*V + (61507584 + (61198336)*R + (123230208 + (122920960)*R)*T + (61722624 + (61722624)*R)*T^2)*V^2 + (27262976 + (27262976)*R + (54525952 + (54525952)*R)*T + (27262976 + (27262976)*R)*T^2)*V^3)*Z + (2105776 + (2050624)*R + (4254752 + (4199616)*R)*T + (2148960 + (2148960)*R)*T^2 + (11309872 + (11199552)*R + (22706080 + (22595776)*R)*T + (11396192 + (11396192)*R)*T^2)*V + (16281984 + (16226816)*R + (32607104 + (32551936)*R)*T + (16325120 + (16325120)*R)*T^2)*V^2 + (7077888 + (7077888)*R + (14155776 + (14155776)*R)*T + (7077888 + (7077888)*R)*T^2)*V^3)*Z^2 + (311920 + (307568)*R + (627680 + (623328)*R)*T + (315760 + (315760)*R)*T^2 + (1542960 + (1534256)*R + (3093600 + (3084896)*R)*T + (1550640 + (1550640)*R)*T^2)*V + (2148544 + (2144192)*R + (4300928 + (4296576)*R)*T + (2152384 + (2152384)*R)*T^2)*V^2 + (917504 + (917504)*R + (1835008 + (1835008)*R)*T + (917504 + (917504)*R)*T^2)*V^3)*Z^3 + (22544 + (22416)*R + (45216 + (45088)*R)*T + (22672 + (22672)*R)*T^2 + (104528 + (104272)*R + (209312 + (209056)*R)*T + (104784 + (104784)*R)*T^2)*V + (141376 + (141248)*R + (282880 + (282752)*R)*T + (141504 + (141504)*R)*T^2)*V^2 + (59392 + (59392)*R + (118784 + (118784)*R)*T + (59392 + (59392)*R)*T^2)*V^3)*Z^4 + (640 + (640)*R + (1280 + (1280)*R)*T + (640 + (640)*R)*T^2 + (2816 + (2816)*R + (5632 + (5632)*R)*T + (2816 + (2816)*R)*T^2)*V + (3712 + (3712)*R + (7424 + (7424)*R)*T + (3712 + (3712)*R)*T^2)*V^2 + (1536 + (1536)*R + (3072 + (3072)*R)*T + (1536 + (1536)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 0 1 := by
  have identity : evenChartExpr 1 0 Z V T R 1 0 1 =
      (7596330 + (8138788)*R + (14683450 + (15224832)*R)*T + (7088128 + (7088128)*R)*T^2 + (14952704 + (16035840)*R + (28888352 + (29970432)*R)*T + (13936640 + (13936640)*R)*T^2)*V + (7356416 + (7897088)*R + (14204928 + (14745600)*R)*T + (6848512 + (6848512)*R)*T^2)*V^2 + (4576837 + (4845572)*R + (8897351 + (9165824)*R)*T + (4320768 + (4320768)*R)*T^2 + (9039424 + (9576448)*R + (17566532 + (18103296)*R)*T + (8527360 + (8527360)*R)*T^2)*V + (4462592 + (4730880)*R + (8669184 + (8937472)*R)*T + (4206592 + (4206592)*R)*T^2)*V^2)*Z + (1102500 + (1152448)*R + (2156596 + (2206528)*R)*T + (1054112 + (1054112)*R)*T^2 + (2184612 + (2284480)*R + (4272436 + (4372288)*R)*T + (2087840 + (2087840)*R)*T^2)*V + (1082112 + (1132032)*R + (2115840 + (2165760)*R)*T + (1033728 + (1033728)*R)*T^2)*V^2)*Z^2 + (132720 + (136848)*R + (261376 + (265504)*R)*T + (128656 + (128656)*R)*T^2 + (263824 + (272080)*R + (519520 + (527776)*R)*T + (255696 + (255696)*R)*T^2)*V + (131104 + (135232)*R + (258144 + (262272)*R)*T + (127040 + (127040)*R)*T^2)*V^2)*Z^3 + (7984 + (8112)*R + (15840 + (15968)*R)*T + (7856 + (7856)*R)*T^2 + (15920 + (16176)*R + (31584 + (31840)*R)*T + (15664 + (15664)*R)*T^2)*V + (7936 + (8064)*R + (15744 + (15872)*R)*T + (7808 + (7808)*R)*T^2)*V^2)*Z^4 + (192 + (192)*R + (384 + (384)*R)*T + (192 + (192)*R)*T^2 + (384 + (384)*R + (768 + (768)*R)*T + (384 + (384)*R)*T^2)*V + (192 + (192)*R + (384 + (384)*R)*T + (192 + (192)*R)*T^2)*V^2)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 1 1 := by
  have identity : evenChartExpr 1 0 Z V T R 1 1 1 =
      (1841878 + (1298396)*R + (4191942 + (3649536)*R)*T + (2349056 + (2349056)*R)*T^2 + (3922688 + (2838528)*R + (8861408 + (7778304)*R)*T + (4937728 + (4937728)*R)*T^2)*V + (2080768 + (1540096)*R + (4669440 + (4128768)*R)*T + (2588672 + (2588672)*R)*T^2)*V^2 + (1190587 + (921596)*R + (2637241 + (2368512)*R)*T + (1446400 + (1446400)*R)*T^2 + (2495168 + (1957888)*R + (5502396 + (4965376)*R)*T + (3006976 + (3006976)*R)*T^2)*V + (1304576 + (1036288)*R + (2865152 + (2596864)*R)*T + (1560576 + (1560576)*R)*T^2)*V^2)*Z + (306540 + (256576)*R + (661468 + (611520)*R)*T + (354912 + (354912)*R)*T^2 + (633452 + (533568)*R + (1363676 + (1263808)*R)*T + (730208 + (730208)*R)*T^2)*V + (326912 + (276992)*R + (702208 + (652288)*R)*T + (375296 + (375296)*R)*T^2)*V^2)*Z^2 + (39312 + (35184)*R + (82688 + (78560)*R)*T + (43376 + (43376)*R)*T^2 + (80240 + (71984)*R + (168608 + (160352)*R)*T + (88368 + (88368)*R)*T^2)*V + (40928 + (36800)*R + (85920 + (81792)*R)*T + (44992 + (44992)*R)*T^2)*V^2)*Z^3 + (2512 + (2384)*R + (5152 + (5024)*R)*T + (2640 + (2640)*R)*T^2 + (5072 + (4816)*R + (10400 + (10144)*R)*T + (5328 + (5328)*R)*T^2)*V + (2560 + (2432)*R + (5248 + (5120)*R)*T + (2688 + (2688)*R)*T^2)*V^2)*Z^4 + (64 + (64)*R + (128 + (128)*R)*T + (64 + (64)*R)*T^2 + (128 + (128)*R + (256 + (256)*R)*T + (128 + (128)*R)*T^2)*V + (64 + (64)*R + (128 + (128)*R)*T + (64 + (64)*R)*T^2)*V^2)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 0 2 := by
  have identity : evenChartExpr 1 0 Z V T R 1 0 2 =
      (238140 + (500808)*R + (234496 + (496640)*R)*T + (500224 + (1025024)*R + (496640 + (1020928)*R)*T)*V + (262144 + (524288)*R + (262144 + (524288)*R)*T)*V^2 + (121991 + (253192)*R + (121088 + (252160)*R)*T + (253056 + (515328)*R + (252160 + (514304)*R)*T)*V + (131072 + (262144)*R + (131072 + (262144)*R)*T)*V^2)*Z + (23432 + (48016)*R + (23376 + (47952)*R)*T + (48008 + (97168)*R + (47952 + (97104)*R)*T)*V + (24576 + (49152)*R + (24576 + (49152)*R)*T)*V^2)*Z^2 + (2000 + (4048)*R + (2000 + (4048)*R)*T + (4048 + (8144)*R + (4048 + (8144)*R)*T)*V + (2048 + (4096)*R + (2048 + (4096)*R)*T)*V^2)*Z^3 + (64 + (128)*R + (64 + (128)*R)*T + (128 + (256)*R + (128 + (256)*R)*T)*V + (64 + (128)*R + (64 + (128)*R)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 1 2 := by
  have identity : evenChartExpr 1 0 Z V T R 1 1 2 =
      (295364 + (32696)*R + (299008 + (36864)*R)*T + (557568 + (32768)*R + (561152 + (36864)*R)*T)*V + (262144 + (262144)*T)*V^2 + (143481 + (12280)*R + (144384 + (13312)*R)*T + (274560 + (12288)*R + (275456 + (13312)*R)*T)*V + (131072 + (131072)*T)*V^2)*Z + (26120 + (1536)*R + (26176 + (1600)*R)*T + (50696 + (1536)*R + (50752 + (1600)*R)*T)*V + (24576 + (24576)*T)*V^2)*Z^2 + (2112 + (64)*R + (2112 + (64)*R)*T + (4160 + (64)*R + (4160 + (64)*R)*T)*V + (2048 + (2048)*T)*V^2)*Z^3 + (64 + (64)*T + (128 + (128)*T)*V + (64 + (64)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 0 3 := by
  have identity : evenChartExpr 1 0 Z V T R 1 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_0_1_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 0 Z V T R 1 1 3 := by
  have identity : evenChartExpr 1 0 Z V T R 1 1 3 =
      (262664 + (262144)*T + (524800 + (524288)*T)*V + (262144 + (262144)*T)*V^2 + (131201 + (131072)*T + (262272 + (262144)*T)*V + (131072 + (131072)*T)*V^2)*Z + (24584 + (24576)*T + (49160 + (49152)*T)*V + (24576 + (24576)*T)*V^2)*Z^2 + (2048 + (2048)*T + (4096 + (4096)*T)*V + (2048 + (2048)*T)*V^2)*Z^3 + (64 + (64)*T + (128 + (128)*T)*V + (64 + (64)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 0 0 := by
  have identity : evenChartExpr 1 1 Z V T R 0 0 0 =
      (20115064 + (20406416)*R + (40044602 + (40335360)*R)*T + (19933184 + (19933184)*R)*T^2 + (52624872 + (53207040)*R + (104831008 + (105412608)*R)*T + (52209664 + (52209664)*R)*T^2)*V + (45092864 + (45383680)*R + (89952256 + (90243072)*R)*T + (44859392 + (44859392)*R)*T^2)*V^2 + (12582912 + (12582912)*R + (25165824 + (25165824)*R)*T + (12582912 + (12582912)*R)*T^2)*V^3 + (11892621 + (12035088)*R + (23683591 + (23825920)*R)*T + (11791872 + (11791872)*R)*T^2 + (31030140 + (31314944)*R + (61838852 + (62123520)*R)*T + (30809600 + (30809600)*R)*T^2)*V + (26477568 + (26619904)*R + (52835328 + (52977664)*R)*T + (26357760 + (26357760)*R)*T^2)*V^2 + (7340032 + (7340032)*R + (14680064 + (14680064)*R)*T + (7340032 + (7340032)*R)*T^2)*V^3)*Z + (2803384 + (2829440)*R + (5585952 + (5612000)*R)*T + (2782624 + (2782624)*R)*T^2 + (7292664 + (7344768)*R + (14541408 + (14593504)*R)*T + (7248800 + (7248800)*R)*T^2)*V + (6193216 + (6219264)*R + (12363328 + (12389376)*R)*T + (6170112 + (6170112)*R)*T^2)*V^2 + (1703936 + (1703936)*R + (3407872 + (3407872)*R)*T + (1703936 + (1703936)*R)*T^2)*V^3)*Z^2 + (329200 + (331312)*R + (656512 + (658624)*R)*T + (327312 + (327312)*R)*T^2 + (853488 + (857712)*R + (1703104 + (1707328)*R)*T + (849616 + (849616)*R)*T^2)*V + (720896 + (723008)*R + (1439808 + (1441920)*R)*T + (718912 + (718912)*R)*T^2)*V^2 + (196608 + (196608)*R + (393216 + (393216)*R)*T + (196608 + (196608)*R)*T^2)*V^3)*Z^3 + (19248 + (19312)*R + (38432 + (38496)*R)*T + (19184 + (19184)*R)*T^2 + (49712 + (49840)*R + (99296 + (99424)*R)*T + (49584 + (49584)*R)*T^2)*V + (41728 + (41792)*R + (83392 + (83456)*R)*T + (41664 + (41664)*R)*T^2)*V^2 + (11264 + (11264)*R + (22528 + (22528)*R)*T + (11264 + (11264)*R)*T^2)*V^3)*Z^4 + (448 + (448)*R + (896 + (896)*R)*T + (448 + (448)*R)*T^2 + (1152 + (1152)*R + (2304 + (2304)*R)*T + (1152 + (1152)*R)*T^2)*V + (960 + (960)*R + (1920 + (1920)*R)*T + (960 + (960)*R)*T^2)*V^2 + (256 + (256)*R + (512 + (512)*R)*T + (256 + (256)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 1 0 := by
  have identity : evenChartExpr 1 1 Z V T R 0 1 0 =
      (13472200 + (13148016)*R + (27097030 + (26773504)*R)*T + (13621248 + (13621248)*R)*T^2 + (48104024 + (47456256)*R + (96561120 + (95913984)*R)*T + (48453632 + (48453632)*R)*T^2)*V + (55603200 + (55279616)*R + (111407104 + (111083520)*R)*T + (55803904 + (55803904)*R)*T^2)*V^2 + (20971520 + (20971520)*R + (41943040 + (41943040)*R)*T + (20971520 + (20971520)*R)*T^2)*V^3 + (9091195 + (8936432)*R + (18271737 + (18117120)*R)*T + (9179648 + (9179648)*R)*T^2 + (31909004 + (31599616)*R + (64014844 + (63705600)*R)*T + (32104960 + (32104960)*R)*T^2)*V + (36449280 + (36294656)*R + (73006080 + (72851456)*R)*T + (36556800 + (36556800)*R)*T^2)*V^2 + (13631488 + (13631488)*R + (27262976 + (27262976)*R)*T + (13631488 + (13631488)*R)*T^2)*V^3)*Z + (2441032 + (2413440)*R + (4901344 + (4873760)*R)*T + (2460256 + (2460256)*R)*T^2 + (8439048 + (8383872)*R + (16918944 + (16863776)*R)*T + (8479840 + (8479840)*R)*T^2)*V + (9536960 + (9509376)*R + (19095488 + (19067904)*R)*T + (9558528 + (9558528)*R)*T^2)*V^2 + (3538944 + (3538944)*R + (7077888 + (7077888)*R)*T + (3538944 + (3538944)*R)*T^2)*V^3)*Z^2 + (326224 + (324048)*R + (654272 + (652096)*R)*T + (328048 + (328048)*R)*T^2 + (1112720 + (1108368)*R + (2229184 + (2224832)*R)*T + (1116464 + (1116464)*R)*T^2)*V + (1245248 + (1243072)*R + (2492416 + (2490240)*R)*T + (1247168 + (1247168)*R)*T^2)*V^2 + (458752 + (458752)*R + (917504 + (917504)*R)*T + (458752 + (458752)*R)*T^2)*V^3)*Z^3 + (21712 + (21648)*R + (43488 + (43424)*R)*T + (21776 + (21776)*R)*T^2 + (73168 + (73040)*R + (146464 + (146336)*R)*T + (73296 + (73296)*R)*T^2)*V + (81152 + (81088)*R + (162368 + (162304)*R)*T + (81216 + (81216)*R)*T^2)*V^2 + (29696 + (29696)*R + (59392 + (59392)*R)*T + (29696 + (29696)*R)*T^2)*V^3)*Z^4 + (576 + (576)*R + (1152 + (1152)*R)*T + (576 + (576)*R)*T^2 + (1920 + (1920)*R + (3840 + (3840)*R)*T + (1920 + (1920)*R)*T^2)*V + (2112 + (2112)*R + (4224 + (4224)*R)*T + (2112 + (2112)*R)*T^2)*V^2 + (768 + (768)*R + (1536 + (1536)*R)*T + (768 + (768)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 0 1 := by
  have identity : evenChartExpr 1 1 Z V T R 0 0 1 =
      (474016 + (745616)*R + (742714 + (1013760)*R)*T + (272384 + (272384)*R)*T^2 + (760592 + (1302528)*R + (1062176 + (1603584)*R)*T + (305152 + (305152)*R)*T^2)*V + (286720 + (557056)*R + (319488 + (589824)*R)*T + (32768 + (32768)*R)*T^2)*V^2 + (235219 + (369680)*R + (360775 + (495104)*R)*T + (126464 + (126464)*R)*T^2 + (375490 + (644096)*R + (513348 + (781824)*R)*T + (138752 + (138752)*R)*T^2)*V + (140288 + (274432)*R + (152576 + (286720)*R)*T + (12288 + (12288)*R)*T^2)*V^2)*Z + (43756 + (68736)*R + (65620 + (90592)*R)*T + (21920 + (21920)*R)*T^2 + (69484 + (119424)*R + (92884 + (142816)*R)*T + (23456 + (23456)*R)*T^2)*V + (25728 + (50688)*R + (27264 + (52224)*R)*T + (1536 + (1536)*R)*T^2)*V^2)*Z^2 + (3616 + (5680)*R + (5296 + (7360)*R)*T + (1680 + (1680)*R)*T^2 + (5712 + (9840)*R + (7456 + (11584)*R)*T + (1744 + (1744)*R)*T^2)*V + (2096 + (4160)*R + (2160 + (4224)*R)*T + (64 + (64)*R)*T^2)*V^2)*Z^3 + (112 + (176)*R + (160 + (224)*R)*T + (48 + (48)*R)*T^2 + (176 + (304)*R + (224 + (352)*R)*T + (48 + (48)*R)*T^2)*V + (64 + (128)*R + (64 + (128)*R)*T)*V^2)*Z^4) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 1 1 := by
  have identity : evenChartExpr 1 1 Z V T R 0 1 1 =
      (8964192 + (8691568)*R + (18132678 + (17860608)*R)*T + (9164800 + (9164800)*R)*T^2 + (18114800 + (17571840)*R + (36687584 + (36145152)*R)*T + (18569216 + (18569216)*R)*T^2)*V + (9150464 + (8880128)*R + (18554880 + (18284544)*R)*T + (9404416 + (9404416)*R)*T^2)*V^2 + (5532205 + (5397488)*R + (11173817 + (11039232)*R)*T + (5640704 + (5640704)*R)*T^2 + (11159102 + (10890240)*R + (22555580 + (22286848)*R)*T + (11395584 + (11395584)*R)*T^2)*V + (5626880 + (5492736)*R + (11381760 + (11247616)*R)*T + (5754880 + (5754880)*R)*T^2)*V^2)*Z + (1365284 + (1340288)*R + (2752444 + (2727456)*R)*T + (1387104 + (1387104)*R)*T^2 + (2748580 + (2698624)*R + (5543228 + (5493280)*R)*T + (2794592 + (2794592)*R)*T^2)*V + (1383296 + (1358336)*R + (2790784 + (2765824)*R)*T + (1407488 + (1407488)*R)*T^2)*V^2)*Z^2 + (168416 + (166352)*R + (338768 + (336704)*R)*T + (170352 + (170352)*R)*T^2 + (338352 + (334224)*R + (680672 + (676544)*R)*T + (342320 + (342320)*R)*T^2)*V + (169936 + (167872)*R + (341904 + (339840)*R)*T + (171968 + (171968)*R)*T^2)*V^2)*Z^3 + (10384 + (10320)*R + (20832 + (20768)*R)*T + (10448 + (10448)*R)*T^2 + (20816 + (20688)*R + (41760 + (41632)*R)*T + (20944 + (20944)*R)*T^2)*V + (10432 + (10368)*R + (20928 + (20864)*R)*T + (10496 + (10496)*R)*T^2)*V^2)*Z^4 + (256 + (256)*R + (512 + (512)*R)*T + (256 + (256)*R)*T^2 + (512 + (512)*R + (1024 + (1024)*R)*T + (512 + (512)*R)*T^2)*V + (256 + (256)*R + (512 + (512)*R)*T + (256 + (256)*R)*T^2)*V^2)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 0 2 := by
  have identity : evenChartExpr 1 1 Z V T R 0 0 2 =
      (105276 + (236616)*R + (103424 + (234496)*R)*T + (236288 + (498688)*R + (234496 + (496640)*R)*T)*V + (131072 + (262144)*R + (131072 + (262144)*R)*T)*V^2 + (56007 + (121608)*R + (55552 + (121088)*R)*T + (121536 + (252672)*R + (121088 + (252160)*R)*T)*V + (65536 + (131072)*R + (65536 + (131072)*R)*T)*V^2)*Z + (11116 + (23408)*R + (11088 + (23376)*R)*T + (23404 + (47984)*R + (23376 + (47952)*R)*T)*V + (12288 + (24576)*R + (12288 + (24576)*R)*T)*V^2)*Z^2 + (976 + (2000)*R + (976 + (2000)*R)*T + (2000 + (4048)*R + (2000 + (4048)*R)*T)*V + (1024 + (2048)*R + (1024 + (2048)*R)*T)*V^2)*Z^3 + (32 + (64)*R + (32 + (64)*R)*T + (64 + (128)*R + (64 + (128)*R)*T)*V + (32 + (64)*R + (32 + (64)*R)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 1 2 := by
  have identity : evenChartExpr 1 1 Z V T R 0 1 2 =
      (166084 + (34744)*R + (167936 + (36864)*R)*T + (297216 + (34816)*R + (299008 + (36864)*R)*T)*V + (131072 + (131072)*T)*V^2 + (78393 + (12792)*R + (78848 + (13312)*R)*T + (143936 + (12800)*R + (144384 + (13312)*R)*T)*V + (65536 + (65536)*T)*V^2)*Z + (13860 + (1568)*R + (13888 + (1600)*R)*T + (26148 + (1568)*R + (26176 + (1600)*R)*T)*V + (12288 + (12288)*T)*V^2)*Z^2 + (1088 + (64)*R + (1088 + (64)*R)*T + (2112 + (64)*R + (2112 + (64)*R)*T)*V + (1024 + (1024)*T)*V^2)*Z^3 + (32 + (32)*T + (64 + (64)*T)*V + (32 + (32)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 0 3 := by
  have identity : evenChartExpr 1 1 Z V T R 0 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_0_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 0 1 3 := by
  have identity : evenChartExpr 1 1 Z V T R 0 1 3 =
      (131336 + (131072)*T + (262400 + (262144)*T)*V + (131072 + (131072)*T)*V^2 + (65601 + (65536)*T + (131136 + (131072)*T)*V + (65536 + (65536)*T)*V^2)*Z + (12292 + (12288)*T + (24580 + (24576)*T)*V + (12288 + (12288)*T)*V^2)*Z^2 + (1024 + (1024)*T + (2048 + (2048)*T)*V + (1024 + (1024)*T)*V^2)*Z^3 + (32 + (32)*T + (64 + (64)*T)*V + (32 + (32)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_0_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 0 0 := by
  have identity : evenChartExpr 1 1 Z V T R 1 0 0 =
      (58627140 + (59207824)*R + (116826170 + (117405696)*R)*T + (58206208 + (58206208)*R)*T^2 + (142226352 + (143388672)*R + (283557920 + (284719104)*R)*T + (141338624 + (141338624)*R)*T^2)*V + (108765184 + (109346816)*R + (217063424 + (217645056)*R)*T + (108298240 + (108298240)*R)*T^2)*V^2 + (25165824 + (25165824)*R + (50331648 + (50331648)*R)*T + (25165824 + (25165824)*R)*T^2)*V^3 + (35082501 + (35366928)*R + (69941255 + (70225408)*R)*T + (34860544 + (34860544)*R)*T^2 + (84748532 + (85317632)*R + (169033732 + (169602560)*R)*T + (84286976 + (84286976)*R)*T^2)*V + (64346112 + (64630784)*R + (128452608 + (128737280)*R)*T + (64106496 + (64106496)*R)*T^2)*V^2 + (14680064 + (14680064)*R + (29360128 + (29360128)*R)*T + (14680064 + (14680064)*R)*T^2)*V^3)*Z + (8380752 + (8432832)*R + (16717440 + (16769504)*R)*T + (8336800 + (8336800)*R)*T^2 + (20151248 + (20255424)*R + (40212224 + (40316384)*R)*T + (20061088 + (20061088)*R)*T^2)*V + (15178368 + (15230464)*R + (30310528 + (30362624)*R)*T + (15132160 + (15132160)*R)*T^2)*V^2 + (3407872 + (3407872)*R + (6815744 + (6815744)*R)*T + (3407872 + (3407872)*R)*T^2)*V^3)*Z^2 + (998832 + (1003056)*R + (1993792 + (1998016)*R)*T + (994960 + (994960)*R)*T^2 + (2389360 + (2397808)*R + (4770880 + (4779328)*R)*T + (2381520 + (2381520)*R)*T^2)*V + (1783744 + (1787968)*R + (3563520 + (3567744)*R)*T + (1779776 + (1779776)*R)*T^2)*V^2 + (393216 + (393216)*R + (786432 + (786432)*R)*T + (393216 + (393216)*R)*T^2)*V^3)*Z^3 + (59376 + (59504)*R + (118624 + (118752)*R)*T + (59248 + (59248)*R)*T^2 + (141232 + (141488)*R + (282208 + (282464)*R)*T + (140976 + (140976)*R)*T^2)*V + (104384 + (104512)*R + (208640 + (208768)*R)*T + (104256 + (104256)*R)*T^2)*V^2 + (22528 + (22528)*R + (45056 + (45056)*R)*T + (22528 + (22528)*R)*T^2)*V^3)*Z^4 + (1408 + (1408)*R + (2816 + (2816)*R)*T + (1408 + (1408)*R)*T^2 + (3328 + (3328)*R + (6656 + (6656)*R)*T + (3328 + (3328)*R)*T^2)*V + (2432 + (2432)*R + (4864 + (4864)*R)*T + (2432 + (2432)*R)*T^2)*V^2 + (512 + (512)*R + (1024 + (1024)*R)*T + (512 + (512)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_1_0 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 1 0 := by
  have identity : evenChartExpr 1 1 Z V T R 1 1 0 =
      (8547388 + (7901040)*R + (17457094 + (16812032)*R)*T + (8902656 + (8902656)*R)*T^2 + (59231440 + (57937920)*R + (119226336 + (117934080)*R)*T + (59987968 + (59987968)*R)*T^2)*V + (92626944 + (91979776)*R + (185655296 + (185008128)*R)*T + (93028352 + (93028352)*R)*T^2)*V^2 + (41943040 + (41943040)*R + (83886080 + (83886080)*R)*T + (41943040 + (41943040)*R)*T^2)*V^3 + (6885131 + (6576112)*R + (13969401 + (13660672)*R)*T + (7082496 + (7082496)*R)*T^2 + (41129756 + (40511488)*R + (82673660 + (82055680)*R)*T + (41542144 + (41542144)*R)*T^2)*V + (61507584 + (61198336)*R + (123230208 + (122920960)*R)*T + (61722624 + (61722624)*R)*T^2)*V^2 + (27262976 + (27262976)*R + (54525952 + (54525952)*R)*T + (27262976 + (27262976)*R)*T^2)*V^3)*Z + (2108080 + (2052928)*R + (4257152 + (4202016)*R)*T + (2148960 + (2148960)*R)*T^2 + (11312176 + (11201856)*R + (22708480 + (22598176)*R)*T + (11396192 + (11396192)*R)*T^2)*V + (16281984 + (16226816)*R + (32607104 + (32551936)*R)*T + (16325120 + (16325120)*R)*T^2)*V^2 + (7077888 + (7077888)*R + (14155776 + (14155776)*R)*T + (7077888 + (7077888)*R)*T^2)*V^3)*Z^2 + (312016 + (307664)*R + (627776 + (623424)*R)*T + (315760 + (315760)*R)*T^2 + (1543056 + (1534352)*R + (3093696 + (3084992)*R)*T + (1550640 + (1550640)*R)*T^2)*V + (2148544 + (2144192)*R + (4300928 + (4296576)*R)*T + (2152384 + (2152384)*R)*T^2)*V^2 + (917504 + (917504)*R + (1835008 + (1835008)*R)*T + (917504 + (917504)*R)*T^2)*V^3)*Z^3 + (22544 + (22416)*R + (45216 + (45088)*R)*T + (22672 + (22672)*R)*T^2 + (104528 + (104272)*R + (209312 + (209056)*R)*T + (104784 + (104784)*R)*T^2)*V + (141376 + (141248)*R + (282880 + (282752)*R)*T + (141504 + (141504)*R)*T^2)*V^2 + (59392 + (59392)*R + (118784 + (118784)*R)*T + (59392 + (59392)*R)*T^2)*V^3)*Z^4 + (640 + (640)*R + (1280 + (1280)*R)*T + (640 + (640)*R)*T^2 + (2816 + (2816)*R + (5632 + (5632)*R)*T + (2816 + (2816)*R)*T^2)*V + (3712 + (3712)*R + (7424 + (7424)*R)*T + (3712 + (3712)*R)*T^2)*V^2 + (1536 + (1536)*R + (3072 + (3072)*R)*T + (1536 + (1536)*R)*T^2)*V^3)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_0_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 0 1 := by
  have identity : evenChartExpr 1 1 Z V T R 1 0 1 =
      (7547280 + (8089744)*R + (14628154 + (15169536)*R)*T + (7088128 + (7088128)*R)*T^2 + (14903552 + (15986688)*R + (28833056 + (29915136)*R)*T + (13936640 + (13936640)*R)*T^2)*V + (7356416 + (7897088)*R + (14204928 + (14745600)*R)*T + (6848512 + (6848512)*R)*T^2)*V^2 + (4558417 + (4827152)*R + (8877383 + (9145856)*R)*T + (4320768 + (4320768)*R)*T^2 + (9020992 + (9558016)*R + (17546564 + (18083328)*R)*T + (8527360 + (8527360)*R)*T^2)*V + (4462592 + (4730880)*R + (8669184 + (8937472)*R)*T + (4206592 + (4206592)*R)*T^2)*V^2)*Z + (1100196 + (1150144)*R + (2154196 + (2204128)*R)*T + (1054112 + (1054112)*R)*T^2 + (2182308 + (2282176)*R + (4270036 + (4369888)*R)*T + (2087840 + (2087840)*R)*T^2)*V + (1082112 + (1132032)*R + (2115840 + (2165760)*R)*T + (1033728 + (1033728)*R)*T^2)*V^2)*Z^2 + (132624 + (136752)*R + (261280 + (265408)*R)*T + (128656 + (128656)*R)*T^2 + (263728 + (271984)*R + (519424 + (527680)*R)*T + (255696 + (255696)*R)*T^2)*V + (131104 + (135232)*R + (258144 + (262272)*R)*T + (127040 + (127040)*R)*T^2)*V^2)*Z^3 + (7984 + (8112)*R + (15840 + (15968)*R)*T + (7856 + (7856)*R)*T^2 + (15920 + (16176)*R + (31584 + (31840)*R)*T + (15664 + (15664)*R)*T^2)*V + (7936 + (8064)*R + (15744 + (15872)*R)*T + (7808 + (7808)*R)*T^2)*V^2)*Z^4 + (192 + (192)*R + (384 + (384)*R)*T + (192 + (192)*R)*T^2 + (384 + (384)*R + (768 + (768)*R)*T + (384 + (384)*R)*T^2)*V + (192 + (192)*R + (384 + (384)*R)*T + (192 + (192)*R)*T^2)*V^2)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_1_1 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 1 1 := by
  have identity : evenChartExpr 1 1 Z V T R 1 1 1 =
      (1890928 + (1347440)*R + (4247238 + (3704832)*R)*T + (2349056 + (2349056)*R)*T^2 + (3971840 + (2887680)*R + (8916704 + (7833600)*R)*T + (4937728 + (4937728)*R)*T^2)*V + (2080768 + (1540096)*R + (4669440 + (4128768)*R)*T + (2588672 + (2588672)*R)*T^2)*V^2 + (1209007 + (940016)*R + (2657209 + (2388480)*R)*T + (1446400 + (1446400)*R)*T^2 + (2513600 + (1976320)*R + (5522364 + (4985344)*R)*T + (3006976 + (3006976)*R)*T^2)*V + (1304576 + (1036288)*R + (2865152 + (2596864)*R)*T + (1560576 + (1560576)*R)*T^2)*V^2)*Z + (308844 + (258880)*R + (663868 + (613920)*R)*T + (354912 + (354912)*R)*T^2 + (635756 + (535872)*R + (1366076 + (1266208)*R)*T + (730208 + (730208)*R)*T^2)*V + (326912 + (276992)*R + (702208 + (652288)*R)*T + (375296 + (375296)*R)*T^2)*V^2)*Z^2 + (39408 + (35280)*R + (82784 + (78656)*R)*T + (43376 + (43376)*R)*T^2 + (80336 + (72080)*R + (168704 + (160448)*R)*T + (88368 + (88368)*R)*T^2)*V + (40928 + (36800)*R + (85920 + (81792)*R)*T + (44992 + (44992)*R)*T^2)*V^2)*Z^3 + (2512 + (2384)*R + (5152 + (5024)*R)*T + (2640 + (2640)*R)*T^2 + (5072 + (4816)*R + (10400 + (10144)*R)*T + (5328 + (5328)*R)*T^2)*V + (2560 + (2432)*R + (5248 + (5120)*R)*T + (2688 + (2688)*R)*T^2)*V^2)*Z^4 + (64 + (64)*R + (128 + (128)*R)*T + (64 + (64)*R)*T^2 + (128 + (128)*R + (256 + (256)*R)*T + (128 + (128)*R)*T^2)*V + (64 + (64)*R + (128 + (128)*R)*T + (64 + (64)*R)*T^2)*V^2)*Z^5) / 4 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_0_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 0 2 := by
  have identity : evenChartExpr 1 1 Z V T R 1 0 2 =
      (238140 + (500808)*R + (234496 + (496640)*R)*T + (500224 + (1025024)*R + (496640 + (1020928)*R)*T)*V + (262144 + (524288)*R + (262144 + (524288)*R)*T)*V^2 + (121991 + (253192)*R + (121088 + (252160)*R)*T + (253056 + (515328)*R + (252160 + (514304)*R)*T)*V + (131072 + (262144)*R + (131072 + (262144)*R)*T)*V^2)*Z + (23432 + (48016)*R + (23376 + (47952)*R)*T + (48008 + (97168)*R + (47952 + (97104)*R)*T)*V + (24576 + (49152)*R + (24576 + (49152)*R)*T)*V^2)*Z^2 + (2000 + (4048)*R + (2000 + (4048)*R)*T + (4048 + (8144)*R + (4048 + (8144)*R)*T)*V + (2048 + (4096)*R + (2048 + (4096)*R)*T)*V^2)*Z^3 + (64 + (128)*R + (64 + (128)*R)*T + (128 + (256)*R + (128 + (256)*R)*T)*V + (64 + (128)*R + (64 + (128)*R)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_1_2 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 1 2 := by
  have identity : evenChartExpr 1 1 Z V T R 1 1 2 =
      (295364 + (32696)*R + (299008 + (36864)*R)*T + (557568 + (32768)*R + (561152 + (36864)*R)*T)*V + (262144 + (262144)*T)*V^2 + (143481 + (12280)*R + (144384 + (13312)*R)*T + (274560 + (12288)*R + (275456 + (13312)*R)*T)*V + (131072 + (131072)*T)*V^2)*Z + (26120 + (1536)*R + (26176 + (1600)*R)*T + (50696 + (1536)*R + (50752 + (1600)*R)*T)*V + (24576 + (24576)*T)*V^2)*Z^2 + (2112 + (64)*R + (2112 + (64)*R)*T + (4160 + (64)*R + (4160 + (64)*R)*T)*V + (2048 + (2048)*T)*V^2)*Z^3 + (64 + (64)*T + (128 + (128)*T)*V + (64 + (64)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_0_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 0 3 := by
  have identity : evenChartExpr 1 1 Z V T R 1 0 3 =
      (0) / 1 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_1_1_1_1_3 (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R) :
    0 ≤ evenChartExpr 1 1 Z V T R 1 1 3 := by
  have identity : evenChartExpr 1 1 Z V T R 1 1 3 =
      (262664 + (262144)*T + (524800 + (524288)*T)*V + (262144 + (262144)*T)*V^2 + (131201 + (131072)*T + (262272 + (262144)*T)*V + (131072 + (131072)*T)*V^2)*Z + (24584 + (24576)*T + (49160 + (49152)*T)*V + (24576 + (24576)*T)*V^2)*Z^2 + (2048 + (2048)*T + (4096 + (4096)*T)*V + (2048 + (2048)*T)*V^2)*Z^3 + (64 + (64)*T + (128 + (128)*T)*V + (64 + (64)*T)*V^2)*Z^4) / 2 := by
    norm_num [evenChartExpr,qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ]
    <;> ring
  rw [identity]
  positivity
private theorem chart0_nonnegative (mode : Fin 2) (endpoint : Fin 2)
    (Z V T R : ℚ) (hZ : 0 ≤ Z) (hV : 0 ≤ V) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (row kind bank : Fin 4) (hr : row.val < 2) (hk : kind.val < 2) :
    0 ≤ evenChartExpr mode endpoint Z V T R row kind bank := by
  fin_cases mode <;> fin_cases endpoint <;> fin_cases row <;> fin_cases kind <;> fin_cases bank
  all_goals first | omega | skip
  all_goals first
    | exact chart0_0_0_0_0_0 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_1_0 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_0_1 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_1_1 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_0_2 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_1_2 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_0_3 Z V T R hZ hV hT hR
    | exact chart0_0_0_0_1_3 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_0_0 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_1_0 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_0_1 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_1_1 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_0_2 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_1_2 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_0_3 Z V T R hZ hV hT hR
    | exact chart0_0_0_1_1_3 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_0_0 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_1_0 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_0_1 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_1_1 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_0_2 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_1_2 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_0_3 Z V T R hZ hV hT hR
    | exact chart0_0_1_0_1_3 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_0_0 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_1_0 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_0_1 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_1_1 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_0_2 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_1_2 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_0_3 Z V T R hZ hV hT hR
    | exact chart0_0_1_1_1_3 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_0_0 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_1_0 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_0_1 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_1_1 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_0_2 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_1_2 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_0_3 Z V T R hZ hV hT hR
    | exact chart0_1_0_0_1_3 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_0_0 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_1_0 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_0_1 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_1_1 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_0_2 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_1_2 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_0_3 Z V T R hZ hV hT hR
    | exact chart0_1_0_1_1_3 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_0_0 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_1_0 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_0_1 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_1_1 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_0_2 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_1_2 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_0_3 Z V T R hZ hV hT hR
    | exact chart0_1_1_0_1_3 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_0_0 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_1_0 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_0_1 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_1_1 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_0_2 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_1_2 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_0_3 Z V T R hZ hV hT hR
    | exact chart0_1_1_1_1_3 Z V T R hZ hV hT hR
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
