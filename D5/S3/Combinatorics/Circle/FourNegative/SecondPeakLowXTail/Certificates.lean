/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Certificates
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Positive polynomial certificates for the six low-X margins. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

open private qHead qNewHead qModulus qMask qMass qTerminal qPeak qSeam qSlack margin smallTZero smallTPositive largeTZero largeTPositive cap bend second from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model

-- smallt-smalle-t1/old.0.seam
private theorem cert_smallt_smalle_t1_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 0 =
      (113636 + (211904)*H + (98304)*H^2 + (325340 + (620224)*H + (294912)*H^2)*T + (310016 + (604928)*H + (294912)*H^2)*T^2 + (98304 + (196608)*H + (98304)*H^2)*T^3 + (174353 + (329984)*H + (155648)*H^2 + (504208 + (971136)*H + (466944)*H^2)*T + (485504 + (952448)*H + (466944)*H^2)*T^2 + (155648 + (311296)*H + (155648)*H^2)*T^3)*Z + (111438 + (213836)*H + (102400)*H^2 + (325246 + (632444)*H + (307200)*H^2)*T + (316208 + (623408)*H + (307200)*H^2)*T^2 + (102400 + (204800)*H + (102400)*H^2)*T^3)*Z^2 + (38002 + (73842)*H + (35840)*H^2 + (111842 + (219362)*H + (107520)*H^2)*T + (109680 + (217200)*H + (107520)*H^2)*T^2 + (35840 + (71680)*H + (35840)*H^2)*T^3)*Z^3 + (7296 + (14336)*H + (7040)*H^2 + (21632 + (42752)*H + (21120)*H^2)*T + (21376 + (42496)*H + (21120)*H^2)*T^2 + (7040 + (14080)*H + (7040)*H^2)*T^3)*Z^4 + (748 + (1484)*H + (736)*H^2 + (2232 + (4440)*H + (2208)*H^2)*T + (2220 + (4428)*H + (2208)*H^2)*T^2 + (736 + (1472)*H + (736)*H^2)*T^3)*Z^5 + (32 + (64)*H + (32)*H^2 + (96 + (192)*H + (96)*H^2)*T + (96 + (192)*H + (96)*H^2)*T^2 + (32 + (64)*H + (32)*H^2)*T^3)*Z^6) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-t1/old.1.seam
private theorem cert_smallt_smalle_t1_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 1 =
      (2794 + (2792)*H + (5478 + (5480)*H)*T + (2688 + (2688)*H)*T^2 + (3923 + (3922)*H + (7762 + (7762)*H)*T + (3840 + (3840)*H)*T^2)*Z + (2142 + (2142)*H + (4262 + (4262)*H)*T + (2120 + (2120)*H)*T^2)*Z^2 + (574 + (574)*H + (1146 + (1146)*H)*T + (572 + (572)*H)*T^2)*Z^3 + (76 + (76)*H + (152 + (152)*H)*T + (76 + (76)*H)*T^2)*Z^4 + (4 + (4)*H + (8 + (8)*H)*T + (4 + (4)*H)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-t1/old.2.seam
private theorem cert_smallt_smalle_t1_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 2 =
      (4174 + (12884)*H + (8704)*H^2 + (8256 + (25152)*H + (16896)*H^2)*T + (4096 + (12288)*H + (8192)*H^2)*T^2 + (5187 + (15812)*H + (10624)*H^2 + (10304 + (31168)*H + (20864)*H^2)*T + (5120 + (15360)*H + (10240)*H^2)*T^2)*Z + (2580 + (7796)*H + (5216)*H^2 + (5140 + (15476)*H + (10336)*H^2)*T + (2560 + (7680)*H + (5120)*H^2)*T^2)*Z^2 + (642 + (1930)*H + (1288)*H^2 + (1282 + (3850)*H + (2568)*H^2)*T + (640 + (1920)*H + (1280)*H^2)*T^2)*Z^3 + (80 + (240)*H + (160)*H^2 + (160 + (480)*H + (320)*H^2)*T + (80 + (240)*H + (160)*H^2)*T^2)*Z^4 + (4 + (12)*H + (8)*H^2 + (8 + (24)*H + (16)*H^2)*T + (4 + (12)*H + (8)*H^2)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-t1/new.0.slack
private theorem cert_smallt_smalle_t1_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 3 =
      (7000 + (72704)*H + (65536)*H^2 + (79972 + (276736)*H + (196608)*H^2)*T + (138496 + (335104)*H + (196608)*H^2)*T^2 + (65536 + (131072)*H + (65536)*H^2)*T^3 + (10863 + (92864)*H + (81920)*H^2 + (103920 + (349760)*H + (245760)*H^2)*T + (174976 + (420736)*H + (245760)*H^2)*T^2 + (81920 + (163840)*H + (81920)*H^2)*T^3)*Z + (6550 + (47520)*H + (40960)*H^2 + (54118 + (177008)*H + (122880)*H^2)*T + (88528 + (211408)*H + (122880)*H^2)*T^2 + (40960 + (81920)*H + (40960)*H^2)*T^3)*Z^2 + (1932 + (12172)*H + (10240)*H^2 + (14108 + (44828)*H + (30720)*H^2)*T + (22416 + (53136)*H + (30720)*H^2)*T^2 + (10240 + (20480)*H + (10240)*H^2)*T^3)*Z^3 + (280 + (1560)*H + (1280)*H^2 + (1840 + (5680)*H + (3840)*H^2)*T + (2840 + (6680)*H + (3840)*H^2)*T^2 + (1280 + (2560)*H + (1280)*H^2)*T^3)*Z^4 + (16 + (80)*H + (64)*H^2 + (96 + (288)*H + (192)*H^2)*T + (144 + (336)*H + (192)*H^2)*T^2 + (64 + (128)*H + (64)*H^2)*T^3)*Z^5) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-t1/new.1.slack
private theorem cert_smallt_smalle_t1_new_1_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 4 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) 1 4 =
      (4046 + (4016)*H + (8274 + (8240)*H)*T + (4224 + (4224)*H)*T^2 + (4011 + (3996)*H + (8172 + (8156)*H)*T + (4160 + (4160)*H)*T^2)*Z + (1502 + (1500)*H + (3046 + (3044)*H)*T + (1544 + (1544)*H)*T^2)*Z^2 + (252 + (252)*H + (508 + (508)*H)*T + (256 + (256)*H)*T^2)*Z^3 + (16 + (16)*H + (32 + (32)*H)*T + (16 + (16)*H)*T^2)*Z^4) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-t1/old.0.seam
private theorem cert_smallt_largee_t1_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 0 =
      (6413860 + (12705280)*R + (6291456)*R^2 + (31822876 + (63280128)*R + (31457280)*R^2)*T + (63278592 + (126193152)*R + (62914560)*R^2)*T^2 + (63035392 + (125949952)*R + (62914560)*R^2)*T^3 + (31457280 + (62914560)*R + (31457280)*R^2)*T^4 + (6291456 + (12582912)*R + (6291456)*R^2)*T^5 + (16463633 + (32716544)*R + (16252928)*R^2 + (81894928 + (163159552)*R + (81264640)*R^2)*T + (163157760 + (325687040)*R + (162529280)*R^2)*T^2 + (162738176 + (325267456)*R + (162529280)*R^2)*T^3 + (81264640 + (162529280)*R + (81264640)*R^2)*T^4 + (16252928 + (32505856)*R + (16252928)*R^2)*T^5)*Z + (19029058 + (37903424)*R + (18874368)*R^2 + (94835074 + (189206912)*R + (94371840)*R^2)*T + (189206080 + (377949760)*R + (188743680)*R^2)*T^2 + (188897536 + (377641216)*R + (188743680)*R^2)*T^3 + (94371840 + (188743680)*R + (94371840)*R^2)*T^4 + (18874368 + (37748736)*R + (18874368)*R^2)*T^5)*Z^2 + (13038912 + (26015040)*R + (12976128)*R^2 + (65068800 + (129949440)*R + (64880640)*R^2)*T + (129949248 + (259710528)*R + (129761280)*R^2)*T^2 + (129823872 + (259585152)*R + (129761280)*R^2)*T^3 + (64880640 + (129761280)*R + (64880640)*R^2)*T^4 + (12976128 + (25952256)*R + (12976128)*R^2)*T^5)*Z^3 + (5864302 + (11713390)*R + (5849088)*R^2 + (29291060 + (58536500)*R + (29245440)*R^2)*T + (58536478 + (117027358)*R + (58490880)*R^2)*T^2 + (58506072 + (116996952)*R + (58490880)*R^2)*T^3 + (29245440 + (58490880)*R + (29245440)*R^2)*T^4 + (5849088 + (11698176)*R + (5849088)*R^2)*T^5)*Z^4 + (1808537 + (3614873)*R + (1806336)*R^2 + (9038282 + (18069962)*R + (9031680)*R^2)*T + (18069961 + (36133321)*R + (18063360)*R^2)*T^2 + (18065560 + (36128920)*R + (18063360)*R^2)*T^3 + (9031680 + (18063360)*R + (9031680)*R^2)*T^4 + (1806336 + (3612672)*R + (1806336)*R^2)*T^5)*Z^5 + (387248 + (774320)*R + (387072)*R^2 + (1935888 + (3871248)*R + (1935360)*R^2)*T + (3871248 + (7741968)*R + (3870720)*R^2)*T^2 + (3870896 + (7741616)*R + (3870720)*R^2)*T^3 + (1935360 + (3870720)*R + (1935360)*R^2)*T^4 + (387072 + (774144)*R + (387072)*R^2)*T^5)*Z^6 + (56838 + (113670)*R + (56832)*R^2 + (284178 + (568338)*R + (284160)*R^2)*T + (568338 + (1136658)*R + (568320)*R^2)*T^2 + (568326 + (1136646)*R + (568320)*R^2)*T^3 + (284160 + (568320)*R + (284160)*R^2)*T^4 + (56832 + (113664)*R + (56832)*R^2)*T^5)*Z^7 + (5472 + (10944)*R + (5472)*R^2 + (27360 + (54720)*R + (27360)*R^2)*T + (54720 + (109440)*R + (54720)*R^2)*T^2 + (54720 + (109440)*R + (54720)*R^2)*T^3 + (27360 + (54720)*R + (27360)*R^2)*T^4 + (5472 + (10944)*R + (5472)*R^2)*T^5)*Z^8 + (312 + (624)*R + (312)*R^2 + (1560 + (3120)*R + (1560)*R^2)*T + (3120 + (6240)*R + (3120)*R^2)*T^2 + (3120 + (6240)*R + (3120)*R^2)*T^3 + (1560 + (3120)*R + (1560)*R^2)*T^4 + (312 + (624)*R + (312)*R^2)*T^5)*Z^9 + (8 + (16)*R + (8)*R^2 + (40 + (80)*R + (40)*R^2)*T + (80 + (160)*R + (80)*R^2)*T^2 + (80 + (160)*R + (80)*R^2)*T^3 + (40 + (80)*R + (40)*R^2)*T^4 + (8 + (16)*R + (8)*R^2)*T^5)*Z^10) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-t1/old.1.seam
private theorem cert_smallt_largee_t1_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 1 =
      (22338 + (22336)*R + (66174 + (66176)*R)*T + (65344 + (65344)*R)*T^2 + (21504 + (21504)*R)*T^3 + (42545 + (42544)*R + (126560 + (126560)*R)*T + (125488 + (125488)*R)*T^2 + (41472 + (41472)*R)*T^3)*Z + (34220 + (34220)*R + (102104 + (102104)*R)*T + (101548 + (101548)*R)*T^2 + (33664 + (33664)*R)*T^3)*Z^2 + (15121 + (15121)*R + (45218 + (45218)*R)*T + (45073 + (45073)*R)*T^2 + (14976 + (14976)*R)*T^3)*Z^3 + (3975 + (3975)*R + (11906 + (11906)*R)*T + (11887 + (11887)*R)*T^2 + (3956 + (3956)*R)*T^3)*Z^4 + (623 + (623)*R + (1868 + (1868)*R)*T + (1867 + (1867)*R)*T^2 + (622 + (622)*R)*T^3)*Z^5 + (54 + (54)*R + (162 + (162)*R)*T + (162 + (162)*R)*T^2 + (54 + (54)*R)*T^3)*Z^6 + (2 + (2)*R + (6 + (6)*R)*T + (6 + (6)*R)*T^2 + (2 + (2)*R)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-t1/old.2.seam
private theorem cert_smallt_largee_t1_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 2 =
      (453264 + (942742)*R + (489472)*R^2 + (1889440 + (3884192)*R + (1994752)*R^2)*T + (2943488 + (5988864)*R + (3045376)*R^2)*T^2 + (2031616 + (4096000)*R + (2064384)*R^2)*T^3 + (524288 + (1048576)*R + (524288)*R^2)*T^4 + (1058157 + (2177902)*R + (1119744)*R^2 + (4360816 + (8902256)*R + (4541440)*R^2)*T + (6726912 + (13630208)*R + (6903296)*R^2)*T^2 + (4603904 + (9265152)*R + (4661248)*R^2)*T^3 + (1179648 + (2359296)*R + (1179648)*R^2)*T^4)*Z + (1090266 + (2225626)*R + (1135360)*R^2 + (4453786 + (9040794)*R + (4587008)*R^2)*T + (6816448 + (13764032)*R + (6947584)*R^2)*T^2 + (4632576 + (9308160)*R + (4675584)*R^2)*T^3 + (1179648 + (2359296)*R + (1179648)*R^2)*T^4)*Z^2 + (651458 + (1321346)*R + (669888)*R^2 + (2643330 + (5341442)*R + (2698112)*R^2)*T + (4020416 + (8095104)*R + (4074688)*R^2)*T^2 + (2716672 + (5451264)*R + (2734592)*R^2)*T^3 + (688128 + (1376256)*R + (688128)*R^2)*T^4)*Z^3 + (248986 + (502514)*R + (253528)*R^2 + (1005108 + (2023780)*R + (1018672)*R^2)*T + (1521306 + (3056114)*R + (1534808)*R^2)*T^2 + (1023232 + (2050944)*R + (1027712)*R^2)*T^3 + (258048 + (516096)*R + (258048)*R^2)*T^4)*Z^4 + (63163 + (127001)*R + (63838)*R^2 + (254006 + (510034)*R + (256028)*R^2)*T + (383035 + (768089)*R + (385054)*R^2)*T^2 + (256704 + (514080)*R + (257376)*R^2)*T^3 + (64512 + (129024)*R + (64512)*R^2)*T^4)*Z^5 + (10640 + (21336)*R + (10696)*R^2 + (42672 + (85512)*R + (42840)*R^2)*T + (64176 + (128520)*R + (64344)*R^2)*T^2 + (42896 + (85848)*R + (42952)*R^2)*T^3 + (10752 + (21504)*R + (10752)*R^2)*T^4)*Z^6 + (1148 + (2298)*R + (1150)*R^2 + (4596 + (9198)*R + (4602)*R^2)*T + (6900 + (13806)*R + (6906)*R^2)*T^2 + (4604 + (9210)*R + (4606)*R^2)*T^3 + (1152 + (2304)*R + (1152)*R^2)*T^4)*Z^7 + (72 + (144)*R + (72)*R^2 + (288 + (576)*R + (288)*R^2)*T + (432 + (864)*R + (432)*R^2)*T^2 + (288 + (576)*R + (288)*R^2)*T^3 + (72 + (144)*R + (72)*R^2)*T^4)*Z^8 + (2 + (4)*R + (2)*R^2 + (8 + (16)*R + (8)*R^2)*T + (12 + (24)*R + (12)*R^2)*T^2 + (8 + (16)*R + (8)*R^2)*T^3 + (2 + (4)*R + (2)*R^2)*T^4)*Z^9) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-t1/new.0.slack
private theorem cert_smallt_largee_t1_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 3 =
      (3727192 + (7921664)*R + (4194304)*R^2 + (19572580 + (40544256)*R + (20971520)*R^2)*T + (40546304 + (82489344)*R + (41943040)*R^2)*T^2 + (41478144 + (83421184)*R + (41943040)*R^2)*T^3 + (20971520 + (41943040)*R + (20971520)*R^2)*T^4 + (4194304 + (8388608)*R + (4194304)*R^2)*T^5 + (8635823 + (18073088)*R + (9437184)*R^2 + (44784560 + (91970560)*R + (47185920)*R^2)*T + (91973120 + (186344960)*R + (94371840)*R^2)*T^2 + (93573120 + (187944960)*R + (94371840)*R^2)*T^3 + (47185920 + (94371840)*R + (47185920)*R^2)*T^4 + (9437184 + (18874368)*R + (9437184)*R^2)*T^5)*Z + (8848886 + (18286080)*R + (9437184)*R^2 + (45422326 + (92608256)*R + (47185920)*R^2)*T + (92609536 + (186981376)*R + (94371840)*R^2)*T^2 + (93784832 + (188156672)*R + (94371840)*R^2)*T^3 + (47185920 + (94371840)*R + (47185920)*R^2)*T^4 + (9437184 + (18874368)*R + (9437184)*R^2)*T^5)*Z^2 + (5265472 + (10770496)*R + (5505024)*R^2 + (26806784 + (54331904)*R + (27525120)*R^2)*T + (54332224 + (109382464)*R + (55050240)*R^2)*T^2 + (54811008 + (109861248)*R + (55050240)*R^2)*T^3 + (27525120 + (55050240)*R + (27525120)*R^2)*T^4 + (5505024 + (11010048)*R + (5505024)*R^2)*T^5)*Z^3 + (2005952 + (4070336)*R + (2064384)*R^2 + (10146664 + (20468584)*R + (10321920)*R^2)*T + (20468624 + (41112464)*R + (20643840)*R^2)*T^2 + (20585448 + (41229288)*R + (20643840)*R^2)*T^3 + (10321920 + (20643840)*R + (10321920)*R^2)*T^4 + (2064384 + (4128768)*R + (2064384)*R^2)*T^5)*Z^4 + (507558 + (1023654)*R + (516096)*R^2 + (2554868 + (5135348)*R + (2580480)*R^2)*T + (5135350 + (10296310)*R + (5160960)*R^2)*T^2 + (5152424 + (10313384)*R + (5160960)*R^2)*T^3 + (2580480 + (5160960)*R + (2580480)*R^2)*T^4 + (516096 + (1032192)*R + (516096)*R^2)*T^5)*Z^5 + (85324 + (171340)*R + (86016)*R^2 + (428004 + (858084)*R + (430080)*R^2)*T + (858084 + (1718244)*R + (860160)*R^2)*T^2 + (859468 + (1719628)*R + (860160)*R^2)*T^3 + (430080 + (860160)*R + (430080)*R^2)*T^4 + (86016 + (172032)*R + (86016)*R^2)*T^5)*Z^6 + (9192 + (18408)*R + (9216)*R^2 + (46008 + (92088)*R + (46080)*R^2)*T + (92088 + (184248)*R + (92160)*R^2)*T^2 + (92136 + (184296)*R + (92160)*R^2)*T^3 + (46080 + (92160)*R + (46080)*R^2)*T^4 + (9216 + (18432)*R + (9216)*R^2)*T^5)*Z^7 + (576 + (1152)*R + (576)*R^2 + (2880 + (5760)*R + (2880)*R^2)*T + (5760 + (11520)*R + (5760)*R^2)*T^2 + (5760 + (11520)*R + (5760)*R^2)*T^3 + (2880 + (5760)*R + (2880)*R^2)*T^4 + (576 + (1152)*R + (576)*R^2)*T^5)*Z^8 + (16 + (32)*R + (16)*R^2 + (80 + (160)*R + (80)*R^2)*T + (160 + (320)*R + (160)*R^2)*T^2 + (160 + (320)*R + (160)*R^2)*T^3 + (80 + (160)*R + (80)*R^2)*T^4 + (16 + (32)*R + (16)*R^2)*T^5)*Z^9) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-t1/new.1.slack
private theorem cert_smallt_largee_t1_new_1_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 4 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 4 =
      (32158 + (32128)*R + (98082 + (98048)*R)*T + (99712 + (99712)*R)*T^2 + (33792 + (33792)*R)*T^3 + (48047 + (48032)*R + (146256 + (146240)*R)*T + (148384 + (148384)*R)*T^2 + (50176 + (50176)*R)*T^3)*Z + (29994 + (29992)*R + (91090 + (91088)*R)*T + (92200 + (92200)*R)*T^2 + (31104 + (31104)*R)*T^3)*Z^2 + (10014 + (10014)*R + (30332 + (30332)*R)*T + (30622 + (30622)*R)*T^2 + (10304 + (10304)*R)*T^3)*Z^3 + (1886 + (1886)*R + (5696 + (5696)*R)*T + (5734 + (5734)*R)*T^2 + (1924 + (1924)*R)*T^3)*Z^4 + (190 + (190)*R + (572 + (572)*R)*T + (574 + (574)*R)*T^2 + (192 + (192)*R)*T^3)*Z^5 + (8 + (8)*R + (24 + (24)*R)*T + (24 + (24)*R)*T^2 + (8 + (8)*R)*T^3)*Z^6) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-t1/new.2.slack
private theorem cert_smallt_largee_t1_new_2_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 5 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/4) 5 =
      (142192 + (211818)*R + (69632)*R^2 + (415584 + (620384)*R + (204800)*R^2)*T + (404480 + (605184)*R + (200704)*R^2)*T^2 + (131072 + (196608)*R + (65536)*R^2)*T^3 + (243091 + (362898)*R + (119808)*R^2 + (715664 + (1069968)*R + (354304)*R^2)*T + (701952 + (1051136)*R + (349184)*R^2)*T^2 + (229376 + (344064)*R + (114688)*R^2)*T^3)*Z + (178790 + (267366)*R + (88576)*R^2 + (529638 + (792806)*R + (263168)*R^2)*T + (522880 + (783488)*R + (260608)*R^2)*T^2 + (172032 + (258048)*R + (86016)*R^2)*T^3)*Z^2 + (73342 + (109822)*R + (36480)*R^2 + (218366 + (327166)*R + (108800)*R^2)*T + (216704 + (324864)*R + (108160)*R^2)*T^2 + (71680 + (107520)*R + (35840)*R^2)*T^3)*Z^3 + (18124 + (27164)*R + (9040)*R^2 + (54168 + (81208)*R + (27040)*R^2)*T + (53964 + (80924)*R + (26960)*R^2)*T^2 + (17920 + (26880)*R + (8960)*R^2)*T^3)*Z^4 + (2698 + (4046)*R + (1348)*R^2 + (8084 + (12124)*R + (4040)*R^2)*T + (8074 + (12110)*R + (4036)*R^2)*T^2 + (2688 + (4032)*R + (1344)*R^2)*T^3)*Z^5 + (224 + (336)*R + (112)*R^2 + (672 + (1008)*R + (336)*R^2)*T + (672 + (1008)*R + (336)*R^2)*T^2 + (224 + (336)*R + (112)*R^2)*T^3)*Z^6 + (8 + (12)*R + (4)*R^2 + (24 + (36)*R + (12)*R^2)*T + (24 + (36)*R + (12)*R^2)*T^2 + (8 + (12)*R + (4)*R^2)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-tmax/old.0.seam
private theorem cert_smallt_smalle_tmax_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 0 =
      (435428 + (828608)*H + (393216)*H^2 + (1263836 + (2443456)*H + (1179648)*H^2)*T + (1221632 + (2401280)*H + (1179648)*H^2)*T^2 + (393216 + (786432)*H + (393216)*H^2)*T^3 + (890001 + (1709184)*H + (819200)*H^2 + (2599056 + (5056640)*H + (2457600)*H^2)*T + (2528256 + (4985856)*H + (2457600)*H^2)*T^2 + (819200 + (1638400)*H + (819200)*H^2)*T^3)*Z + (796574 + (1542044)*H + (745472)*H^2 + (2338590 + (4575004)*H + (2236416)*H^2)*T + (2287488 + (4523904)*H + (2236416)*H^2)*T^2 + (745472 + (1490944)*H + (745472)*H^2)*T^3)*Z^2 + (407618 + (794690)*H + (387072)*H^2 + (1202306 + (2363522)*H + (1161216)*H^2)*T + (1181760 + (2342976)*H + (1161216)*H^2)*T^2 + (387072 + (774144)*H + (387072)*H^2)*T^3)*Z^3 + (130404 + (255844)*H + (125440)*H^2 + (386248 + (762568)*H + (376320)*H^2)*T + (381284 + (757604)*H + (376320)*H^2)*T^2 + (125440 + (250880)*H + (125440)*H^2)*T^3)*Z^4 + (26704 + (52688)*H + (25984)*H^2 + (79392 + (157344)*H + (77952)*H^2)*T + (78672 + (156624)*H + (77952)*H^2)*T^2 + (25984 + (51968)*H + (25984)*H^2)*T^3)*Z^5 + (3418 + (6778)*H + (3360)*H^2 + (10196 + (20276)*H + (10080)*H^2)*T + (10138 + (20218)*H + (10080)*H^2)*T^2 + (3360 + (6720)*H + (3360)*H^2)*T^3)*Z^6 + (250 + (498)*H + (248)*H^2 + (748 + (1492)*H + (744)*H^2)*T + (746 + (1490)*H + (744)*H^2)*T^2 + (248 + (496)*H + (248)*H^2)*T^3)*Z^7 + (8 + (16)*H + (8)*H^2 + (24 + (48)*H + (24)*H^2)*T + (24 + (48)*H + (24)*H^2)*T^2 + (8 + (16)*H + (8)*H^2)*T^3)*Z^8) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-tmax/old.1.seam
private theorem cert_smallt_smalle_tmax_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 1 =
      (874 + (872)*H + (1638 + (1640)*H)*T + (768 + (768)*H)*T^2 + (1299 + (1298)*H + (2514 + (2514)*H)*T + (1216 + (1216)*H)*T^2)*Z + (774 + (774)*H + (1526 + (1526)*H)*T + (752 + (752)*H)*T^2)*Z^2 + (230 + (230)*H + (458 + (458)*H)*T + (228 + (228)*H)*T^2)*Z^3 + (34 + (34)*H + (68 + (68)*H)*T + (34 + (34)*H)*T^2)*Z^4 + (2 + (2)*H + (4 + (4)*H)*T + (2 + (2)*H)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-tmax/old.2.seam
private theorem cert_smallt_smalle_tmax_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 2 =
      (29386 + (64208)*H + (34816)*H^2 + (57984 + (125568)*H + (67584)*H^2)*T + (28672 + (61440)*H + (32768)*H^2)*T^2 + (53207 + (113112)*H + (59904)*H^2 + (105376 + (222624)*H + (117248)*H^2)*T + (52224 + (109568)*H + (57344)*H^2)*T^2)*Z + (40981 + (85269)*H + (44288)*H^2 + (81416 + (168712)*H + (87296)*H^2)*T + (40448 + (83456)*H + (43008)*H^2)*T^2)*Z^2 + (17423 + (35663)*H + (18240)*H^2 + (34702 + (70862)*H + (36160)*H^2)*T + (17280 + (35200)*H + (17920)*H^2)*T^2)*Z^3 + (4419 + (8939)*H + (4520)*H^2 + (8819 + (17819)*H + (9000)*H^2)*T + (4400 + (8880)*H + (4480)*H^2)*T^2)*Z^4 + (669 + (1343)*H + (674)*H^2 + (1337 + (2683)*H + (1346)*H^2)*T + (668 + (1340)*H + (672)*H^2)*T^2)*Z^5 + (56 + (112)*H + (56)*H^2 + (112 + (224)*H + (112)*H^2)*T + (56 + (112)*H + (56)*H^2)*T^2)*Z^6 + (2 + (4)*H + (2)*H^2 + (4 + (8)*H + (4)*H^2)*T + (2 + (4)*H + (2)*H^2)*T^2)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-tmax/new.0.slack
private theorem cert_smallt_smalle_tmax_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 3 =
      (53848 + (316160)*H + (262144)*H^2 + (370276 + (1156864)*H + (786432)*H^2)*T + (578560 + (1364992)*H + (786432)*H^2)*T^2 + (262144 + (524288)*H + (262144)*H^2)*T^3 + (106223 + (565056)*H + (458752)*H^2 + (671472 + (2047808)*H + (1376256)*H^2)*T + (1024000 + (2400256)*H + (1376256)*H^2)*T^2 + (458752 + (917504)*H + (458752)*H^2)*T^3)*Z + (88390 + (432464)*H + (344064)*H^2 + (520902 + (1553104)*H + (1032192)*H^2)*T + (776576 + (1808768)*H + (1032192)*H^2)*T^2 + (344064 + (688128)*H + (344064)*H^2)*T^3)*Z^2 + (40380 + (183740)*H + (143360)*H^2 + (224124 + (654204)*H + (430080)*H^2)*T + (327104 + (757184)*H + (430080)*H^2)*T^2 + (143360 + (286720)*H + (143360)*H^2)*T^3)*Z^3 + (10964 + (46804)*H + (35840)*H^2 + (57768 + (165288)*H + (107520)*H^2)*T + (82644 + (190164)*H + (107520)*H^2)*T^2 + (35840 + (71680)*H + (35840)*H^2)*T^3)*Z^4 + (1772 + (7148)*H + (5376)*H^2 + (8920 + (25048)*H + (16128)*H^2)*T + (12524 + (28652)*H + (16128)*H^2)*T^2 + (5376 + (10752)*H + (5376)*H^2)*T^3)*Z^5 + (158 + (606)*H + (448)*H^2 + (764 + (2108)*H + (1344)*H^2)*T + (1054 + (2398)*H + (1344)*H^2)*T^2 + (448 + (896)*H + (448)*H^2)*T^3)*Z^6 + (6 + (22)*H + (16)*H^2 + (28 + (76)*H + (48)*H^2)*T + (38 + (86)*H + (48)*H^2)*T^2 + (16 + (32)*H + (16)*H^2)*T^3)*Z^7) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-smalle-tmax/new.1.slack
private theorem cert_smallt_smalle_tmax_new_1_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 4 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) ((Z+4)^2/4) 4 =
      (36686 + (36656)*H + (73554 + (73520)*H)*T + (36864 + (36864)*H)*T^2 + (63979 + (63964)*H + (128108 + (128092)*H)*T + (64128 + (64128)*H)*T^2)*Z + (47670 + (47668)*H + (95382 + (95380)*H)*T + (47712 + (47712)*H)*T^2)*Z^2 + (19668 + (19668)*H + (39340 + (39340)*H)*T + (19672 + (19672)*H)*T^2)*Z^3 + (4850 + (4850)*H + (9700 + (9700)*H)*T + (4850 + (4850)*H)*T^2)*Z^4 + (714 + (714)*H + (1428 + (1428)*H)*T + (714 + (714)*H)*T^2)*Z^5 + (58 + (58)*H + (116 + (116)*H)*T + (58 + (58)*H)*T^2)*Z^6 + (2 + (2)*H + (4 + (4)*H)*T + (2 + (2)*H)*T^2)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-tmax/old.0.seam
private theorem cert_smallt_largee_tmax_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 0 =
      (1657252 + (3230080)*R + (1572864)*R^2 + (8117020 + (15981312)*R + (7864320)*R^2)*T + (15980928 + (31709568)*R + (15728640)*R^2)*T^2 + (15812608 + (31541248)*R + (15728640)*R^2)*T^3 + (7864320 + (15728640)*R + (7864320)*R^2)*T^4 + (1572864 + (3145728)*R + (1572864)*R^2)*T^5 + (3418385 + (6695168)*R + (3276800)*R^2 + (16808464 + (33192448)*R + (16384000)*R^2)*T + (33192192 + (65960192)*R + (32768000)*R^2)*T^2 + (32909312 + (65677312)*R + (32768000)*R^2)*T^3 + (16384000 + (32768000)*R + (16384000)*R^2)*T^4 + (3276800 + (6553600)*R + (3276800)*R^2)*T^5)*Z + (3084090 + (6065976)*R + (2981888)*R^2 + (15215986 + (30125424)*R + (14909440)*R^2)*T + (30125368 + (59944248)*R + (29818880)*R^2)*T^2 + (29921024 + (59739904)*R + (29818880)*R^2)*T^3 + (14909440 + (29818880)*R + (14909440)*R^2)*T^4 + (2981888 + (5963776)*R + (2981888)*R^2)*T^5)*Z^2 + (1589380 + (3137668)*R + (1548288)*R^2 + (7864712 + (15606152)*R + (7741440)*R^2)*T + (15606148 + (31089028)*R + (15482880)*R^2)*T^2 + (15523968 + (31006848)*R + (15482880)*R^2)*T^3 + (7741440 + (15482880)*R + (7741440)*R^2)*T^4 + (1548288 + (3096576)*R + (1548288)*R^2)*T^5)*Z^3 + (511688 + (1013448)*R + (501760)*R^2 + (2538584 + (5047384)*R + (2508800)*R^2)*T + (5047384 + (10064984)*R + (5017600)*R^2)*T^2 + (5027528 + (10045128)*R + (5017600)*R^2)*T^3 + (2508800 + (5017600)*R + (2508800)*R^2)*T^4 + (501760 + (1003520)*R + (501760)*R^2)*T^5)*Z^4 + (105376 + (209312)*R + (103936)*R^2 + (524000 + (1043680)*R + (519680)*R^2)*T + (1043680 + (2083040)*R + (1039360)*R^2)*T^2 + (1040800 + (2080160)*R + (1039360)*R^2)*T^3 + (519680 + (1039360)*R + (519680)*R^2)*T^4 + (103936 + (207872)*R + (103936)*R^2)*T^5)*Z^5 + (13556 + (26996)*R + (13440)*R^2 + (67548 + (134748)*R + (67200)*R^2)*T + (134748 + (269148)*R + (134400)*R^2)*T^2 + (134516 + (268916)*R + (134400)*R^2)*T^3 + (67200 + (134400)*R + (67200)*R^2)*T^4 + (13440 + (26880)*R + (13440)*R^2)*T^5)*Z^6 + (996 + (1988)*R + (992)*R^2 + (4972 + (9932)*R + (4960)*R^2)*T + (9932 + (19852)*R + (9920)*R^2)*T^2 + (9924 + (19844)*R + (9920)*R^2)*T^3 + (4960 + (9920)*R + (4960)*R^2)*T^4 + (992 + (1984)*R + (992)*R^2)*T^5)*Z^7 + (32 + (64)*R + (32)*R^2 + (160 + (320)*R + (160)*R^2)*T + (320 + (640)*R + (320)*R^2)*T^2 + (320 + (640)*R + (320)*R^2)*T^3 + (160 + (320)*R + (160)*R^2)*T^4 + (32 + (64)*R + (32)*R^2)*T^5)*Z^8) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-tmax/old.1.seam
private theorem cert_smallt_largee_tmax_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 1 =
      (1746 + (1744)*R + (5022 + (5024)*R)*T + (4816 + (4816)*R)*T^2 + (1536 + (1536)*R)*T^3 + (2597 + (2596)*R + (7624 + (7624)*R)*T + (7460 + (7460)*R)*T^2 + (2432 + (2432)*R)*T^3)*Z + (1548 + (1548)*R + (4600 + (4600)*R)*T + (4556 + (4556)*R)*T^2 + (1504 + (1504)*R)*T^3)*Z^2 + (460 + (460)*R + (1376 + (1376)*R)*T + (1372 + (1372)*R)*T^2 + (456 + (456)*R)*T^3)*Z^3 + (68 + (68)*R + (204 + (204)*R)*T + (204 + (204)*R)*T^2 + (68 + (68)*R)*T^3)*Z^4 + (4 + (4)*R + (12 + (12)*R)*T + (12 + (12)*R)*T^2 + (4 + (4)*R)*T^3)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-tmax/old.2.seam
private theorem cert_smallt_largee_tmax_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 2 =
      (111504 + (233878)*R + (122368)*R^2 + (468640 + (967328)*R + (498688)*R^2)*T + (733952 + (1495296)*R + (761344)*R^2)*T^2 + (507904 + (1024000)*R + (516096)*R^2)*T^3 + (131072 + (262144)*R + (131072)*R^2)*T^4 + (205357 + (424110)*R + (218752)*R^2 + (848880 + (1734896)*R + (886016)*R^2)*T + (1311168 + (2656320)*R + (1345152)*R^2)*T^2 + (897024 + (1804288)*R + (907264)*R^2)*T^3 + (229376 + (458752)*R + (229376)*R^2)*T^4)*Z + (160202 + (327018)*R + (166816)*R^2 + (654202 + (1326778)*R + (672576)*R^2)*T + (999856 + (2016592)*R + (1016736)*R^2)*T^2 + (677888 + (1360896)*R + (683008)*R^2)*T^3 + (172032 + (344064)*R + (172032)*R^2)*T^4)*Z^2 + (68758 + (139150)*R + (70392)*R^2 + (278314 + (561178)*R + (282864)*R^2)*T + (422036 + (848268)*R + (426232)*R^2)*T^2 + (284160 + (569600)*R + (285440)*R^2)*T^3 + (71680 + (143360)*R + (71680)*R^2)*T^4)*Z^3 + (17558 + (35318)*R + (17760)*R^2 + (70636 + (141836)*R + (71200)*R^2)*T + (106518 + (213558)*R + (107040)*R^2)*T^2 + (71360 + (142880)*R + (71520)*R^2)*T^3 + (17920 + (35840)*R + (17920)*R^2)*T^4)*Z^4 + (2670 + (5350)*R + (2680)*R^2 + (10700 + (21428)*R + (10728)*R^2)*T + (16078 + (32182)*R + (16104)*R^2)*T^2 + (10736 + (21480)*R + (10744)*R^2)*T^3 + (2688 + (5376)*R + (2688)*R^2)*T^4)*Z^5 + (224 + (448)*R + (224)*R^2 + (896 + (1792)*R + (896)*R^2)*T + (1344 + (2688)*R + (1344)*R^2)*T^2 + (896 + (1792)*R + (896)*R^2)*T^3 + (224 + (448)*R + (224)*R^2)*T^4)*Z^6 + (8 + (16)*R + (8)*R^2 + (32 + (64)*R + (32)*R^2)*T + (48 + (96)*R + (48)*R^2)*T^2 + (32 + (64)*R + (32)*R^2)*T^3 + (8 + (16)*R + (8)*R^2)*T^4)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-tmax/new.0.slack
private theorem cert_smallt_largee_tmax_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 3 =
      (632152 + (1680896)*R + (1048576)*R^2 + (3994468 + (9237504)*R + (5242880)*R^2)*T + (9238016 + (19723776)*R + (10485760)*R^2)*T^2 + (10070016 + (20555776)*R + (10485760)*R^2)*T^3 + (5242880 + (10485760)*R + (5242880)*R^2)*T^4 + (1048576 + (2097152)*R + (1048576)*R^2)*T^5 + (1130031 + (2965120)*R + (1835008)*R^2 + (7060656 + (16235776)*R + (9175040)*R^2)*T + (16236160 + (34586240)*R + (18350080)*R^2)*T^2 + (17645568 + (35995648)*R + (18350080)*R^2)*T^3 + (9175040 + (18350080)*R + (9175040)*R^2)*T^4 + (1835008 + (3670016)*R + (1835008)*R^2)*T^5)*Z + (864918 + (2241184)*R + (1376256)*R^2 + (5347382 + (12228672)*R + (6881280)*R^2)*T + (12228768 + (25991328)*R + (13762560)*R^2)*T^2 + (13251328 + (27013888)*R + (13762560)*R^2)*T^3 + (6881280 + (13762560)*R + (6881280)*R^2)*T^4 + (1376256 + (2752512)*R + (1376256)*R^2)*T^5)*Z^2 + (367480 + (940920)*R + (573440)*R^2 + (2249328 + (5116528)*R + (2867200)*R^2)*T + (5116536 + (10850936)*R + (5734400)*R^2)*T^2 + (5528448 + (11262848)*R + (5734400)*R^2)*T^3 + (2867200 + (5734400)*R + (2867200)*R^2)*T^4 + (573440 + (1146880)*R + (573440)*R^2)*T^5)*Z^3 + (93608 + (236968)*R + (143360)*R^2 + (567544 + (1284344)*R + (716800)*R^2)*T + (1284344 + (2717944)*R + (1433600)*R^2)*T^2 + (1383848 + (2817448)*R + (1433600)*R^2)*T^3 + (716800 + (1433600)*R + (716800)*R^2)*T^4 + (143360 + (286720)*R + (143360)*R^2)*T^5)*Z^4 + (14296 + (35800)*R + (21504)*R^2 + (85896 + (193416)*R + (107520)*R^2)*T + (193416 + (408456)*R + (215040)*R^2)*T^2 + (207832 + (422872)*R + (215040)*R^2)*T^3 + (107520 + (215040)*R + (107520)*R^2)*T^4 + (21504 + (43008)*R + (21504)*R^2)*T^5)*Z^5 + (1212 + (3004)*R + (1792)*R^2 + (7220 + (16180)*R + (8960)*R^2)*T + (16180 + (34100)*R + (17920)*R^2)*T^2 + (17340 + (35260)*R + (17920)*R^2)*T^3 + (8960 + (17920)*R + (8960)*R^2)*T^4 + (1792 + (3584)*R + (1792)*R^2)*T^5)*Z^6 + (44 + (108)*R + (64)*R^2 + (260 + (580)*R + (320)*R^2)*T + (580 + (1220)*R + (640)*R^2)*T^2 + (620 + (1260)*R + (640)*R^2)*T^3 + (320 + (640)*R + (320)*R^2)*T^4 + (64 + (128)*R + (64)*R^2)*T^5)*Z^7) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-tmax/new.1.slack
private theorem cert_smallt_largee_tmax_new_1_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 4 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 4 =
      (73342 + (73312)*R + (220386 + (220352)*R)*T + (220768 + (220768)*R)*T^2 + (73728 + (73728)*R)*T^3 + (127943 + (127928)*R + (384128 + (384112)*R)*T + (384440 + (384440)*R)*T^2 + (128256 + (128256)*R)*T^3)*Z + (95338 + (95336)*R + (286098 + (286096)*R)*T + (286184 + (286184)*R)*T^2 + (95424 + (95424)*R)*T^3)*Z^2 + (39336 + (39336)*R + (118016 + (118016)*R)*T + (118024 + (118024)*R)*T^2 + (39344 + (39344)*R)*T^3)*Z^3 + (9700 + (9700)*R + (29100 + (29100)*R)*T + (29100 + (29100)*R)*T^2 + (9700 + (9700)*R)*T^3)*Z^4 + (1428 + (1428)*R + (4284 + (4284)*R)*T + (4284 + (4284)*R)*T^2 + (1428 + (1428)*R)*T^3)*Z^5 + (116 + (116)*R + (348 + (348)*R)*T + (348 + (348)*R)*T^2 + (116 + (116)*R)*T^3)*Z^6 + (4 + (4)*R + (12 + (12)*R)*T + (12 + (12)*R)*T^2 + (4 + (4)*R)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- smallt-largee-tmax/new.2.slack
private theorem cert_smallt_largee_tmax_new_2_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 5 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) ((2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2) 5 =
      (39280 + (56682)*R + (17408)*R^2 + (111456 + (162656)*R + (51200)*R^2)*T + (104960 + (155136)*R + (50176)*R^2)*T^2 + (32768 + (49152)*R + (16384)*R^2)*T^3 + (48147 + (69394)*R + (21248)*R^2 + (137360 + (200336)*R + (62976)*R^2)*T + (130176 + (192384)*R + (62208)*R^2)*T^2 + (40960 + (61440)*R + (20480)*R^2)*T^3)*Z + (23686 + (34118)*R + (10432)*R^2 + (67878 + (98982)*R + (31104)*R^2)*T + (64672 + (95584)*R + (30912)*R^2)*T^2 + (20480 + (30720)*R + (10240)*R^2)*T^3)*Z^2 + (5846 + (8422)*R + (2576)*R^2 + (16814 + (24526)*R + (7712)*R^2)*T + (16088 + (23784)*R + (7696)*R^2)*T^2 + (5120 + (7680)*R + (2560)*R^2)*T^3)*Z^3 + (724 + (1044)*R + (320)*R^2 + (2088 + (3048)*R + (960)*R^2)*T + (2004 + (2964)*R + (960)*R^2)*T^2 + (640 + (960)*R + (320)*R^2)*T^3)*Z^4 + (36 + (52)*R + (16)*R^2 + (104 + (152)*R + (48)*R^2)*T + (100 + (148)*R + (48)*R^2)*T^2 + (32 + (48)*R + (16)*R^2)*T^3)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-1/old.0.seam
private theorem cert_larget_smalle_1_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 0 =
      (864484 + (1650880)*H + (786432)*H^2 + (858112 + (1644544)*H + (786432)*H^2)*R + (2515164 + (4874432)*H + (2359296)*H^2 + (2502656 + (4861952)*H + (2359296)*H^2)*R)*T + (2437120 + (4796416)*H + (2359296)*H^2 + (2430976 + (4790272)*H + (2359296)*H^2)*R)*T^2 + (786432 + (1572864)*H + (786432)*H^2 + (786432 + (1572864)*H + (786432)*H^2)*R)*T^3 + (1772689 + (3411072)*H + (1638400)*H^2 + (1765376 + (3403776)*H + (1638400)*H^2)*R + (5183632 + (10098816)*H + (4915200)*H^2 + (5169152 + (10084352)*H + (4915200)*H^2)*R)*T + (5049344 + (9964544)*H + (4915200)*H^2 + (5042176 + (9957376)*H + (4915200)*H^2)*R)*T^2 + (1638400 + (3276800)*H + (1638400)*H^2 + (1638400 + (3276800)*H + (1638400)*H^2)*R)*T^3)*Z + (1589790 + (3080732)*H + (1490944)*H^2 + (1586432 + (3077376)*H + (1490944)*H^2)*R + (4670494 + (9143324)*H + (4472832)*H^2 + (4663808 + (9136640)*H + (4472832)*H^2)*R)*T + (4571648 + (9044480)*H + (4472832)*H^2 + (4568320 + (9041152)*H + (4472832)*H^2)*R)*T^2 + (1490944 + (2981888)*H + (1490944)*H^2 + (1490944 + (2981888)*H + (1490944)*H^2)*R)*T^3)*Z^2 + (814466 + (1588610)*H + (774144)*H^2 + (813696 + (1587840)*H + (774144)*H^2)*R + (2403074 + (4725506)*H + (2322432)*H^2 + (2401536 + (4723968)*H + (2322432)*H^2)*R)*T + (2362752 + (4685184)*H + (2322432)*H^2 + (2361984 + (4684416)*H + (2322432)*H^2)*R)*T^2 + (774144 + (1548288)*H + (774144)*H^2 + (774144 + (1548288)*H + (774144)*H^2)*R)*T^3)*Z^3 + (260720 + (511600)*H + (250880)*H^2 + (260632 + (511512)*H + (250880)*H^2)*R + (772320 + (1524960)*H + (752640)*H^2 + (772144 + (1524784)*H + (752640)*H^2)*R)*T + (762480 + (1515120)*H + (752640)*H^2 + (762392 + (1515032)*H + (752640)*H^2)*R)*T^2 + (250880 + (501760)*H + (250880)*H^2 + (250880 + (501760)*H + (250880)*H^2)*R)*T^3)*Z^4 + (53404 + (105372)*H + (51968)*H^2 + (53400 + (105368)*H + (51968)*H^2)*R + (158776 + (314680)*H + (155904)*H^2 + (158768 + (314672)*H + (155904)*H^2)*R)*T + (157340 + (313244)*H + (155904)*H^2 + (157336 + (313240)*H + (155904)*H^2)*R)*T^2 + (51968 + (103936)*H + (51968)*H^2 + (51968 + (103936)*H + (51968)*H^2)*R)*T^3)*Z^5 + (6836 + (13556)*H + (6720)*H^2 + (6836 + (13556)*H + (6720)*H^2)*R + (20392 + (40552)*H + (20160)*H^2 + (20392 + (40552)*H + (20160)*H^2)*R)*T + (20276 + (40436)*H + (20160)*H^2 + (20276 + (40436)*H + (20160)*H^2)*R)*T^2 + (6720 + (13440)*H + (6720)*H^2 + (6720 + (13440)*H + (6720)*H^2)*R)*T^3)*Z^6 + (500 + (996)*H + (496)*H^2 + (500 + (996)*H + (496)*H^2)*R + (1496 + (2984)*H + (1488)*H^2 + (1496 + (2984)*H + (1488)*H^2)*R)*T + (1492 + (2980)*H + (1488)*H^2 + (1492 + (2980)*H + (1488)*H^2)*R)*T^2 + (496 + (992)*H + (496)*H^2 + (496 + (992)*H + (496)*H^2)*R)*T^3)*Z^7 + (16 + (32)*H + (16)*H^2 + (16 + (32)*H + (16)*H^2)*R + (48 + (96)*H + (48)*H^2 + (48 + (96)*H + (48)*H^2)*R)*T + (48 + (96)*H + (48)*H^2 + (48 + (96)*H + (48)*H^2)*R)*T^2 + (16 + (32)*H + (16)*H^2 + (16 + (32)*H + (16)*H^2)*R)*T^3)*Z^8) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-1/old.1.seam
private theorem cert_larget_smalle_1_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 1 =
      (6772 + (6760)*H + (3338 + (3328)*H)*R + (13158 + (13160)*H + (6400 + (6400)*H)*R)*T + (6400 + (6400)*H + (3072 + (3072)*H)*R)*T^2 + (8661 + (8658)*H + (4290 + (4288)*H)*R + (17042 + (17042)*H + (8384 + (8384)*H)*R)*T + (8384 + (8384)*H + (4096 + (4096)*H)*R)*T^2)*Z + (4470 + (4470)*H + (2224 + (2224)*H)*R + (8870 + (8870)*H + (4400 + (4400)*H)*R)*T + (4400 + (4400)*H + (2176 + (2176)*H)*R)*T^2)*Z^2 + (1162 + (1162)*H + (580 + (580)*H)*R + (2318 + (2318)*H + (1156 + (1156)*H)*R)*T + (1156 + (1156)*H + (576 + (576)*H)*R)*T^2)*Z^3 + (152 + (152)*H + (76 + (76)*H)*R + (304 + (304)*H + (152 + (152)*H)*R)*T + (152 + (152)*H + (76 + (76)*H)*R)*T^2)*Z^4 + (8 + (8)*H + (4 + (4)*H)*R + (16 + (16)*H + (8 + (8)*H)*R)*T + (8 + (8)*H + (4 + (4)*H)*R)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-1/old.2.seam
private theorem cert_larget_smalle_1_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 2 =
      (63002 + (132640)*H + (69632)*H^2 + (67232 + (136864)*H + (69632)*H^2)*R + (124288 + (259456)*H + (135168)*H^2 + (132608 + (267776)*H + (135168)*H^2)*R)*T + (61440 + (126976)*H + (65536)*H^2 + (65536 + (131072)*H + (65536)*H^2)*R)*T^2 + (111631 + (231440)*H + (119808)*H^2 + (116848 + (236656)*H + (119808)*H^2)*R + (221088 + (455584)*H + (234496)*H^2 + (231424 + (465920)*H + (234496)*H^2)*R)*T + (109568 + (224256)*H + (114688)*H^2 + (114688 + (229376)*H + (114688)*H^2)*R)*T^2)*Z + (84546 + (173122)*H + (88576)*H^2 + (87130 + (175706)*H + (88576)*H^2)*R + (167976 + (342568)*H + (174592)*H^2 + (173120 + (347712)*H + (174592)*H^2)*R)*T + (83456 + (169472)*H + (86016)*H^2 + (86016 + (172032)*H + (86016)*H^2)*R)*T^2)*Z^2 + (35488 + (71968)*H + (36480)*H^2 + (36130 + (72610)*H + (36480)*H^2)*R + (70686 + (143006)*H + (72320)*H^2 + (71968 + (144288)*H + (72320)*H^2)*R)*T + (35200 + (71040)*H + (35840)*H^2 + (35840 + (71680)*H + (35840)*H^2)*R)*T^2)*Z^3 + (8918 + (17958)*H + (9040)*H^2 + (8998 + (18038)*H + (9040)*H^2)*R + (17798 + (35798)*H + (18000)*H^2 + (17958 + (35958)*H + (18000)*H^2)*R)*T + (8880 + (17840)*H + (8960)*H^2 + (8960 + (17920)*H + (8960)*H^2)*R)*T^2)*Z^4 + (1342 + (2690)*H + (1348)*H^2 + (1346 + (2694)*H + (1348)*H^2)*R + (2682 + (5374)*H + (2692)*H^2 + (2690 + (5382)*H + (2692)*H^2)*R)*T + (1340 + (2684)*H + (1344)*H^2 + (1344 + (2688)*H + (1344)*H^2)*R)*T^2)*Z^5 + (112 + (224)*H + (112)*H^2 + (112 + (224)*H + (112)*H^2)*R + (224 + (448)*H + (224)*H^2 + (224 + (448)*H + (224)*H^2)*R)*T + (112 + (224)*H + (112)*H^2 + (112 + (224)*H + (112)*H^2)*R)*T^2)*Z^6 + (4 + (8)*H + (4)*H^2 + (4 + (8)*H + (4)*H^2)*R + (8 + (16)*H + (8)*H^2 + (8 + (16)*H + (8)*H^2)*R)*T + (4 + (8)*H + (4)*H^2 + (4 + (8)*H + (4)*H^2)*R)*T^2)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-1/new.0.slack
private theorem cert_larget_smalle_1_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 3 =
      (116312 + (640768)*H + (524288)*H^2 + (124928 + (649216)*H + (524288)*H^2)*R + (757348 + (2330368)*H + (1572864)*H^2 + (774144 + (2347008)*H + (1572864)*H^2)*R)*T + (1165312 + (2738176)*H + (1572864)*H^2 + (1173504 + (2746368)*H + (1572864)*H^2)*R)*T^2 + (524288 + (1048576)*H + (524288)*H^2 + (524288 + (1048576)*H + (524288)*H^2)*R)*T^3 + (222959 + (1140544)*H + (917504)*H^2 + (233472 + (1150976)*H + (917504)*H^2)*R + (1363696 + (4116288)*H + (2752512)*H^2 + (1384448 + (4136960)*H + (2752512)*H^2)*R)*T + (2058240 + (4810752)*H + (2752512)*H^2 + (2068480 + (4820992)*H + (2752512)*H^2)*R)*T^2 + (917504 + (1835008)*H + (917504)*H^2 + (917504 + (1835008)*H + (917504)*H^2)*R)*T^3)*Z + (181958 + (870096)*H + (688128)*H^2 + (187136 + (875264)*H + (688128)*H^2)*R + (1052102 + (3116496)*H + (2064384)*H^2 + (1062400 + (3126784)*H + (2064384)*H^2)*R)*T + (1558272 + (3622656)*H + (2064384)*H^2 + (1563392 + (3627776)*H + (2064384)*H^2)*R)*T^2 + (688128 + (1376256)*H + (688128)*H^2 + (688128 + (1376256)*H + (688128)*H^2)*R)*T^3)*Z^2 + (82044 + (368764)*H + (286720)*H^2 + (83328 + (370048)*H + (286720)*H^2)*R + (450812 + (1310972)*H + (860160)*H^2 + (453376 + (1313536)*H + (860160)*H^2)*R)*T + (655488 + (1515648)*H + (860160)*H^2 + (656768 + (1516928)*H + (860160)*H^2)*R)*T^2 + (286720 + (573440)*H + (286720)*H^2 + (286720 + (573440)*H + (286720)*H^2)*R)*T^3)*Z^3 + (22088 + (93768)*H + (71680)*H^2 + (22248 + (93928)*H + (71680)*H^2)*R + (115856 + (330896)*H + (215040)*H^2 + (116176 + (331216)*H + (215040)*H^2)*R)*T + (165448 + (380488)*H + (215040)*H^2 + (165608 + (380648)*H + (215040)*H^2)*R)*T^2 + (71680 + (143360)*H + (71680)*H^2 + (71680 + (143360)*H + (71680)*H^2)*R)*T^3)*Z^4 + (3552 + (14304)*H + (10752)*H^2 + (3560 + (14312)*H + (10752)*H^2)*R + (17856 + (50112)*H + (32256)*H^2 + (17872 + (50128)*H + (32256)*H^2)*R)*T + (25056 + (57312)*H + (32256)*H^2 + (25064 + (57320)*H + (32256)*H^2)*R)*T^2 + (10752 + (21504)*H + (10752)*H^2 + (10752 + (21504)*H + (10752)*H^2)*R)*T^3)*Z^5 + (316 + (1212)*H + (896)*H^2 + (316 + (1212)*H + (896)*H^2)*R + (1528 + (4216)*H + (2688)*H^2 + (1528 + (4216)*H + (2688)*H^2)*R)*T + (2108 + (4796)*H + (2688)*H^2 + (2108 + (4796)*H + (2688)*H^2)*R)*T^2 + (896 + (1792)*H + (896)*H^2 + (896 + (1792)*H + (896)*H^2)*R)*T^3)*Z^6 + (12 + (44)*H + (32)*H^2 + (12 + (44)*H + (32)*H^2)*R + (56 + (152)*H + (96)*H^2 + (56 + (152)*H + (96)*H^2)*R)*T + (76 + (172)*H + (96)*H^2 + (76 + (172)*H + (96)*H^2)*R)*T^2 + (32 + (64)*H + (32)*H^2 + (32 + (64)*H + (32)*H^2)*R)*T^3)*Z^7) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-1/new.1.slack
private theorem cert_larget_smalle_1_new_1_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 4 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 1 4 =
      (63300 + (63280)*H + (70134 + (70144)*H)*R + (127314 + (127280)*H + (140800 + (140800)*H)*R)*T + (64000 + (64000)*H + (70656 + (70656)*H)*R)*T^2 + (115817 + (115804)*H + (124542 + (124544)*H)*R + (232172 + (232156)*H + (249472 + (249472)*H)*R)*T + (116352 + (116352)*H + (124928 + (124928)*H)*R)*T^2)*Z + (89494 + (89492)*H + (93984 + (93984)*H)*R + (179126 + (179124)*H + (188064 + (188064)*H)*R)*T + (89632 + (89632)*H + (94080 + (94080)*H)*R)*T^2)*Z^2 + (37932 + (37932)*H + (39096 + (39096)*H)*R + (75876 + (75876)*H + (78200 + (78200)*H)*R)*T + (37944 + (37944)*H + (39104 + (39104)*H)*R)*T^2)*Z^3 + (9532 + (9532)*H + (9684 + (9684)*H)*R + (19064 + (19064)*H + (19368 + (19368)*H)*R)*T + (9532 + (9532)*H + (9684 + (9684)*H)*R)*T^2)*Z^4 + (1420 + (1420)*H + (1428 + (1428)*H)*R + (2840 + (2840)*H + (2856 + (2856)*H)*R)*T + (1420 + (1420)*H + (1428 + (1428)*H)*R)*T^2)*Z^5 + (116 + (116)*H + (116 + (116)*H)*R + (232 + (232)*H + (232 + (232)*H)*R)*T + (116 + (116)*H + (116 + (116)*H)*R)*T^2)*Z^6 + (4 + (4)*H + (4 + (4)*H)*R + (8 + (8)*H + (8 + (8)*H)*R)*T + (4 + (4)*H + (4 + (4)*H)*R)*T^2)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-1/old.0.seam
private theorem cert_larget_largee_1_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 0 =
      (864484 + (792768)*H + (858112 + (786432)*H)*R + (3373276 + (3158208)*H + (3360768 + (3145728)*H)*R)*T + (4939776 + (4724736)*H + (4933632 + (4718592)*H)*R)*T^2 + (3217408 + (3145728)*H + (3217408 + (3145728)*H)*R)*T^3 + (786432 + (786432)*H + (786432 + (786432)*H)*R)*T^4 + (1772689 + (1645696)*H + (1765376 + (1638400)*H)*R + (6949008 + (6568064)*H + (6934528 + (6553600)*H)*R)*T + (10218496 + (9837568)*H + (10211328 + (9830400)*H)*R)*T^2 + (6680576 + (6553600)*H + (6680576 + (6553600)*H)*R)*T^3 + (1638400 + (1638400)*H + (1638400 + (1638400)*H)*R)*T^4)*Z + (1589790 + (1494300)*H + (1586432 + (1490944)*H)*R + (6256926 + (5970460)*H + (6250240 + (5963776)*H)*R)*T + (9235456 + (8948992)*H + (9232128 + (8945664)*H)*R)*T^2 + (6059264 + (5963776)*H + (6059264 + (5963776)*H)*R)*T^3 + (1490944 + (1490944)*H + (1490944 + (1490944)*H)*R)*T^4)*Z^2 + (814466 + (774914)*H + (813696 + (774144)*H)*R + (3216770 + (3098114)*H + (3215232 + (3096576)*H)*R)*T + (4764288 + (4645632)*H + (4763520 + (4644864)*H)*R)*T^2 + (3136128 + (3096576)*H + (3136128 + (3096576)*H)*R)*T^3 + (774144 + (774144)*H + (774144 + (774144)*H)*R)*T^4)*Z^3 + (260720 + (250968)*H + (260632 + (250880)*H)*R + (1032952 + (1003696)*H + (1032776 + (1003520)*H)*R)*T + (1534624 + (1505368)*H + (1534536 + (1505280)*H)*R)*T^2 + (1013272 + (1003520)*H + (1013272 + (1003520)*H)*R)*T^3 + (250880 + (250880)*H + (250880 + (250880)*H)*R)*T^4)*Z^4 + (53404 + (51972)*H + (53400 + (51968)*H)*R + (212176 + (207880)*H + (212168 + (207872)*H)*R)*T + (316108 + (311812)*H + (316104 + (311808)*H)*R)*T^2 + (209304 + (207872)*H + (209304 + (207872)*H)*R)*T^3 + (51968 + (51968)*H + (51968 + (51968)*H)*R)*T^4)*Z^5 + (6836 + (6720)*H + (6836 + (6720)*H)*R + (27228 + (26880)*H + (27228 + (26880)*H)*R)*T + (40668 + (40320)*H + (40668 + (40320)*H)*R)*T^2 + (26996 + (26880)*H + (26996 + (26880)*H)*R)*T^3 + (6720 + (6720)*H + (6720 + (6720)*H)*R)*T^4)*Z^6 + (500 + (496)*H + (500 + (496)*H)*R + (1996 + (1984)*H + (1996 + (1984)*H)*R)*T + (2988 + (2976)*H + (2988 + (2976)*H)*R)*T^2 + (1988 + (1984)*H + (1988 + (1984)*H)*R)*T^3 + (496 + (496)*H + (496 + (496)*H)*R)*T^4)*Z^7 + (16 + (16)*H + (16 + (16)*H)*R + (64 + (64)*H + (64 + (64)*H)*R)*T + (96 + (96)*H + (96 + (96)*H)*R)*T^2 + (64 + (64)*H + (64 + (64)*H)*R)*T^3 + (16 + (16)*H + (16 + (16)*H)*R)*T^4)*Z^8) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-1/old.1.seam
private theorem cert_larget_largee_1_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2 + (2)*H) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 1 =
      (6772 + (10194)*H + (3432)*H^2 + (3338 + (3328)*H)*R + (16496 + (23246)*H + (6760)*H^2 + (9738 + (9728)*H)*R)*T + (12800 + (16128)*H + (3328)*H^2 + (9472 + (9472)*H)*R)*T^2 + (3072 + (3072)*H + (3072 + (3072)*H)*R)*T^3 + (8661 + (13029)*H + (4370)*H^2 + (4290 + (4288)*H)*R + (21332 + (29988)*H + (8658)*H^2 + (12674 + (12672)*H)*R)*T + (16768 + (21056)*H + (4288)*H^2 + (12480 + (12480)*H)*R)*T^2 + (4096 + (4096)*H + (4096 + (4096)*H)*R)*T^3)*Z + (4470 + (6716)*H + (2246)*H^2 + (2224 + (2224)*H)*R + (11094 + (15564)*H + (4470)*H^2 + (6624 + (6624)*H)*R)*T + (8800 + (11024)*H + (2224)*H^2 + (6576 + (6576)*H)*R)*T^2 + (2176 + (2176)*H + (2176 + (2176)*H)*R)*T^3)*Z^2 + (1162 + (1744)*H + (582)*H^2 + (580 + (580)*H)*R + (2898 + (4060)*H + (1162)*H^2 + (1736 + (1736)*H)*R)*T + (2312 + (2892)*H + (580)*H^2 + (1732 + (1732)*H)*R)*T^2 + (576 + (576)*H + (576 + (576)*H)*R)*T^3)*Z^3 + (152 + (228)*H + (76)*H^2 + (76 + (76)*H)*R + (380 + (532)*H + (152)*H^2 + (228 + (228)*H)*R)*T + (304 + (380)*H + (76)*H^2 + (228 + (228)*H)*R)*T^2 + (76 + (76)*H + (76 + (76)*H)*R)*T^3)*Z^4 + (8 + (12)*H + (4)*H^2 + (4 + (4)*H)*R + (20 + (28)*H + (8)*H^2 + (12 + (12)*H)*R)*T + (16 + (20)*H + (4)*H^2 + (12 + (12)*H)*R)*T^2 + (4 + (4)*H + (4 + (4)*H)*R)*T^3)*Z^5) / (2 + (2)*H) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-1/old.2.seam
private theorem cert_larget_largee_1_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 2 =
      (54544 + (56960)*H + (58774 + (61184)*H)*R + (174880 + (179840)*H + (183200 + (188160)*H)*R)*T + (185856 + (188416)*H + (189952 + (192512)*H)*R)*T^2 + (65536 + (65536)*H + (65536 + (65536)*H)*R)*T^3 + (101197 + (104160)*H + (106414 + (109376)*H)*R + (317264 + (323296)*H + (327600 + (333632)*H)*R)*T + (330752 + (333824)*H + (335872 + (338944)*H)*R)*T^2 + (114688 + (114688)*H + (114688 + (114688)*H)*R)*T^3)*Z + (79378 + (80824)*H + (81962 + (83408)*H)*R + (244818 + (247736)*H + (249962 + (252880)*H)*R)*T + (251456 + (252928)*H + (254016 + (255488)*H)*R)*T^2 + (86016 + (86016)*H + (86016 + (86016)*H)*R)*T^3)*Z^2 + (34204 + (34554)*H + (34846 + (35196)*H)*R + (104252 + (104954)*H + (105534 + (106236)*H)*R)*T + (105888 + (106240)*H + (106528 + (106880)*H)*R)*T^2 + (35840 + (35840)*H + (35840 + (35840)*H)*R)*T^3)*Z^3 + (8758 + (8800)*H + (8838 + (8880)*H)*R + (26476 + (26560)*H + (26636 + (26720)*H)*R)*T + (26678 + (26720)*H + (26758 + (26800)*H)*R)*T^2 + (8960 + (8960)*H + (8960 + (8960)*H)*R)*T^3)*Z^4 + (1334 + (1336)*H + (1338 + (1340)*H)*R + (4012 + (4016)*H + (4020 + (4024)*H)*R)*T + (4022 + (4024)*H + (4026 + (4028)*H)*R)*T^2 + (1344 + (1344)*H + (1344 + (1344)*H)*R)*T^3)*Z^5 + (112 + (112)*H + (112 + (112)*H)*R + (336 + (336)*H + (336 + (336)*H)*R)*T + (336 + (336)*H + (336 + (336)*H)*R)*T^2 + (112 + (112)*H + (112 + (112)*H)*R)*T^3)*Z^6 + (4 + (4)*H + (4 + (4)*H)*R + (12 + (12)*H + (12 + (12)*H)*R)*T + (12 + (12)*H + (12 + (12)*H)*R)*T^2 + (4 + (4)*H + (4 + (4)*H)*R)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-1/new.0.slack
private theorem cert_larget_largee_1_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 3 =
      (116312 + (515840)*H + (124928 + (524288)*H)*R + (882276 + (2080512)*H + (899072 + (2097152)*H)*R)*T + (1939456 + (3137536)*H + (1947648 + (3145728)*H)*R)*T^2 + (1697792 + (2097152)*H + (1697792 + (2097152)*H)*R)*T^3 + (524288 + (524288)*H + (524288 + (524288)*H)*R)*T^4 + (222959 + (907072)*H + (233472 + (917504)*H)*R + (1597168 + (3649344)*H + (1617920 + (3670016)*H)*R)*T + (3442688 + (5494784)*H + (3452928 + (5505024)*H)*R)*T^2 + (2985984 + (3670016)*H + (2985984 + (3670016)*H)*R)*T^3 + (917504 + (917504)*H + (917504 + (917504)*H)*R)*T^4)*Z + (181958 + (682960)*H + (187136 + (688128)*H)*R + (1239238 + (2742224)*H + (1249536 + (2752512)*H)*R)*T + (2620672 + (4123648)*H + (2625792 + (4128768)*H)*R)*T^2 + (2251520 + (2752512)*H + (2251520 + (2752512)*H)*R)*T^3 + (688128 + (688128)*H + (688128 + (688128)*H)*R)*T^4)*Z^2 + (82044 + (285436)*H + (83328 + (286720)*H)*R + (534140 + (1144316)*H + (536704 + (1146880)*H)*R)*T + (1108864 + (1719040)*H + (1110144 + (1720320)*H)*R)*T^2 + (943488 + (1146880)*H + (943488 + (1146880)*H)*R)*T^3 + (286720 + (286720)*H + (286720 + (286720)*H)*R)*T^4)*Z^3 + (22088 + (71520)*H + (22248 + (71680)*H)*R + (138104 + (286400)*H + (138424 + (286720)*H)*R)*T + (281624 + (429920)*H + (281784 + (430080)*H)*R)*T^2 + (237288 + (286720)*H + (237288 + (286720)*H)*R)*T^3 + (71680 + (71680)*H + (71680 + (71680)*H)*R)*T^4)*Z^4 + (3552 + (10744)*H + (3560 + (10752)*H)*R + (21416 + (42992)*H + (21432 + (43008)*H)*R)*T + (42928 + (64504)*H + (42936 + (64512)*H)*R)*T^2 + (35816 + (43008)*H + (35816 + (43008)*H)*R)*T^3 + (10752 + (10752)*H + (10752 + (10752)*H)*R)*T^4)*Z^5 + (316 + (896)*H + (316 + (896)*H)*R + (1844 + (3584)*H + (1844 + (3584)*H)*R)*T + (3636 + (5376)*H + (3636 + (5376)*H)*R)*T^2 + (3004 + (3584)*H + (3004 + (3584)*H)*R)*T^3 + (896 + (896)*H + (896 + (896)*H)*R)*T^4)*Z^6 + (12 + (32)*H + (12 + (32)*H)*R + (68 + (128)*H + (68 + (128)*H)*R)*T + (132 + (192)*H + (132 + (192)*H)*R)*T^2 + (108 + (128)*H + (108 + (128)*H)*R)*T^3 + (32 + (32)*H + (32 + (32)*H)*R)*T^4)*Z^7) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-1/new.2.slack
private theorem cert_larget_largee_1_new_2_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 5 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 1 5 =
      (22128 + (17152)*H + (13674 + (8704)*H)*R + (43616 + (33536)*H + (26976 + (16896)*H)*R)*T + (21504 + (16384)*H + (13312 + (8192)*H)*R)*T^2 + (27091 + (21056)*H + (16658 + (10624)*H)*R + (53712 + (41536)*H + (33040 + (20864)*H)*R)*T + (26624 + (20480)*H + (16384 + (10240)*H)*R)*T^2)*Z + (13302 + (10384)*H + (8134 + (5216)*H)*R + (26486 + (20624)*H + (16198 + (10336)*H)*R)*T + (13184 + (10240)*H + (8064 + (5120)*H)*R)*T^2)*Z^2 + (3274 + (2572)*H + (1990 + (1288)*H)*R + (6538 + (5132)*H + (3974 + (2568)*H)*R)*T + (3264 + (2560)*H + (1984 + (1280)*H)*R)*T^2)*Z^3 + (404 + (320)*H + (244 + (160)*H)*R + (808 + (640)*H + (488 + (320)*H)*R)*T + (404 + (320)*H + (244 + (160)*H)*R)*T^2)*Z^4 + (20 + (16)*H + (12 + (8)*H)*R + (40 + (32)*H + (24 + (16)*H)*R)*T + (20 + (16)*H + (12 + (8)*H)*R)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-2/old.0.seam
private theorem cert_larget_smalle_2_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 0 =
      (864484 + (1650880)*H + (786432)*H^2 + (858112 + (1644544)*H + (786432)*H^2)*R + (2515164 + (4874432)*H + (2359296)*H^2 + (2502656 + (4861952)*H + (2359296)*H^2)*R)*T + (2437120 + (4796416)*H + (2359296)*H^2 + (2430976 + (4790272)*H + (2359296)*H^2)*R)*T^2 + (786432 + (1572864)*H + (786432)*H^2 + (786432 + (1572864)*H + (786432)*H^2)*R)*T^3 + (1772689 + (3411072)*H + (1638400)*H^2 + (1765376 + (3403776)*H + (1638400)*H^2)*R + (5183632 + (10098816)*H + (4915200)*H^2 + (5169152 + (10084352)*H + (4915200)*H^2)*R)*T + (5049344 + (9964544)*H + (4915200)*H^2 + (5042176 + (9957376)*H + (4915200)*H^2)*R)*T^2 + (1638400 + (3276800)*H + (1638400)*H^2 + (1638400 + (3276800)*H + (1638400)*H^2)*R)*T^3)*Z + (1589790 + (3080732)*H + (1490944)*H^2 + (1586432 + (3077376)*H + (1490944)*H^2)*R + (4670494 + (9143324)*H + (4472832)*H^2 + (4663808 + (9136640)*H + (4472832)*H^2)*R)*T + (4571648 + (9044480)*H + (4472832)*H^2 + (4568320 + (9041152)*H + (4472832)*H^2)*R)*T^2 + (1490944 + (2981888)*H + (1490944)*H^2 + (1490944 + (2981888)*H + (1490944)*H^2)*R)*T^3)*Z^2 + (814466 + (1588610)*H + (774144)*H^2 + (813696 + (1587840)*H + (774144)*H^2)*R + (2403074 + (4725506)*H + (2322432)*H^2 + (2401536 + (4723968)*H + (2322432)*H^2)*R)*T + (2362752 + (4685184)*H + (2322432)*H^2 + (2361984 + (4684416)*H + (2322432)*H^2)*R)*T^2 + (774144 + (1548288)*H + (774144)*H^2 + (774144 + (1548288)*H + (774144)*H^2)*R)*T^3)*Z^3 + (260720 + (511600)*H + (250880)*H^2 + (260632 + (511512)*H + (250880)*H^2)*R + (772320 + (1524960)*H + (752640)*H^2 + (772144 + (1524784)*H + (752640)*H^2)*R)*T + (762480 + (1515120)*H + (752640)*H^2 + (762392 + (1515032)*H + (752640)*H^2)*R)*T^2 + (250880 + (501760)*H + (250880)*H^2 + (250880 + (501760)*H + (250880)*H^2)*R)*T^3)*Z^4 + (53404 + (105372)*H + (51968)*H^2 + (53400 + (105368)*H + (51968)*H^2)*R + (158776 + (314680)*H + (155904)*H^2 + (158768 + (314672)*H + (155904)*H^2)*R)*T + (157340 + (313244)*H + (155904)*H^2 + (157336 + (313240)*H + (155904)*H^2)*R)*T^2 + (51968 + (103936)*H + (51968)*H^2 + (51968 + (103936)*H + (51968)*H^2)*R)*T^3)*Z^5 + (6836 + (13556)*H + (6720)*H^2 + (6836 + (13556)*H + (6720)*H^2)*R + (20392 + (40552)*H + (20160)*H^2 + (20392 + (40552)*H + (20160)*H^2)*R)*T + (20276 + (40436)*H + (20160)*H^2 + (20276 + (40436)*H + (20160)*H^2)*R)*T^2 + (6720 + (13440)*H + (6720)*H^2 + (6720 + (13440)*H + (6720)*H^2)*R)*T^3)*Z^6 + (500 + (996)*H + (496)*H^2 + (500 + (996)*H + (496)*H^2)*R + (1496 + (2984)*H + (1488)*H^2 + (1496 + (2984)*H + (1488)*H^2)*R)*T + (1492 + (2980)*H + (1488)*H^2 + (1492 + (2980)*H + (1488)*H^2)*R)*T^2 + (496 + (992)*H + (496)*H^2 + (496 + (992)*H + (496)*H^2)*R)*T^3)*Z^7 + (16 + (32)*H + (16)*H^2 + (16 + (32)*H + (16)*H^2)*R + (48 + (96)*H + (48)*H^2 + (48 + (96)*H + (48)*H^2)*R)*T + (48 + (96)*H + (48)*H^2 + (48 + (96)*H + (48)*H^2)*R)*T^2 + (16 + (32)*H + (16)*H^2 + (16 + (32)*H + (16)*H^2)*R)*T^3)*Z^8) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-2/old.1.seam
private theorem cert_larget_smalle_2_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 1 =
      (15230 + (15208)*H + (11796 + (11776)*H)*R + (29798 + (29800)*H + (23040 + (23040)*H)*R)*T + (14592 + (14592)*H + (11264 + (11264)*H)*R)*T^2 + (19095 + (19090)*H + (14724 + (14720)*H)*R + (37714 + (37714)*H + (29056 + (29056)*H)*R)*T + (18624 + (18624)*H + (14336 + (14336)*H)*R)*T^2)*Z + (9638 + (9638)*H + (7392 + (7392)*H)*R + (19158 + (19158)*H + (14688 + (14688)*H)*R)*T + (9520 + (9520)*H + (7296 + (7296)*H)*R)*T^2)*Z^2 + (2446 + (2446)*H + (1864 + (1864)*H)*R + (4882 + (4882)*H + (3720 + (3720)*H)*R)*T + (2436 + (2436)*H + (1856 + (1856)*H)*R)*T^2)*Z^3 + (312 + (312)*H + (236 + (236)*H)*R + (624 + (624)*H + (472 + (472)*H)*R)*T + (312 + (312)*H + (236 + (236)*H)*R)*T^2)*Z^4 + (16 + (16)*H + (12 + (12)*H)*R + (32 + (32)*H + (24 + (24)*H)*R)*T + (16 + (16)*H + (12 + (12)*H)*R)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-2/old.2.seam
private theorem cert_larget_smalle_2_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 2 =
      (63002 + (132640)*H + (69632)*H^2 + (67232 + (136864)*H + (69632)*H^2)*R + (124288 + (259456)*H + (135168)*H^2 + (132608 + (267776)*H + (135168)*H^2)*R)*T + (61440 + (126976)*H + (65536)*H^2 + (65536 + (131072)*H + (65536)*H^2)*R)*T^2 + (111631 + (231440)*H + (119808)*H^2 + (116848 + (236656)*H + (119808)*H^2)*R + (221088 + (455584)*H + (234496)*H^2 + (231424 + (465920)*H + (234496)*H^2)*R)*T + (109568 + (224256)*H + (114688)*H^2 + (114688 + (229376)*H + (114688)*H^2)*R)*T^2)*Z + (84546 + (173122)*H + (88576)*H^2 + (87130 + (175706)*H + (88576)*H^2)*R + (167976 + (342568)*H + (174592)*H^2 + (173120 + (347712)*H + (174592)*H^2)*R)*T + (83456 + (169472)*H + (86016)*H^2 + (86016 + (172032)*H + (86016)*H^2)*R)*T^2)*Z^2 + (35488 + (71968)*H + (36480)*H^2 + (36130 + (72610)*H + (36480)*H^2)*R + (70686 + (143006)*H + (72320)*H^2 + (71968 + (144288)*H + (72320)*H^2)*R)*T + (35200 + (71040)*H + (35840)*H^2 + (35840 + (71680)*H + (35840)*H^2)*R)*T^2)*Z^3 + (8918 + (17958)*H + (9040)*H^2 + (8998 + (18038)*H + (9040)*H^2)*R + (17798 + (35798)*H + (18000)*H^2 + (17958 + (35958)*H + (18000)*H^2)*R)*T + (8880 + (17840)*H + (8960)*H^2 + (8960 + (17920)*H + (8960)*H^2)*R)*T^2)*Z^4 + (1342 + (2690)*H + (1348)*H^2 + (1346 + (2694)*H + (1348)*H^2)*R + (2682 + (5374)*H + (2692)*H^2 + (2690 + (5382)*H + (2692)*H^2)*R)*T + (1340 + (2684)*H + (1344)*H^2 + (1344 + (2688)*H + (1344)*H^2)*R)*T^2)*Z^5 + (112 + (224)*H + (112)*H^2 + (112 + (224)*H + (112)*H^2)*R + (224 + (448)*H + (224)*H^2 + (224 + (448)*H + (224)*H^2)*R)*T + (112 + (224)*H + (112)*H^2 + (112 + (224)*H + (112)*H^2)*R)*T^2)*Z^6 + (4 + (8)*H + (4)*H^2 + (4 + (8)*H + (4)*H^2)*R + (8 + (16)*H + (8)*H^2 + (8 + (16)*H + (8)*H^2)*R)*T + (4 + (8)*H + (4)*H^2 + (4 + (8)*H + (4)*H^2)*R)*T^2)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-2/new.0.slack
private theorem cert_larget_smalle_2_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 3 =
      (116312 + (640768)*H + (524288)*H^2 + (124928 + (649216)*H + (524288)*H^2)*R + (757348 + (2330368)*H + (1572864)*H^2 + (774144 + (2347008)*H + (1572864)*H^2)*R)*T + (1165312 + (2738176)*H + (1572864)*H^2 + (1173504 + (2746368)*H + (1572864)*H^2)*R)*T^2 + (524288 + (1048576)*H + (524288)*H^2 + (524288 + (1048576)*H + (524288)*H^2)*R)*T^3 + (222959 + (1140544)*H + (917504)*H^2 + (233472 + (1150976)*H + (917504)*H^2)*R + (1363696 + (4116288)*H + (2752512)*H^2 + (1384448 + (4136960)*H + (2752512)*H^2)*R)*T + (2058240 + (4810752)*H + (2752512)*H^2 + (2068480 + (4820992)*H + (2752512)*H^2)*R)*T^2 + (917504 + (1835008)*H + (917504)*H^2 + (917504 + (1835008)*H + (917504)*H^2)*R)*T^3)*Z + (181958 + (870096)*H + (688128)*H^2 + (187136 + (875264)*H + (688128)*H^2)*R + (1052102 + (3116496)*H + (2064384)*H^2 + (1062400 + (3126784)*H + (2064384)*H^2)*R)*T + (1558272 + (3622656)*H + (2064384)*H^2 + (1563392 + (3627776)*H + (2064384)*H^2)*R)*T^2 + (688128 + (1376256)*H + (688128)*H^2 + (688128 + (1376256)*H + (688128)*H^2)*R)*T^3)*Z^2 + (82044 + (368764)*H + (286720)*H^2 + (83328 + (370048)*H + (286720)*H^2)*R + (450812 + (1310972)*H + (860160)*H^2 + (453376 + (1313536)*H + (860160)*H^2)*R)*T + (655488 + (1515648)*H + (860160)*H^2 + (656768 + (1516928)*H + (860160)*H^2)*R)*T^2 + (286720 + (573440)*H + (286720)*H^2 + (286720 + (573440)*H + (286720)*H^2)*R)*T^3)*Z^3 + (22088 + (93768)*H + (71680)*H^2 + (22248 + (93928)*H + (71680)*H^2)*R + (115856 + (330896)*H + (215040)*H^2 + (116176 + (331216)*H + (215040)*H^2)*R)*T + (165448 + (380488)*H + (215040)*H^2 + (165608 + (380648)*H + (215040)*H^2)*R)*T^2 + (71680 + (143360)*H + (71680)*H^2 + (71680 + (143360)*H + (71680)*H^2)*R)*T^3)*Z^4 + (3552 + (14304)*H + (10752)*H^2 + (3560 + (14312)*H + (10752)*H^2)*R + (17856 + (50112)*H + (32256)*H^2 + (17872 + (50128)*H + (32256)*H^2)*R)*T + (25056 + (57312)*H + (32256)*H^2 + (25064 + (57320)*H + (32256)*H^2)*R)*T^2 + (10752 + (21504)*H + (10752)*H^2 + (10752 + (21504)*H + (10752)*H^2)*R)*T^3)*Z^5 + (316 + (1212)*H + (896)*H^2 + (316 + (1212)*H + (896)*H^2)*R + (1528 + (4216)*H + (2688)*H^2 + (1528 + (4216)*H + (2688)*H^2)*R)*T + (2108 + (4796)*H + (2688)*H^2 + (2108 + (4796)*H + (2688)*H^2)*R)*T^2 + (896 + (1792)*H + (896)*H^2 + (896 + (1792)*H + (896)*H^2)*R)*T^3)*Z^6 + (12 + (44)*H + (32)*H^2 + (12 + (44)*H + (32)*H^2)*R + (56 + (152)*H + (96)*H^2 + (56 + (152)*H + (96)*H^2)*R)*T + (76 + (172)*H + (96)*H^2 + (76 + (172)*H + (96)*H^2)*R)*T^2 + (32 + (64)*H + (32)*H^2 + (32 + (64)*H + (32)*H^2)*R)*T^3)*Z^7) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-smalle-2/new.1.slack
private theorem cert_larget_smalle_2_new_1_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 4 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) 2 4 =
      (46394 + (46384)*H + (53228 + (53248)*H)*R + (94034 + (94000)*H + (107520 + (107520)*H)*R)*T + (47616 + (47616)*H + (54272 + (54272)*H)*R)*T^2 + (94951 + (94940)*H + (103676 + (103680)*H)*R + (190828 + (190812)*H + (208128 + (208128)*H)*R)*T + (95872 + (95872)*H + (104448 + (104448)*H)*R)*T^2)*Z + (79158 + (79156)*H + (83648 + (83648)*H)*R + (158550 + (158548)*H + (167488 + (167488)*H)*R)*T + (79392 + (79392)*H + (83840 + (83840)*H)*R)*T^2)*Z^2 + (35364 + (35364)*H + (36528 + (36528)*H)*R + (70748 + (70748)*H + (73072 + (73072)*H)*R)*T + (35384 + (35384)*H + (36544 + (36544)*H)*R)*T^2)*Z^3 + (9212 + (9212)*H + (9364 + (9364)*H)*R + (18424 + (18424)*H + (18728 + (18728)*H)*R)*T + (9212 + (9212)*H + (9364 + (9364)*H)*R)*T^2)*Z^4 + (1404 + (1404)*H + (1412 + (1412)*H)*R + (2808 + (2808)*H + (2824 + (2824)*H)*R)*T + (1404 + (1404)*H + (1412 + (1412)*H)*R)*T^2)*Z^5 + (116 + (116)*H + (116 + (116)*H)*R + (232 + (232)*H + (232 + (232)*H)*R)*T + (116 + (116)*H + (116 + (116)*H)*R)*T^2)*Z^6 + (4 + (4)*H + (4 + (4)*H)*R + (8 + (8)*H + (8 + (8)*H)*R)*T + (4 + (4)*H + (4 + (4)*H)*R)*T^2)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-2/old.0.seam
private theorem cert_larget_largee_2_old_0_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 0 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 0 =
      (864484 + (792768)*H + (858112 + (786432)*H)*R + (3373276 + (3158208)*H + (3360768 + (3145728)*H)*R)*T + (4939776 + (4724736)*H + (4933632 + (4718592)*H)*R)*T^2 + (3217408 + (3145728)*H + (3217408 + (3145728)*H)*R)*T^3 + (786432 + (786432)*H + (786432 + (786432)*H)*R)*T^4 + (1772689 + (1645696)*H + (1765376 + (1638400)*H)*R + (6949008 + (6568064)*H + (6934528 + (6553600)*H)*R)*T + (10218496 + (9837568)*H + (10211328 + (9830400)*H)*R)*T^2 + (6680576 + (6553600)*H + (6680576 + (6553600)*H)*R)*T^3 + (1638400 + (1638400)*H + (1638400 + (1638400)*H)*R)*T^4)*Z + (1589790 + (1494300)*H + (1586432 + (1490944)*H)*R + (6256926 + (5970460)*H + (6250240 + (5963776)*H)*R)*T + (9235456 + (8948992)*H + (9232128 + (8945664)*H)*R)*T^2 + (6059264 + (5963776)*H + (6059264 + (5963776)*H)*R)*T^3 + (1490944 + (1490944)*H + (1490944 + (1490944)*H)*R)*T^4)*Z^2 + (814466 + (774914)*H + (813696 + (774144)*H)*R + (3216770 + (3098114)*H + (3215232 + (3096576)*H)*R)*T + (4764288 + (4645632)*H + (4763520 + (4644864)*H)*R)*T^2 + (3136128 + (3096576)*H + (3136128 + (3096576)*H)*R)*T^3 + (774144 + (774144)*H + (774144 + (774144)*H)*R)*T^4)*Z^3 + (260720 + (250968)*H + (260632 + (250880)*H)*R + (1032952 + (1003696)*H + (1032776 + (1003520)*H)*R)*T + (1534624 + (1505368)*H + (1534536 + (1505280)*H)*R)*T^2 + (1013272 + (1003520)*H + (1013272 + (1003520)*H)*R)*T^3 + (250880 + (250880)*H + (250880 + (250880)*H)*R)*T^4)*Z^4 + (53404 + (51972)*H + (53400 + (51968)*H)*R + (212176 + (207880)*H + (212168 + (207872)*H)*R)*T + (316108 + (311812)*H + (316104 + (311808)*H)*R)*T^2 + (209304 + (207872)*H + (209304 + (207872)*H)*R)*T^3 + (51968 + (51968)*H + (51968 + (51968)*H)*R)*T^4)*Z^5 + (6836 + (6720)*H + (6836 + (6720)*H)*R + (27228 + (26880)*H + (27228 + (26880)*H)*R)*T + (40668 + (40320)*H + (40668 + (40320)*H)*R)*T^2 + (26996 + (26880)*H + (26996 + (26880)*H)*R)*T^3 + (6720 + (6720)*H + (6720 + (6720)*H)*R)*T^4)*Z^6 + (500 + (496)*H + (500 + (496)*H)*R + (1996 + (1984)*H + (1996 + (1984)*H)*R)*T + (2988 + (2976)*H + (2988 + (2976)*H)*R)*T^2 + (1988 + (1984)*H + (1988 + (1984)*H)*R)*T^3 + (496 + (496)*H + (496 + (496)*H)*R)*T^4)*Z^7 + (16 + (16)*H + (16 + (16)*H)*R + (64 + (64)*H + (64 + (64)*H)*R)*T + (96 + (96)*H + (96 + (96)*H)*R)*T^2 + (64 + (64)*H + (64 + (64)*H)*R)*T^3 + (16 + (16)*H + (16 + (16)*H)*R)*T^4)*Z^8) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-2/old.1.seam
private theorem cert_larget_largee_2_old_1_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2 + (2)*H) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 1 =
      (15230 + (18642)*H + (3432)*H^2 + (11796 + (11776)*H)*R + (41594 + (48334)*H + (6760)*H^2 + (34836 + (34816)*H)*R)*T + (37632 + (40960)*H + (3328)*H^2 + (34304 + (34304)*H)*R)*T^2 + (11264 + (11264)*H + (11264 + (11264)*H)*R)*T^3 + (19095 + (23461)*H + (4370)*H^2 + (14724 + (14720)*H)*R + (52438 + (61092)*H + (8658)*H^2 + (43780 + (43776)*H)*R)*T + (47680 + (51968)*H + (4288)*H^2 + (43392 + (43392)*H)*R)*T^2 + (14336 + (14336)*H + (14336 + (14336)*H)*R)*T^3)*Z + (9638 + (11884)*H + (2246)*H^2 + (7392 + (7392)*H)*R + (26550 + (31020)*H + (4470)*H^2 + (22080 + (22080)*H)*R)*T + (24208 + (26432)*H + (2224)*H^2 + (21984 + (21984)*H)*R)*T^2 + (7296 + (7296)*H + (7296 + (7296)*H)*R)*T^3)*Z^2 + (2446 + (3028)*H + (582)*H^2 + (1864 + (1864)*H)*R + (6746 + (7908)*H + (1162)*H^2 + (5584 + (5584)*H)*R)*T + (6156 + (6736)*H + (580)*H^2 + (5576 + (5576)*H)*R)*T^2 + (1856 + (1856)*H + (1856 + (1856)*H)*R)*T^3)*Z^3 + (312 + (388)*H + (76)*H^2 + (236 + (236)*H)*R + (860 + (1012)*H + (152)*H^2 + (708 + (708)*H)*R)*T + (784 + (860)*H + (76)*H^2 + (708 + (708)*H)*R)*T^2 + (236 + (236)*H + (236 + (236)*H)*R)*T^3)*Z^4 + (16 + (20)*H + (4)*H^2 + (12 + (12)*H)*R + (44 + (52)*H + (8)*H^2 + (36 + (36)*H)*R)*T + (40 + (44)*H + (4)*H^2 + (36 + (36)*H)*R)*T^2 + (12 + (12)*H + (12 + (12)*H)*R)*T^3)*Z^5) / (2 + (2)*H) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-2/old.2.seam
private theorem cert_larget_largee_2_old_2_seam (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 2 =
      (54544 + (56960)*H + (58774 + (61184)*H)*R + (174880 + (179840)*H + (183200 + (188160)*H)*R)*T + (185856 + (188416)*H + (189952 + (192512)*H)*R)*T^2 + (65536 + (65536)*H + (65536 + (65536)*H)*R)*T^3 + (101197 + (104160)*H + (106414 + (109376)*H)*R + (317264 + (323296)*H + (327600 + (333632)*H)*R)*T + (330752 + (333824)*H + (335872 + (338944)*H)*R)*T^2 + (114688 + (114688)*H + (114688 + (114688)*H)*R)*T^3)*Z + (79378 + (80824)*H + (81962 + (83408)*H)*R + (244818 + (247736)*H + (249962 + (252880)*H)*R)*T + (251456 + (252928)*H + (254016 + (255488)*H)*R)*T^2 + (86016 + (86016)*H + (86016 + (86016)*H)*R)*T^3)*Z^2 + (34204 + (34554)*H + (34846 + (35196)*H)*R + (104252 + (104954)*H + (105534 + (106236)*H)*R)*T + (105888 + (106240)*H + (106528 + (106880)*H)*R)*T^2 + (35840 + (35840)*H + (35840 + (35840)*H)*R)*T^3)*Z^3 + (8758 + (8800)*H + (8838 + (8880)*H)*R + (26476 + (26560)*H + (26636 + (26720)*H)*R)*T + (26678 + (26720)*H + (26758 + (26800)*H)*R)*T^2 + (8960 + (8960)*H + (8960 + (8960)*H)*R)*T^3)*Z^4 + (1334 + (1336)*H + (1338 + (1340)*H)*R + (4012 + (4016)*H + (4020 + (4024)*H)*R)*T + (4022 + (4024)*H + (4026 + (4028)*H)*R)*T^2 + (1344 + (1344)*H + (1344 + (1344)*H)*R)*T^3)*Z^5 + (112 + (112)*H + (112 + (112)*H)*R + (336 + (336)*H + (336 + (336)*H)*R)*T + (336 + (336)*H + (336 + (336)*H)*R)*T^2 + (112 + (112)*H + (112 + (112)*H)*R)*T^3)*Z^6 + (4 + (4)*H + (4 + (4)*H)*R + (12 + (12)*H + (12 + (12)*H)*R)*T + (12 + (12)*H + (12 + (12)*H)*R)*T^2 + (4 + (4)*H + (4 + (4)*H)*R)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-2/new.0.slack
private theorem cert_larget_largee_2_new_0_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 3 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (4) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 3 =
      (116312 + (515840)*H + (124928 + (524288)*H)*R + (882276 + (2080512)*H + (899072 + (2097152)*H)*R)*T + (1939456 + (3137536)*H + (1947648 + (3145728)*H)*R)*T^2 + (1697792 + (2097152)*H + (1697792 + (2097152)*H)*R)*T^3 + (524288 + (524288)*H + (524288 + (524288)*H)*R)*T^4 + (222959 + (907072)*H + (233472 + (917504)*H)*R + (1597168 + (3649344)*H + (1617920 + (3670016)*H)*R)*T + (3442688 + (5494784)*H + (3452928 + (5505024)*H)*R)*T^2 + (2985984 + (3670016)*H + (2985984 + (3670016)*H)*R)*T^3 + (917504 + (917504)*H + (917504 + (917504)*H)*R)*T^4)*Z + (181958 + (682960)*H + (187136 + (688128)*H)*R + (1239238 + (2742224)*H + (1249536 + (2752512)*H)*R)*T + (2620672 + (4123648)*H + (2625792 + (4128768)*H)*R)*T^2 + (2251520 + (2752512)*H + (2251520 + (2752512)*H)*R)*T^3 + (688128 + (688128)*H + (688128 + (688128)*H)*R)*T^4)*Z^2 + (82044 + (285436)*H + (83328 + (286720)*H)*R + (534140 + (1144316)*H + (536704 + (1146880)*H)*R)*T + (1108864 + (1719040)*H + (1110144 + (1720320)*H)*R)*T^2 + (943488 + (1146880)*H + (943488 + (1146880)*H)*R)*T^3 + (286720 + (286720)*H + (286720 + (286720)*H)*R)*T^4)*Z^3 + (22088 + (71520)*H + (22248 + (71680)*H)*R + (138104 + (286400)*H + (138424 + (286720)*H)*R)*T + (281624 + (429920)*H + (281784 + (430080)*H)*R)*T^2 + (237288 + (286720)*H + (237288 + (286720)*H)*R)*T^3 + (71680 + (71680)*H + (71680 + (71680)*H)*R)*T^4)*Z^4 + (3552 + (10744)*H + (3560 + (10752)*H)*R + (21416 + (42992)*H + (21432 + (43008)*H)*R)*T + (42928 + (64504)*H + (42936 + (64512)*H)*R)*T^2 + (35816 + (43008)*H + (35816 + (43008)*H)*R)*T^3 + (10752 + (10752)*H + (10752 + (10752)*H)*R)*T^4)*Z^5 + (316 + (896)*H + (316 + (896)*H)*R + (1844 + (3584)*H + (1844 + (3584)*H)*R)*T + (3636 + (5376)*H + (3636 + (5376)*H)*R)*T^2 + (3004 + (3584)*H + (3004 + (3584)*H)*R)*T^3 + (896 + (896)*H + (896 + (896)*H)*R)*T^4)*Z^6 + (12 + (32)*H + (12 + (32)*H)*R + (68 + (128)*H + (68 + (128)*H)*R)*T + (132 + (192)*H + (132 + (192)*H)*R)*T^2 + (108 + (128)*H + (108 + (128)*H)*R)*T^3 + (32 + (32)*H + (32 + (32)*H)*R)*T^4)*Z^7) / (4) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- larget-largee-2/new.2.slack
private theorem cert_larget_largee_2_new_2_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 5 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) 2 5 =
      (22128 + (17152)*H + (13674 + (8704)*H)*R + (43616 + (33536)*H + (26976 + (16896)*H)*R)*T + (21504 + (16384)*H + (13312 + (8192)*H)*R)*T^2 + (27091 + (21056)*H + (16658 + (10624)*H)*R + (53712 + (41536)*H + (33040 + (20864)*H)*R)*T + (26624 + (20480)*H + (16384 + (10240)*H)*R)*T^2)*Z + (13302 + (10384)*H + (8134 + (5216)*H)*R + (26486 + (20624)*H + (16198 + (10336)*H)*R)*T + (13184 + (10240)*H + (8064 + (5120)*H)*R)*T^2)*Z^2 + (3274 + (2572)*H + (1990 + (1288)*H)*R + (6538 + (5132)*H + (3974 + (2568)*H)*R)*T + (3264 + (2560)*H + (1984 + (1280)*H)*R)*T^2)*Z^3 + (404 + (320)*H + (244 + (160)*H)*R + (808 + (640)*H + (488 + (320)*H)*R)*T + (404 + (320)*H + (244 + (160)*H)*R)*T^2)*Z^4 + (20 + (16)*H + (12 + (8)*H)*R + (40 + (32)*H + (24 + (16)*H)*R)*T + (20 + (16)*H + (12 + (8)*H)*R)*T^2)*Z^5) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- small-e-exception/new.2.slack
private theorem cert_small_e_exception_new_2_slack (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ margin (Z+4) (8*(H+1)*(T+1)+U) (H+1) ((H+1)*(T+1)) 0 0 5 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : margin (Z+4) (8*(H+1)*(T+1)+U) (H+1) ((H+1)*(T+1)) 0 0 5 =
      (466 + (124)*U + (8)*U^2 + (1196 + (220)*U + (8)*U^2)*H + (992 + (96)*U)*H^2 + (256)*H^3 + (876 + (116)*U + (2284 + (212)*U)*H + (1920 + (96)*U)*H^2 + (512)*H^3)*T + (416 + (1088)*H + (928)*H^2 + (256)*H^3)*T^2 + (109 + (30)*U + (2)*U^2 + (284 + (54)*U + (2)*U^2)*H + (240 + (24)*U)*H^2 + (64)*H^3 + (204 + (28)*U + (540 + (52)*U)*H + (464 + (24)*U)*H^2 + (128)*H^3)*T + (96 + (256)*H + (224)*H^2 + (64)*H^3)*T^2)*Z) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- concavity-1/new/lower
private theorem cert_concavity_1_new_lower (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) 1 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) 1 1 =
      (63300 + (70134)*R + (197448 + (210934)*R)*T + (204800 + (211456)*R)*T^2 + (70656 + (70656)*R)*T^3 + (115817 + (124542)*R + (356714 + (374014)*R)*T + (365824 + (374400)*R)*T^2 + (124928 + (124928)*R)*T^3)*Z + (89494 + (93984)*R + (273110 + (282048)*R)*T + (277696 + (282144)*R)*T^2 + (94080 + (94080)*R)*T^3)*Z^2 + (37932 + (39096)*R + (114972 + (117296)*R)*T + (116144 + (117304)*R)*T^2 + (39104 + (39104)*R)*T^3)*Z^3 + (9532 + (9684)*R + (28748 + (29052)*R)*T + (28900 + (29052)*R)*T^2 + (9684 + (9684)*R)*T^3)*Z^4 + (1420 + (1428)*R + (4268 + (4284)*R)*T + (4276 + (4284)*R)*T^2 + (1428 + (1428)*R)*T^3)*Z^5 + (116 + (116)*R + (348 + (348)*R)*T + (348 + (348)*R)*T^2 + (116 + (116)*R)*T^3)*Z^6 + (4 + (4)*R + (12 + (12)*R)*T + (12 + (12)*R)*T^2 + (4 + (4)*R)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- concavity-1/new/upper
private theorem cert_concavity_1_new_upper (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (cap (Z+4) (2*(Z+4)^2*(T+1)) (R+1)) 1 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (cap (Z+4) (2*(Z+4)^2*(T+1)) (R+1)) 1 =
      (63300 + (126580)*R + (63280)*R^2 + (253894 + (507734)*R + (253840)*R^2)*T + (381874 + (763714)*R + (381840)*R^2)*T^2 + (255280 + (510560)*R + (255280)*R^2)*T^3 + (64000 + (128000)*R + (64000)*R^2)*T^4 + (115817 + (231621)*R + (115804)*R^2 + (463793 + (927557)*R + (463764)*R^2)*T + (696484 + (1392952)*R + (696468)*R^2)*T^2 + (464860 + (929720)*R + (464860)*R^2)*T^3 + (116352 + (232704)*R + (116352)*R^2)*T^4)*Z + (89494 + (178986)*R + (89492)*R^2 + (358112 + (716220)*R + (358108)*R^2)*T + (537374 + (1074746)*R + (537372)*R^2)*T^2 + (358388 + (716776)*R + (358388)*R^2)*T^3 + (89632 + (179264)*R + (89632)*R^2)*T^4)*Z^2 + (37932 + (75864)*R + (37932)*R^2 + (151740 + (303480)*R + (151740)*R^2)*T + (227628 + (455256)*R + (227628)*R^2)*T^2 + (151764 + (303528)*R + (151764)*R^2)*T^3 + (37944 + (75888)*R + (37944)*R^2)*T^4)*Z^3 + (9532 + (19064)*R + (9532)*R^2 + (38128 + (76256)*R + (38128)*R^2)*T + (57192 + (114384)*R + (57192)*R^2)*T^2 + (38128 + (76256)*R + (38128)*R^2)*T^3 + (9532 + (19064)*R + (9532)*R^2)*T^4)*Z^4 + (1420 + (2840)*R + (1420)*R^2 + (5680 + (11360)*R + (5680)*R^2)*T + (8520 + (17040)*R + (8520)*R^2)*T^2 + (5680 + (11360)*R + (5680)*R^2)*T^3 + (1420 + (2840)*R + (1420)*R^2)*T^4)*Z^5 + (116 + (232)*R + (116)*R^2 + (464 + (928)*R + (464)*R^2)*T + (696 + (1392)*R + (696)*R^2)*T^2 + (464 + (928)*R + (464)*R^2)*T^3 + (116 + (232)*R + (116)*R^2)*T^4)*Z^6 + (4 + (8)*R + (4)*R^2 + (16 + (32)*R + (16)*R^2)*T + (24 + (48)*R + (24)*R^2)*T^2 + (16 + (32)*R + (16)*R^2)*T^3 + (4 + (8)*R + (4)*R^2)*T^4)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- concavity-2/new/lower
private theorem cert_concavity_2_new_lower (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) 1 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) 1 2 =
      (46394 + (53228)*R + (147262 + (160748)*R)*T + (155136 + (161792)*R)*T^2 + (54272 + (54272)*R)*T^3 + (94951 + (103676)*R + (294504 + (311804)*R)*T + (304000 + (312576)*R)*T^2 + (104448 + (104448)*R)*T^3)*Z + (79158 + (83648)*R + (242198 + (251136)*R)*T + (246880 + (251328)*R)*T^2 + (83840 + (83840)*R)*T^3)*Z^2 + (35364 + (36528)*R + (107276 + (109600)*R)*T + (108456 + (109616)*R)*T^2 + (36544 + (36544)*R)*T^3)*Z^3 + (9212 + (9364)*R + (27788 + (28092)*R)*T + (27940 + (28092)*R)*T^2 + (9364 + (9364)*R)*T^3)*Z^4 + (1404 + (1412)*R + (4220 + (4236)*R)*T + (4228 + (4236)*R)*T^2 + (1412 + (1412)*R)*T^3)*Z^5 + (116 + (116)*R + (348 + (348)*R)*T + (348 + (348)*R)*T^2 + (116 + (116)*R)*T^3)*Z^6 + (4 + (4)*R + (12 + (12)*R)*T + (12 + (12)*R)*T^2 + (4 + (4)*R)*T^3)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)


-- concavity-2/new/upper
private theorem cert_concavity_2_new_upper (Z T R H U : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H) (hU : 0 ≤ U) :
    0 ≤ second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (cap (Z+4) (2*(Z+4)^2*(T+1)) (R+1)) 2 := by
  have hz : Z+4 ≠ 0 := by linarith
  have ht : T+1 ≠ 0 := by linarith
  have hr : R+1 ≠ 0 := by linarith
  have hh : H+1 ≠ 0 := by linarith
  have hden : (0 : ℚ) < (2) := by positivity
  have identity : second (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (cap (Z+4) (2*(Z+4)^2*(T+1)) (R+1)) 2 =
      (46394 + (92778)*R + (46384)*R^2 + (186812 + (373580)*R + (186768)*R^2)*T + (282034 + (564034)*R + (282000)*R^2)*T^2 + (189232 + (378464)*R + (189232)*R^2)*T^3 + (47616 + (95232)*R + (47616)*R^2)*T^4 + (94951 + (189891)*R + (94940)*R^2 + (380719 + (761411)*R + (380692)*R^2)*T + (572452 + (1144888)*R + (572436)*R^2)*T^2 + (382556 + (765112)*R + (382556)*R^2)*T^3 + (95872 + (191744)*R + (95872)*R^2)*T^4)*Z + (79158 + (158314)*R + (79156)*R^2 + (316864 + (633724)*R + (316860)*R^2)*T + (475646 + (951290)*R + (475644)*R^2)*T^2 + (317332 + (634664)*R + (317332)*R^2)*T^3 + (79392 + (158784)*R + (79392)*R^2)*T^4)*Z^2 + (35364 + (70728)*R + (35364)*R^2 + (141476 + (282952)*R + (141476)*R^2)*T + (212244 + (424488)*R + (212244)*R^2)*T^2 + (141516 + (283032)*R + (141516)*R^2)*T^3 + (35384 + (70768)*R + (35384)*R^2)*T^4)*Z^3 + (9212 + (18424)*R + (9212)*R^2 + (36848 + (73696)*R + (36848)*R^2)*T + (55272 + (110544)*R + (55272)*R^2)*T^2 + (36848 + (73696)*R + (36848)*R^2)*T^3 + (9212 + (18424)*R + (9212)*R^2)*T^4)*Z^4 + (1404 + (2808)*R + (1404)*R^2 + (5616 + (11232)*R + (5616)*R^2)*T + (8424 + (16848)*R + (8424)*R^2)*T^2 + (5616 + (11232)*R + (5616)*R^2)*T^3 + (1404 + (2808)*R + (1404)*R^2)*T^4)*Z^5 + (116 + (232)*R + (116)*R^2 + (464 + (928)*R + (464)*R^2)*T + (696 + (1392)*R + (696)*R^2)*T^2 + (464 + (928)*R + (464)*R^2)*T^3 + (116 + (232)*R + (116)*R^2)*T^4)*Z^6 + (4 + (8)*R + (4)*R^2 + (16 + (32)*R + (16)*R^2)*T + (24 + (48)*R + (24)*R^2)*T^2 + (16 + (32)*R + (16)*R^2)*T^3 + (4 + (8)*R + (4)*R^2)*T^4)*Z^7) / (2) := by
    norm_num [qHead, qNewHead, qModulus, qMask, qMass, qTerminal, qPeak, qSeam, qSlack, margin, smallTZero, smallTPositive, largeTZero, largeTPositive, cap, bend, second, Fin.sum_univ_succ]
    <;> field_simp [hz, ht, hr, hh, ne_of_gt hden] <;> ring
  rw [identity]
  exact div_nonneg (by positivity) (le_of_lt hden)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
