/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch48
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch48
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch48

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower48 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    136, 1, 0, 0, 0, 0, 0, 0, 0;
    438, 137, 1, 0, 0, 0, 0, 0, 0;
    229, 225, 131, 1, 0, 0, 0, 0, 0;
    568, 237, 903, 772, 1, 0, 0, 0, 0;
    123, 589, 142, 842, 511, 1, 0, 0, 0;
    559, 504, 248, 581, 625, 445, 1, 0, 0;
    149, 88, 315, 536, 832, 64, 42, 1, 0;
    918, 683, 199, 688, 183, 165, 383, 626, 1]

private def firstUpper48 : Matrix (Fin 9) (Fin 9) F :=
  !![974, 351, 842, 15, 519, 39, 907, 395, 928;
    0, 178, 936, 717, 405, 718, 417, 576, 643;
    0, 0, 728, 62, 993, 957, 952, 354, 742;
    0, 0, 0, 564, 520, 275, 977, 465, 981;
    0, 0, 0, 0, 626, 940, 729, 623, 1002;
    0, 0, 0, 0, 0, 317, 77, 256, 716;
    0, 0, 0, 0, 0, 0, 746, 112, 882;
    0, 0, 0, 0, 0, 0, 0, 116, 851;
    0, 0, 0, 0, 0, 0, 0, 0, 392]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt48 : residualMinor (48 : F) 0 = firstValue 48 := by
  apply value_of_factors firstLower48 firstUpper48
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower48 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    759, 1, 0, 0, 0, 0, 0, 0, 0;
    717, 339, 1, 0, 0, 0, 0, 0, 0;
    103, 661, 557, 1, 0, 0, 0, 0, 0;
    514, 506, 812, 540, 1, 0, 0, 0, 0;
    189, 326, 887, 196, 739, 1, 0, 0, 0;
    266, 371, 592, 484, 51, 409, 1, 0, 0;
    756, 114, 715, 648, 939, 76, 752, 1, 0;
    645, 789, 640, 27, 144, 71, 464, 675, 1]

private def secondUpper48 : Matrix (Fin 9) (Fin 9) F :=
  !![936, 831, 332, 553, 223, 685, 965, 399, 289;
    0, 387, 684, 756, 614, 697, 770, 678, 328;
    0, 0, 593, 972, 519, 431, 858, 709, 317;
    0, 0, 0, 620, 39, 23, 832, 234, 947;
    0, 0, 0, 0, 402, 765, 273, 796, 422;
    0, 0, 0, 0, 0, 270, 175, 498, 894;
    0, 0, 0, 0, 0, 0, 856, 424, 120;
    0, 0, 0, 0, 0, 0, 0, 288, 185;
    0, 0, 0, 0, 0, 0, 0, 0, 63]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt48 : residualMinor (48 : F) 1 = secondValue 48 := by
  apply value_of_factors secondLower48 secondUpper48
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower49 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    388, 1, 0, 0, 0, 0, 0, 0, 0;
    157, 627, 1, 0, 0, 0, 0, 0, 0;
    963, 478, 127, 1, 0, 0, 0, 0, 0;
    895, 268, 496, 577, 1, 0, 0, 0, 0;
    671, 304, 205, 283, 125, 1, 0, 0, 0;
    743, 421, 103, 585, 669, 904, 1, 0, 0;
    252, 489, 304, 79, 754, 462, 78, 1, 0;
    207, 893, 541, 519, 560, 864, 283, 499, 1]

private def firstUpper49 : Matrix (Fin 9) (Fin 9) F :=
  !![51, 437, 198, 299, 753, 782, 226, 643, 155;
    0, 862, 283, 411, 334, 511, 933, 278, 655;
    0, 0, 290, 217, 807, 546, 697, 864, 820;
    0, 0, 0, 319, 261, 787, 705, 581, 658;
    0, 0, 0, 0, 925, 536, 607, 158, 306;
    0, 0, 0, 0, 0, 738, 779, 731, 36;
    0, 0, 0, 0, 0, 0, 541, 134, 826;
    0, 0, 0, 0, 0, 0, 0, 930, 170;
    0, 0, 0, 0, 0, 0, 0, 0, 597]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt49 : residualMinor (49 : F) 0 = firstValue 49 := by
  apply value_of_factors firstLower49 firstUpper49
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower49 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    365, 1, 0, 0, 0, 0, 0, 0, 0;
    438, 792, 1, 0, 0, 0, 0, 0, 0;
    132, 731, 308, 1, 0, 0, 0, 0, 0;
    137, 54, 329, 695, 1, 0, 0, 0, 0;
    972, 155, 975, 374, 78, 1, 0, 0, 0;
    884, 754, 415, 66, 975, 545, 1, 0, 0;
    629, 237, 73, 796, 490, 36, 302, 1, 0;
    452, 433, 910, 924, 15, 679, 282, 814, 1]

private def secondUpper49 : Matrix (Fin 9) (Fin 9) F :=
  !![224, 690, 368, 37, 926, 70, 195, 551, 237;
    0, 297, 300, 0, 922, 902, 293, 215, 524;
    0, 0, 734, 77, 843, 364, 1004, 718, 773;
    0, 0, 0, 362, 295, 183, 872, 698, 506;
    0, 0, 0, 0, 369, 845, 509, 99, 335;
    0, 0, 0, 0, 0, 924, 118, 154, 312;
    0, 0, 0, 0, 0, 0, 179, 138, 120;
    0, 0, 0, 0, 0, 0, 0, 726, 231;
    0, 0, 0, 0, 0, 0, 0, 0, 214]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt49 : residualMinor (49 : F) 1 = secondValue 49 := by
  apply value_of_factors secondLower49 secondUpper49
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower50 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    322, 1, 0, 0, 0, 0, 0, 0, 0;
    336, 197, 1, 0, 0, 0, 0, 0, 0;
    536, 694, 666, 1, 0, 0, 0, 0, 0;
    540, 700, 196, 290, 1, 0, 0, 0, 0;
    524, 686, 648, 215, 248, 1, 0, 0, 0;
    595, 186, 659, 965, 546, 719, 1, 0, 0;
    907, 731, 395, 31, 654, 825, 300, 1, 0;
    407, 919, 871, 139, 159, 730, 352, 20, 1]

private def firstUpper50 : Matrix (Fin 9) (Fin 9) F :=
  !![601, 915, 645, 40, 899, 807, 394, 19, 694;
    0, 542, 938, 175, 193, 386, 273, 44, 468;
    0, 0, 258, 655, 562, 368, 211, 706, 88;
    0, 0, 0, 825, 722, 441, 421, 228, 945;
    0, 0, 0, 0, 78, 650, 712, 923, 136;
    0, 0, 0, 0, 0, 634, 27, 447, 290;
    0, 0, 0, 0, 0, 0, 103, 662, 261;
    0, 0, 0, 0, 0, 0, 0, 893, 318;
    0, 0, 0, 0, 0, 0, 0, 0, 291]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt50 : residualMinor (50 : F) 0 = firstValue 50 := by
  apply value_of_factors firstLower50 firstUpper50
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower50 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    947, 1, 0, 0, 0, 0, 0, 0, 0;
    969, 949, 1, 0, 0, 0, 0, 0, 0;
    575, 999, 964, 1, 0, 0, 0, 0, 0;
    1006, 829, 913, 888, 1, 0, 0, 0, 0;
    116, 621, 983, 784, 910, 1, 0, 0, 0;
    206, 560, 620, 871, 695, 455, 1, 0, 0;
    46, 802, 268, 545, 563, 784, 460, 1, 0;
    491, 189, 1008, 292, 412, 665, 565, 543, 1]

private def secondUpper50 : Matrix (Fin 9) (Fin 9) F :=
  !![776, 398, 499, 355, 974, 431, 70, 654, 81;
    0, 1004, 433, 759, 945, 406, 311, 296, 924;
    0, 0, 717, 347, 419, 697, 991, 147, 728;
    0, 0, 0, 470, 989, 22, 152, 382, 49;
    0, 0, 0, 0, 736, 226, 157, 833, 149;
    0, 0, 0, 0, 0, 848, 853, 420, 501;
    0, 0, 0, 0, 0, 0, 905, 71, 746;
    0, 0, 0, 0, 0, 0, 0, 833, 88;
    0, 0, 0, 0, 0, 0, 0, 0, 155]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt50 : residualMinor (50 : F) 1 = secondValue 50 := by
  apply value_of_factors secondLower50 secondUpper50
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower51 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    515, 1, 0, 0, 0, 0, 0, 0, 0;
    397, 452, 1, 0, 0, 0, 0, 0, 0;
    74, 452, 526, 1, 0, 0, 0, 0, 0;
    552, 125, 849, 189, 1, 0, 0, 0, 0;
    674, 133, 680, 631, 1000, 1, 0, 0, 0;
    561, 425, 1000, 856, 644, 999, 1, 0, 0;
    287, 909, 294, 958, 717, 675, 155, 1, 0;
    36, 980, 428, 199, 689, 706, 586, 46, 1]

private def firstUpper51 : Matrix (Fin 9) (Fin 9) F :=
  !![285, 40, 483, 340, 621, 728, 934, 812, 461;
    0, 599, 17, 410, 823, 117, 426, 879, 408;
    0, 0, 1007, 186, 951, 609, 854, 10, 32;
    0, 0, 0, 678, 705, 606, 433, 23, 254;
    0, 0, 0, 0, 54, 754, 548, 928, 252;
    0, 0, 0, 0, 0, 803, 943, 112, 297;
    0, 0, 0, 0, 0, 0, 302, 387, 368;
    0, 0, 0, 0, 0, 0, 0, 407, 199;
    0, 0, 0, 0, 0, 0, 0, 0, 455]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt51 : residualMinor (51 : F) 0 = firstValue 51 := by
  apply value_of_factors firstLower51 firstUpper51
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower51 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    619, 1, 0, 0, 0, 0, 0, 0, 0;
    439, 505, 1, 0, 0, 0, 0, 0, 0;
    733, 828, 945, 1, 0, 0, 0, 0, 0;
    367, 132, 807, 69, 1, 0, 0, 0, 0;
    895, 56, 18, 89, 418, 1, 0, 0, 0;
    624, 707, 165, 887, 292, 235, 1, 0, 0;
    787, 57, 973, 64, 672, 719, 232, 1, 0;
    52, 490, 425, 891, 592, 554, 1, 418, 1]

private def secondUpper51 : Matrix (Fin 9) (Fin 9) F :=
  !![13, 842, 465, 631, 100, 418, 975, 132, 956;
    0, 465, 278, 847, 434, 260, 0, 345, 218;
    0, 0, 204, 171, 237, 464, 973, 162, 140;
    0, 0, 0, 632, 933, 294, 380, 830, 3;
    0, 0, 0, 0, 498, 192, 148, 293, 82;
    0, 0, 0, 0, 0, 238, 400, 515, 363;
    0, 0, 0, 0, 0, 0, 46, 468, 856;
    0, 0, 0, 0, 0, 0, 0, 785, 394;
    0, 0, 0, 0, 0, 0, 0, 0, 287]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt51 : residualMinor (51 : F) 1 = secondValue 51 := by
  apply value_of_factors secondLower51 secondUpper51
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower52 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    546, 1, 0, 0, 0, 0, 0, 0, 0;
    457, 325, 1, 0, 0, 0, 0, 0, 0;
    426, 638, 539, 1, 0, 0, 0, 0, 0;
    199, 356, 452, 226, 1, 0, 0, 0, 0;
    519, 680, 108, 939, 308, 1, 0, 0, 0;
    1, 804, 405, 4, 228, 945, 1, 0, 0;
    901, 171, 27, 270, 399, 198, 509, 1, 0;
    319, 798, 64, 803, 561, 278, 631, 945, 1]

private def firstUpper52 : Matrix (Fin 9) (Fin 9) F :=
  !![668, 819, 60, 349, 142, 783, 637, 685, 480;
    0, 50, 517, 321, 515, 356, 288, 832, 816;
    0, 0, 683, 412, 465, 57, 58, 994, 799;
    0, 0, 0, 363, 91, 67, 987, 624, 383;
    0, 0, 0, 0, 51, 868, 372, 884, 363;
    0, 0, 0, 0, 0, 835, 29, 450, 994;
    0, 0, 0, 0, 0, 0, 813, 847, 19;
    0, 0, 0, 0, 0, 0, 0, 763, 184;
    0, 0, 0, 0, 0, 0, 0, 0, 614]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt52 : residualMinor (52 : F) 0 = firstValue 52 := by
  apply value_of_factors firstLower52 firstUpper52
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower52 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    13, 1, 0, 0, 0, 0, 0, 0, 0;
    693, 719, 1, 0, 0, 0, 0, 0, 0;
    275, 409, 808, 1, 0, 0, 0, 0, 0;
    639, 429, 915, 639, 1, 0, 0, 0, 0;
    12, 35, 58, 586, 128, 1, 0, 0, 0;
    758, 521, 831, 821, 821, 812, 1, 0, 0;
    648, 958, 511, 47, 602, 253, 798, 1, 0;
    308, 246, 921, 866, 405, 925, 559, 466, 1]

private def secondUpper52 : Matrix (Fin 9) (Fin 9) F :=
  !![461, 447, 790, 842, 0, 145, 443, 146, 442;
    0, 480, 809, 327, 354, 191, 280, 623, 864;
    0, 0, 312, 561, 406, 677, 555, 9, 788;
    0, 0, 0, 491, 469, 123, 334, 364, 106;
    0, 0, 0, 0, 750, 577, 253, 549, 664;
    0, 0, 0, 0, 0, 15, 108, 545, 255;
    0, 0, 0, 0, 0, 0, 329, 891, 3;
    0, 0, 0, 0, 0, 0, 0, 503, 476;
    0, 0, 0, 0, 0, 0, 0, 0, 504]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt52 : residualMinor (52 : F) 1 = secondValue 52 := by
  apply value_of_factors secondLower52 secondUpper52
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower53 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    543, 1, 0, 0, 0, 0, 0, 0, 0;
    978, 71, 1, 0, 0, 0, 0, 0, 0;
    598, 772, 352, 1, 0, 0, 0, 0, 0;
    915, 895, 189, 741, 1, 0, 0, 0, 0;
    394, 477, 655, 984, 57, 1, 0, 0, 0;
    405, 866, 251, 404, 351, 945, 1, 0, 0;
    955, 585, 883, 198, 602, 960, 89, 1, 0;
    231, 400, 423, 775, 379, 749, 392, 214, 1]

private def firstUpper53 : Matrix (Fin 9) (Fin 9) F :=
  !![754, 157, 323, 750, 993, 459, 202, 293, 280;
    0, 662, 367, 101, 812, 713, 499, 97, 816;
    0, 0, 261, 186, 638, 757, 361, 864, 938;
    0, 0, 0, 967, 435, 504, 353, 392, 496;
    0, 0, 0, 0, 590, 908, 358, 605, 814;
    0, 0, 0, 0, 0, 609, 725, 655, 642;
    0, 0, 0, 0, 0, 0, 523, 168, 871;
    0, 0, 0, 0, 0, 0, 0, 908, 52;
    0, 0, 0, 0, 0, 0, 0, 0, 99]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt53 : residualMinor (53 : F) 0 = firstValue 53 := by
  apply value_of_factors firstLower53 firstUpper53
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower53 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    635, 1, 0, 0, 0, 0, 0, 0, 0;
    734, 602, 1, 0, 0, 0, 0, 0, 0;
    870, 888, 957, 1, 0, 0, 0, 0, 0;
    202, 54, 333, 183, 1, 0, 0, 0, 0;
    39, 1007, 950, 780, 307, 1, 0, 0, 0;
    279, 774, 682, 510, 583, 378, 1, 0, 0;
    996, 748, 863, 41, 830, 185, 970, 1, 0;
    852, 870, 387, 321, 469, 43, 882, 815, 1]

private def secondUpper53 : Matrix (Fin 9) (Fin 9) F :=
  !![641, 614, 770, 654, 138, 977, 619, 383, 275;
    0, 741, 605, 133, 349, 867, 649, 747, 429;
    0, 0, 60, 144, 655, 827, 765, 386, 749;
    0, 0, 0, 89, 417, 333, 329, 915, 941;
    0, 0, 0, 0, 196, 189, 221, 68, 618;
    0, 0, 0, 0, 0, 512, 848, 483, 896;
    0, 0, 0, 0, 0, 0, 825, 276, 222;
    0, 0, 0, 0, 0, 0, 0, 473, 266;
    0, 0, 0, 0, 0, 0, 0, 0, 529]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt53 : residualMinor (53 : F) 1 = secondValue 53 := by
  apply value_of_factors secondLower53 secondUpper53
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower54 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    26, 1, 0, 0, 0, 0, 0, 0, 0;
    324, 262, 1, 0, 0, 0, 0, 0, 0;
    39, 898, 67, 1, 0, 0, 0, 0, 0;
    918, 351, 28, 828, 1, 0, 0, 0, 0;
    637, 764, 300, 153, 759, 1, 0, 0, 0;
    581, 917, 488, 899, 30, 907, 1, 0, 0;
    739, 990, 575, 295, 5, 968, 738, 1, 0;
    499, 236, 831, 840, 1008, 400, 608, 854, 1]

private def firstUpper54 : Matrix (Fin 9) (Fin 9) F :=
  !![769, 6, 387, 544, 896, 797, 559, 230, 312;
    0, 97, 586, 28, 360, 981, 100, 69, 396;
    0, 0, 228, 807, 229, 936, 192, 557, 297;
    0, 0, 0, 599, 115, 119, 848, 269, 609;
    0, 0, 0, 0, 133, 819, 535, 747, 201;
    0, 0, 0, 0, 0, 354, 954, 315, 138;
    0, 0, 0, 0, 0, 0, 648, 96, 579;
    0, 0, 0, 0, 0, 0, 0, 381, 25;
    0, 0, 0, 0, 0, 0, 0, 0, 827]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt54 : residualMinor (54 : F) 0 = firstValue 54 := by
  apply value_of_factors firstLower54 firstUpper54
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower54 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    717, 1, 0, 0, 0, 0, 0, 0, 0;
    33, 806, 1, 0, 0, 0, 0, 0, 0;
    4, 918, 46, 1, 0, 0, 0, 0, 0;
    332, 478, 231, 674, 1, 0, 0, 0, 0;
    862, 506, 963, 280, 102, 1, 0, 0, 0;
    488, 174, 526, 458, 837, 398, 1, 0, 0;
    776, 173, 592, 839, 138, 584, 329, 1, 0;
    272, 275, 717, 659, 631, 126, 801, 837, 1]

private def secondUpper54 : Matrix (Fin 9) (Fin 9) F :=
  !![345, 452, 142, 93, 281, 466, 687, 938, 713;
    0, 58, 653, 968, 772, 371, 321, 452, 778;
    0, 0, 394, 468, 553, 991, 777, 589, 518;
    0, 0, 0, 731, 655, 595, 1008, 753, 550;
    0, 0, 0, 0, 970, 402, 781, 600, 663;
    0, 0, 0, 0, 0, 1002, 552, 302, 493;
    0, 0, 0, 0, 0, 0, 463, 377, 260;
    0, 0, 0, 0, 0, 0, 0, 332, 467;
    0, 0, 0, 0, 0, 0, 0, 0, 369]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt54 : residualMinor (54 : F) 1 = secondValue 54 := by
  apply value_of_factors secondLower54 secondUpper54
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower55 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    268, 1, 0, 0, 0, 0, 0, 0, 0;
    872, 113, 1, 0, 0, 0, 0, 0, 0;
    841, 444, 803, 1, 0, 0, 0, 0, 0;
    914, 147, 720, 75, 1, 0, 0, 0, 0;
    857, 181, 949, 269, 763, 1, 0, 0, 0;
    731, 693, 808, 88, 778, 641, 1, 0, 0;
    874, 806, 309, 681, 259, 358, 846, 1, 0;
    579, 105, 156, 910, 708, 589, 470, 842, 1]

private def firstUpper55 : Matrix (Fin 9) (Fin 9) F :=
  !![141, 106, 246, 870, 357, 176, 28, 428, 660;
    0, 845, 623, 886, 74, 346, 278, 914, 937;
    0, 0, 153, 545, 126, 234, 321, 352, 443;
    0, 0, 0, 87, 948, 901, 379, 520, 484;
    0, 0, 0, 0, 588, 491, 165, 363, 757;
    0, 0, 0, 0, 0, 62, 75, 733, 482;
    0, 0, 0, 0, 0, 0, 299, 634, 857;
    0, 0, 0, 0, 0, 0, 0, 698, 853;
    0, 0, 0, 0, 0, 0, 0, 0, 146]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt55 : residualMinor (55 : F) 0 = firstValue 55 := by
  apply value_of_factors firstLower55 firstUpper55
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower55 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    694, 1, 0, 0, 0, 0, 0, 0, 0;
    655, 945, 1, 0, 0, 0, 0, 0, 0;
    104, 356, 916, 1, 0, 0, 0, 0, 0;
    692, 483, 711, 741, 1, 0, 0, 0, 0;
    500, 892, 110, 40, 1004, 1, 0, 0, 0;
    124, 904, 659, 863, 689, 858, 1, 0, 0;
    117, 759, 631, 3, 967, 180, 797, 1, 0;
    173, 99, 346, 554, 589, 313, 982, 478, 1]

private def secondUpper55 : Matrix (Fin 9) (Fin 9) F :=
  !![317, 173, 939, 712, 245, 840, 168, 180, 806;
    0, 1, 105, 240, 386, 333, 162, 788, 864;
    0, 0, 628, 667, 383, 922, 875, 737, 347;
    0, 0, 0, 251, 197, 987, 690, 943, 533;
    0, 0, 0, 0, 773, 238, 188, 537, 906;
    0, 0, 0, 0, 0, 96, 173, 520, 584;
    0, 0, 0, 0, 0, 0, 588, 356, 502;
    0, 0, 0, 0, 0, 0, 0, 187, 273;
    0, 0, 0, 0, 0, 0, 0, 0, 409]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt55 : residualMinor (55 : F) 1 = secondValue 55 := by
  apply value_of_factors secondLower55 secondUpper55
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 48 through 55. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((48 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt48, secondAt48⟩
  · exact ⟨firstAt49, secondAt49⟩
  · exact ⟨firstAt50, secondAt50⟩
  · exact ⟨firstAt51, secondAt51⟩
  · exact ⟨firstAt52, secondAt52⟩
  · exact ⟨firstAt53, secondAt53⟩
  · exact ⟨firstAt54, secondAt54⟩
  · exact ⟨firstAt55, secondAt55⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch48
