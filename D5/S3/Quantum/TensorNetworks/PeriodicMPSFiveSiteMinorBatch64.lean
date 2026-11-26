/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch64
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch64
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch64

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower64 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    669, 1, 0, 0, 0, 0, 0, 0, 0;
    353, 192, 1, 0, 0, 0, 0, 0, 0;
    380, 770, 247, 1, 0, 0, 0, 0, 0;
    425, 172, 232, 228, 1, 0, 0, 0, 0;
    179, 193, 126, 600, 370, 1, 0, 0, 0;
    548, 874, 118, 96, 380, 626, 1, 0, 0;
    493, 449, 206, 569, 600, 563, 582, 1, 0;
    310, 199, 1005, 136, 612, 668, 795, 186, 1]

private def firstUpper64 : Matrix (Fin 9) (Fin 9) F :=
  !![133, 630, 584, 904, 815, 369, 463, 171, 421;
    0, 835, 594, 748, 432, 988, 234, 799, 139;
    0, 0, 49, 151, 590, 755, 202, 461, 126;
    0, 0, 0, 555, 962, 798, 215, 748, 900;
    0, 0, 0, 0, 852, 95, 134, 370, 745;
    0, 0, 0, 0, 0, 345, 724, 167, 734;
    0, 0, 0, 0, 0, 0, 378, 691, 383;
    0, 0, 0, 0, 0, 0, 0, 717, 722;
    0, 0, 0, 0, 0, 0, 0, 0, 699]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt64 : residualMinor (64 : F) 0 = firstValue 64 := by
  apply value_of_factors firstLower64 firstUpper64
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower64 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    707, 1, 0, 0, 0, 0, 0, 0, 0;
    582, 336, 1, 0, 0, 0, 0, 0, 0;
    108, 752, 641, 1, 0, 0, 0, 0, 0;
    991, 459, 983, 851, 1, 0, 0, 0, 0;
    375, 851, 854, 989, 52, 1, 0, 0, 0;
    315, 679, 9, 652, 232, 197, 1, 0, 0;
    141, 188, 897, 702, 727, 11, 384, 1, 0;
    903, 515, 348, 341, 471, 661, 531, 138, 1]

private def secondUpper64 : Matrix (Fin 9) (Fin 9) F :=
  !![906, 560, 365, 38, 384, 803, 406, 13, 752;
    0, 151, 47, 501, 740, 990, 741, 62, 356;
    0, 0, 208, 1006, 1, 1006, 776, 178, 558;
    0, 0, 0, 242, 747, 678, 916, 56, 62;
    0, 0, 0, 0, 29, 927, 667, 0, 665;
    0, 0, 0, 0, 0, 226, 966, 714, 49;
    0, 0, 0, 0, 0, 0, 59, 738, 919;
    0, 0, 0, 0, 0, 0, 0, 307, 984;
    0, 0, 0, 0, 0, 0, 0, 0, 90]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt64 : residualMinor (64 : F) 1 = secondValue 64 := by
  apply value_of_factors secondLower64 secondUpper64
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower65 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    257, 1, 0, 0, 0, 0, 0, 0, 0;
    68, 994, 1, 0, 0, 0, 0, 0, 0;
    724, 45, 413, 1, 0, 0, 0, 0, 0;
    473, 259, 459, 298, 1, 0, 0, 0, 0;
    296, 337, 653, 907, 390, 1, 0, 0, 0;
    227, 387, 91, 534, 531, 973, 1, 0, 0;
    604, 919, 746, 825, 73, 818, 695, 1, 0;
    653, 302, 849, 511, 991, 432, 158, 255, 1]

private def firstUpper65 : Matrix (Fin 9) (Fin 9) F :=
  !![85, 821, 630, 306, 642, 764, 120, 556, 385;
    0, 996, 251, 919, 504, 754, 556, 274, 330;
    0, 0, 524, 16, 995, 542, 967, 396, 955;
    0, 0, 0, 527, 121, 814, 528, 351, 207;
    0, 0, 0, 0, 659, 213, 784, 939, 450;
    0, 0, 0, 0, 0, 312, 44, 221, 486;
    0, 0, 0, 0, 0, 0, 654, 771, 542;
    0, 0, 0, 0, 0, 0, 0, 852, 179;
    0, 0, 0, 0, 0, 0, 0, 0, 146]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt65 : residualMinor (65 : F) 0 = firstValue 65 := by
  apply value_of_factors firstLower65 firstUpper65
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower65 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    722, 1, 0, 0, 0, 0, 0, 0, 0;
    600, 796, 1, 0, 0, 0, 0, 0, 0;
    752, 647, 472, 1, 0, 0, 0, 0, 0;
    812, 100, 713, 873, 1, 0, 0, 0, 0;
    796, 675, 810, 749, 277, 1, 0, 0, 0;
    541, 998, 783, 878, 15, 793, 1, 0, 0;
    359, 256, 495, 919, 883, 794, 414, 1, 0;
    728, 540, 381, 71, 900, 438, 758, 677, 1]

private def secondUpper65 : Matrix (Fin 9) (Fin 9) F :=
  !![530, 142, 103, 647, 209, 342, 699, 88, 825;
    0, 497, 12, 892, 474, 628, 948, 928, 53;
    0, 0, 535, 545, 545, 18, 246, 365, 596;
    0, 0, 0, 504, 883, 488, 316, 223, 423;
    0, 0, 0, 0, 77, 465, 872, 57, 893;
    0, 0, 0, 0, 0, 805, 348, 151, 804;
    0, 0, 0, 0, 0, 0, 785, 821, 374;
    0, 0, 0, 0, 0, 0, 0, 678, 165;
    0, 0, 0, 0, 0, 0, 0, 0, 1008]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt65 : residualMinor (65 : F) 1 = secondValue 65 := by
  apply value_of_factors secondLower65 secondUpper65
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower66 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    727, 1, 0, 0, 0, 0, 0, 0, 0;
    366, 761, 1, 0, 0, 0, 0, 0, 0;
    329, 453, 54, 1, 0, 0, 0, 0, 0;
    224, 288, 29, 162, 1, 0, 0, 0, 0;
    895, 839, 863, 835, 743, 1, 0, 0, 0;
    181, 999, 575, 54, 918, 306, 1, 0, 0;
    974, 980, 37, 816, 683, 56, 459, 1, 0;
    701, 378, 364, 593, 844, 8, 140, 963, 1]

private def firstUpper66 : Matrix (Fin 9) (Fin 9) F :=
  !![318, 52, 772, 926, 386, 49, 611, 907, 589;
    0, 686, 275, 184, 813, 806, 52, 563, 865;
    0, 0, 788, 305, 978, 834, 340, 547, 815;
    0, 0, 0, 830, 583, 432, 651, 231, 479;
    0, 0, 0, 0, 743, 451, 262, 517, 585;
    0, 0, 0, 0, 0, 556, 496, 778, 459;
    0, 0, 0, 0, 0, 0, 432, 565, 415;
    0, 0, 0, 0, 0, 0, 0, 231, 368;
    0, 0, 0, 0, 0, 0, 0, 0, 106]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt66 : residualMinor (66 : F) 0 = firstValue 66 := by
  apply value_of_factors firstLower66 firstUpper66
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower66 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    462, 1, 0, 0, 0, 0, 0, 0, 0;
    88, 440, 1, 0, 0, 0, 0, 0, 0;
    741, 515, 900, 1, 0, 0, 0, 0, 0;
    300, 922, 564, 960, 1, 0, 0, 0, 0;
    4, 914, 635, 323, 845, 1, 0, 0, 0;
    353, 697, 574, 367, 320, 810, 1, 0, 0;
    172, 293, 608, 117, 757, 43, 822, 1, 0;
    627, 324, 167, 823, 563, 632, 243, 642, 1]

private def secondUpper66 : Matrix (Fin 9) (Fin 9) F :=
  !![870, 799, 173, 735, 980, 850, 827, 371, 862;
    0, 304, 300, 846, 205, 915, 626, 194, 554;
    0, 0, 313, 956, 296, 357, 78, 211, 88;
    0, 0, 0, 388, 428, 215, 993, 328, 193;
    0, 0, 0, 0, 833, 778, 758, 789, 227;
    0, 0, 0, 0, 0, 889, 65, 410, 899;
    0, 0, 0, 0, 0, 0, 20, 579, 812;
    0, 0, 0, 0, 0, 0, 0, 762, 239;
    0, 0, 0, 0, 0, 0, 0, 0, 757]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt66 : residualMinor (66 : F) 1 = secondValue 66 := by
  apply value_of_factors secondLower66 secondUpper66
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower67 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    580, 1, 0, 0, 0, 0, 0, 0, 0;
    586, 780, 1, 0, 0, 0, 0, 0, 0;
    730, 847, 290, 1, 0, 0, 0, 0, 0;
    149, 682, 129, 770, 1, 0, 0, 0, 0;
    152, 101, 704, 712, 86, 1, 0, 0, 0;
    387, 119, 618, 932, 685, 748, 1, 0, 0;
    117, 667, 35, 427, 946, 599, 782, 1, 0;
    359, 663, 41, 264, 61, 983, 942, 5, 1]

private def firstUpper67 : Matrix (Fin 9) (Fin 9) F :=
  !![221, 573, 631, 732, 681, 207, 460, 855, 903;
    0, 476, 944, 319, 807, 524, 212, 403, 414;
    0, 0, 872, 900, 64, 155, 512, 463, 577;
    0, 0, 0, 954, 678, 410, 976, 953, 73;
    0, 0, 0, 0, 207, 430, 233, 90, 357;
    0, 0, 0, 0, 0, 136, 680, 246, 644;
    0, 0, 0, 0, 0, 0, 904, 151, 225;
    0, 0, 0, 0, 0, 0, 0, 841, 180;
    0, 0, 0, 0, 0, 0, 0, 0, 393]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt67 : residualMinor (67 : F) 0 = firstValue 67 := by
  apply value_of_factors firstLower67 firstUpper67
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower67 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    594, 1, 0, 0, 0, 0, 0, 0, 0;
    685, 314, 1, 0, 0, 0, 0, 0, 0;
    809, 398, 254, 1, 0, 0, 0, 0, 0;
    150, 879, 352, 27, 1, 0, 0, 0, 0;
    882, 673, 286, 673, 370, 1, 0, 0, 0;
    814, 308, 630, 214, 849, 401, 1, 0, 0;
    983, 872, 684, 314, 266, 492, 473, 1, 0;
    130, 652, 276, 189, 79, 475, 159, 972, 1]

private def secondUpper67 : Matrix (Fin 9) (Fin 9) F :=
  !![216, 417, 631, 40, 243, 671, 442, 444, 942;
    0, 362, 182, 546, 204, 494, 428, 497, 930;
    0, 0, 67, 553, 969, 182, 288, 467, 121;
    0, 0, 0, 347, 971, 924, 179, 305, 173;
    0, 0, 0, 0, 958, 557, 911, 151, 957;
    0, 0, 0, 0, 0, 705, 67, 802, 279;
    0, 0, 0, 0, 0, 0, 552, 978, 812;
    0, 0, 0, 0, 0, 0, 0, 281, 579;
    0, 0, 0, 0, 0, 0, 0, 0, 379]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt67 : residualMinor (67 : F) 1 = secondValue 67 := by
  apply value_of_factors secondLower67 secondUpper67
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower68 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    658, 1, 0, 0, 0, 0, 0, 0, 0;
    199, 55, 1, 0, 0, 0, 0, 0, 0;
    834, 570, 572, 1, 0, 0, 0, 0, 0;
    941, 6, 760, 676, 1, 0, 0, 0, 0;
    642, 727, 634, 711, 351, 1, 0, 0, 0;
    597, 272, 668, 368, 245, 379, 1, 0, 0;
    963, 427, 993, 405, 675, 924, 626, 1, 0;
    262, 31, 965, 247, 472, 670, 805, 728, 1]

private def firstUpper68 : Matrix (Fin 9) (Fin 9) F :=
  !![87, 700, 641, 102, 818, 65, 815, 791, 95;
    0, 679, 481, 697, 549, 718, 263, 338, 6;
    0, 0, 250, 92, 583, 292, 468, 288, 281;
    0, 0, 0, 360, 920, 718, 111, 158, 230;
    0, 0, 0, 0, 175, 68, 318, 226, 555;
    0, 0, 0, 0, 0, 422, 692, 550, 502;
    0, 0, 0, 0, 0, 0, 708, 574, 22;
    0, 0, 0, 0, 0, 0, 0, 855, 209;
    0, 0, 0, 0, 0, 0, 0, 0, 552]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt68 : residualMinor (68 : F) 0 = firstValue 68 := by
  apply value_of_factors firstLower68 firstUpper68
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower68 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    980, 1, 0, 0, 0, 0, 0, 0, 0;
    645, 113, 1, 0, 0, 0, 0, 0, 0;
    773, 895, 131, 1, 0, 0, 0, 0, 0;
    870, 467, 259, 443, 1, 0, 0, 0, 0;
    753, 581, 423, 928, 576, 1, 0, 0, 0;
    905, 1005, 276, 461, 527, 611, 1, 0, 0;
    282, 12, 547, 258, 428, 604, 32, 1, 0;
    400, 57, 495, 345, 806, 937, 886, 38, 1]

private def secondUpper68 : Matrix (Fin 9) (Fin 9) F :=
  !![943, 872, 274, 894, 29, 580, 133, 467, 894;
    0, 229, 371, 911, 828, 777, 575, 598, 659;
    0, 0, 187, 696, 571, 470, 124, 217, 53;
    0, 0, 0, 236, 886, 8, 618, 801, 117;
    0, 0, 0, 0, 12, 58, 866, 896, 109;
    0, 0, 0, 0, 0, 427, 564, 276, 281;
    0, 0, 0, 0, 0, 0, 150, 533, 813;
    0, 0, 0, 0, 0, 0, 0, 381, 349;
    0, 0, 0, 0, 0, 0, 0, 0, 60]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt68 : residualMinor (68 : F) 1 = secondValue 68 := by
  apply value_of_factors secondLower68 secondUpper68
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower69 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    749, 1, 0, 0, 0, 0, 0, 0, 0;
    803, 131, 1, 0, 0, 0, 0, 0, 0;
    89, 287, 762, 1, 0, 0, 0, 0, 0;
    492, 766, 193, 83, 1, 0, 0, 0, 0;
    859, 420, 805, 54, 226, 1, 0, 0, 0;
    453, 884, 41, 559, 409, 836, 1, 0, 0;
    67, 862, 570, 629, 1006, 530, 805, 1, 0;
    238, 255, 177, 205, 410, 647, 643, 454, 1]

private def firstUpper69 : Matrix (Fin 9) (Fin 9) F :=
  !![992, 861, 330, 741, 679, 953, 858, 136, 834;
    0, 24, 192, 196, 889, 165, 657, 611, 959;
    0, 0, 396, 766, 45, 802, 432, 883, 980;
    0, 0, 0, 56, 294, 44, 112, 848, 893;
    0, 0, 0, 0, 504, 800, 148, 7, 817;
    0, 0, 0, 0, 0, 972, 1008, 973, 735;
    0, 0, 0, 0, 0, 0, 256, 99, 75;
    0, 0, 0, 0, 0, 0, 0, 321, 279;
    0, 0, 0, 0, 0, 0, 0, 0, 720]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt69 : residualMinor (69 : F) 0 = firstValue 69 := by
  apply value_of_factors firstLower69 firstUpper69
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower69 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    674, 1, 0, 0, 0, 0, 0, 0, 0;
    798, 244, 1, 0, 0, 0, 0, 0, 0;
    288, 307, 866, 1, 0, 0, 0, 0, 0;
    490, 411, 968, 259, 1, 0, 0, 0, 0;
    633, 428, 66, 546, 186, 1, 0, 0, 0;
    368, 410, 477, 237, 700, 138, 1, 0, 0;
    902, 1002, 257, 769, 738, 769, 819, 1, 0;
    663, 349, 850, 367, 974, 751, 722, 290, 1]

private def secondUpper69 : Matrix (Fin 9) (Fin 9) F :=
  !![482, 312, 29, 562, 883, 757, 653, 188, 805;
    0, 755, 791, 851, 83, 935, 368, 988, 317;
    0, 0, 735, 660, 422, 855, 120, 836, 898;
    0, 0, 0, 859, 558, 331, 574, 690, 375;
    0, 0, 0, 0, 580, 74, 663, 947, 610;
    0, 0, 0, 0, 0, 166, 293, 842, 994;
    0, 0, 0, 0, 0, 0, 558, 696, 255;
    0, 0, 0, 0, 0, 0, 0, 510, 49;
    0, 0, 0, 0, 0, 0, 0, 0, 44]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt69 : residualMinor (69 : F) 1 = secondValue 69 := by
  apply value_of_factors secondLower69 secondUpper69
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower70 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    332, 1, 0, 0, 0, 0, 0, 0, 0;
    18, 515, 1, 0, 0, 0, 0, 0, 0;
    183, 861, 642, 1, 0, 0, 0, 0, 0;
    142, 819, 621, 120, 1, 0, 0, 0, 0;
    913, 356, 925, 407, 363, 1, 0, 0, 0;
    320, 680, 40, 912, 103, 552, 1, 0, 0;
    978, 2, 638, 974, 454, 259, 336, 1, 0;
    688, 651, 944, 867, 191, 908, 984, 18, 1]

private def firstUpper70 : Matrix (Fin 9) (Fin 9) F :=
  !![344, 889, 743, 442, 919, 524, 476, 103, 974;
    0, 241, 611, 30, 570, 438, 506, 914, 260;
    0, 0, 458, 829, 128, 847, 320, 789, 460;
    0, 0, 0, 242, 390, 639, 971, 223, 916;
    0, 0, 0, 0, 306, 747, 694, 17, 780;
    0, 0, 0, 0, 0, 290, 206, 45, 992;
    0, 0, 0, 0, 0, 0, 324, 767, 951;
    0, 0, 0, 0, 0, 0, 0, 628, 614;
    0, 0, 0, 0, 0, 0, 0, 0, 857]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt70 : residualMinor (70 : F) 0 = firstValue 70 := by
  apply value_of_factors firstLower70 firstUpper70
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower70 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    777, 1, 0, 0, 0, 0, 0, 0, 0;
    308, 278, 1, 0, 0, 0, 0, 0, 0;
    122, 144, 930, 1, 0, 0, 0, 0, 0;
    848, 775, 875, 710, 1, 0, 0, 0, 0;
    128, 746, 241, 578, 466, 1, 0, 0, 0;
    769, 983, 483, 508, 811, 157, 1, 0, 0;
    470, 278, 634, 487, 251, 365, 258, 1, 0;
    527, 158, 593, 205, 22, 423, 828, 536, 1]

private def secondUpper70 : Matrix (Fin 9) (Fin 9) F :=
  !![790, 824, 22, 925, 260, 908, 925, 582, 929;
    0, 219, 141, 152, 740, 633, 817, 622, 350;
    0, 0, 3, 788, 204, 173, 621, 101, 530;
    0, 0, 0, 641, 832, 773, 868, 630, 331;
    0, 0, 0, 0, 210, 24, 586, 747, 824;
    0, 0, 0, 0, 0, 549, 572, 395, 474;
    0, 0, 0, 0, 0, 0, 967, 656, 144;
    0, 0, 0, 0, 0, 0, 0, 583, 358;
    0, 0, 0, 0, 0, 0, 0, 0, 150]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt70 : residualMinor (70 : F) 1 = secondValue 70 := by
  apply value_of_factors secondLower70 secondUpper70
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower71 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    750, 1, 0, 0, 0, 0, 0, 0, 0;
    1000, 943, 1, 0, 0, 0, 0, 0, 0;
    633, 909, 429, 1, 0, 0, 0, 0, 0;
    738, 619, 915, 852, 1, 0, 0, 0, 0;
    962, 724, 343, 200, 826, 1, 0, 0, 0;
    677, 877, 685, 659, 102, 285, 1, 0, 0;
    285, 814, 80, 591, 701, 290, 798, 1, 0;
    521, 609, 187, 749, 28, 944, 766, 444, 1]

private def firstUpper71 : Matrix (Fin 9) (Fin 9) F :=
  !![2, 187, 587, 660, 291, 174, 244, 830, 83;
    0, 494, 952, 418, 908, 342, 831, 929, 21;
    0, 0, 623, 464, 265, 645, 221, 711, 949;
    0, 0, 0, 916, 922, 589, 767, 21, 890;
    0, 0, 0, 0, 614, 459, 57, 482, 937;
    0, 0, 0, 0, 0, 235, 851, 837, 568;
    0, 0, 0, 0, 0, 0, 222, 180, 778;
    0, 0, 0, 0, 0, 0, 0, 33, 776;
    0, 0, 0, 0, 0, 0, 0, 0, 942]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt71 : residualMinor (71 : F) 0 = firstValue 71 := by
  apply value_of_factors firstLower71 firstUpper71
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower71 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    658, 1, 0, 0, 0, 0, 0, 0, 0;
    929, 647, 1, 0, 0, 0, 0, 0, 0;
    989, 71, 369, 1, 0, 0, 0, 0, 0;
    549, 990, 228, 124, 1, 0, 0, 0, 0;
    176, 976, 564, 589, 339, 1, 0, 0, 0;
    875, 512, 110, 129, 982, 780, 1, 0, 0;
    836, 9, 74, 437, 743, 833, 1005, 1, 0;
    202, 533, 239, 233, 712, 937, 225, 344, 1]

private def secondUpper71 : Matrix (Fin 9) (Fin 9) F :=
  !![201, 518, 108, 386, 24, 887, 210, 381, 857;
    0, 691, 844, 279, 557, 237, 246, 410, 847;
    0, 0, 480, 941, 12, 73, 599, 846, 660;
    0, 0, 0, 708, 48, 296, 234, 266, 383;
    0, 0, 0, 0, 160, 772, 655, 535, 73;
    0, 0, 0, 0, 0, 358, 512, 247, 34;
    0, 0, 0, 0, 0, 0, 913, 786, 187;
    0, 0, 0, 0, 0, 0, 0, 57, 251;
    0, 0, 0, 0, 0, 0, 0, 0, 398]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt71 : residualMinor (71 : F) 1 = secondValue 71 := by
  apply value_of_factors secondLower71 secondUpper71
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 64 through 71. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((64 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt64, secondAt64⟩
  · exact ⟨firstAt65, secondAt65⟩
  · exact ⟨firstAt66, secondAt66⟩
  · exact ⟨firstAt67, secondAt67⟩
  · exact ⟨firstAt68, secondAt68⟩
  · exact ⟨firstAt69, secondAt69⟩
  · exact ⟨firstAt70, secondAt70⟩
  · exact ⟨firstAt71, secondAt71⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch64
