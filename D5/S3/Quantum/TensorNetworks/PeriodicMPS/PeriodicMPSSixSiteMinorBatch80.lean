/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch80
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch80
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch80

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower80 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    84, 1, 0, 0, 0, 0, 0, 0, 0;
    104, 1, 1, 0, 0, 0, 0, 0, 0;
    17, 6, 603, 1, 0, 0, 0, 0, 0;
    68, 116, 965, 879, 1, 0, 0, 0, 0;
    941, 164, 758, 482, 617, 1, 0, 0, 0;
    188, 42, 319, 342, 942, 562, 1, 0, 0;
    64, 722, 695, 243, 509, 762, 3, 1, 0;
    599, 595, 72, 962, 277, 543, 765, 318, 1]

private def firstUpper80 : Matrix (Fin 9) (Fin 9) F :=
  !![802, 833, 685, 160, 314, 429, 929, 897, 117;
    0, 40, 215, 329, 575, 126, 860, 301, 776;
    0, 0, 336, 111, 694, 481, 185, 442, 938;
    0, 0, 0, 451, 718, 511, 381, 802, 717;
    0, 0, 0, 0, 819, 239, 742, 919, 189;
    0, 0, 0, 0, 0, 722, 458, 736, 698;
    0, 0, 0, 0, 0, 0, 187, 243, 537;
    0, 0, 0, 0, 0, 0, 0, 980, 217;
    0, 0, 0, 0, 0, 0, 0, 0, 537]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt80 : residualMinor (80 : F) 0 = firstValue 80 := by
  apply value_of_factors firstLower80 firstUpper80
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower80 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    707, 1, 0, 0, 0, 0, 0, 0, 0;
    454, 320, 1, 0, 0, 0, 0, 0, 0;
    60, 857, 144, 1, 0, 0, 0, 0, 0;
    983, 189, 924, 271, 1, 0, 0, 0, 0;
    500, 401, 654, 693, 674, 1, 0, 0, 0;
    509, 481, 532, 209, 826, 287, 1, 0, 0;
    820, 926, 285, 321, 432, 998, 311, 1, 0;
    845, 941, 720, 818, 556, 947, 702, 335, 1]

private def secondUpper80 : Matrix (Fin 9) (Fin 9) F :=
  !![547, 719, 49, 769, 794, 538, 912, 338, 130;
    0, 594, 914, 820, 363, 874, 161, 141, 423;
    0, 0, 234, 864, 240, 566, 378, 395, 113;
    0, 0, 0, 937, 391, 841, 786, 621, 737;
    0, 0, 0, 0, 983, 782, 140, 148, 699;
    0, 0, 0, 0, 0, 91, 59, 402, 807;
    0, 0, 0, 0, 0, 0, 218, 278, 208;
    0, 0, 0, 0, 0, 0, 0, 107, 937;
    0, 0, 0, 0, 0, 0, 0, 0, 296]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt80 : residualMinor (80 : F) 1 = secondValue 80 := by
  apply value_of_factors secondLower80 secondUpper80
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower81 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    437, 1, 0, 0, 0, 0, 0, 0, 0;
    307, 616, 1, 0, 0, 0, 0, 0, 0;
    740, 859, 323, 1, 0, 0, 0, 0, 0;
    218, 71, 914, 636, 1, 0, 0, 0, 0;
    678, 572, 249, 939, 852, 1, 0, 0, 0;
    305, 762, 691, 581, 258, 552, 1, 0, 0;
    351, 105, 792, 75, 302, 922, 393, 1, 0;
    106, 993, 557, 473, 59, 351, 852, 297, 1]

private def firstUpper81 : Matrix (Fin 9) (Fin 9) F :=
  !![931, 406, 59, 874, 566, 382, 926, 658, 800;
    0, 950, 103, 820, 512, 582, 283, 804, 950;
    0, 0, 46, 662, 175, 441, 734, 875, 674;
    0, 0, 0, 972, 450, 566, 525, 62, 655;
    0, 0, 0, 0, 525, 668, 151, 10, 75;
    0, 0, 0, 0, 0, 634, 955, 764, 373;
    0, 0, 0, 0, 0, 0, 117, 937, 622;
    0, 0, 0, 0, 0, 0, 0, 4, 502;
    0, 0, 0, 0, 0, 0, 0, 0, 780]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt81 : residualMinor (81 : F) 0 = firstValue 81 := by
  apply value_of_factors firstLower81 firstUpper81
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower81 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    678, 1, 0, 0, 0, 0, 0, 0, 0;
    860, 320, 1, 0, 0, 0, 0, 0, 0;
    1, 971, 242, 1, 0, 0, 0, 0, 0;
    969, 349, 422, 89, 1, 0, 0, 0, 0;
    311, 688, 179, 95, 77, 1, 0, 0, 0;
    205, 160, 929, 284, 658, 527, 1, 0, 0;
    666, 509, 210, 823, 902, 816, 995, 1, 0;
    588, 773, 670, 232, 203, 324, 785, 109, 1]

private def secondUpper81 : Matrix (Fin 9) (Fin 9) F :=
  !![521, 617, 105, 29, 542, 105, 246, 381, 611;
    0, 188, 101, 865, 449, 471, 33, 771, 868;
    0, 0, 356, 148, 609, 110, 109, 667, 2;
    0, 0, 0, 22, 772, 628, 404, 911, 509;
    0, 0, 0, 0, 392, 245, 60, 557, 435;
    0, 0, 0, 0, 0, 11, 551, 4, 45;
    0, 0, 0, 0, 0, 0, 599, 950, 800;
    0, 0, 0, 0, 0, 0, 0, 784, 22;
    0, 0, 0, 0, 0, 0, 0, 0, 855]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt81 : residualMinor (81 : F) 1 = secondValue 81 := by
  apply value_of_factors secondLower81 secondUpper81
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower82 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    918, 1, 0, 0, 0, 0, 0, 0, 0;
    217, 960, 1, 0, 0, 0, 0, 0, 0;
    401, 359, 869, 1, 0, 0, 0, 0, 0;
    851, 236, 952, 308, 1, 0, 0, 0, 0;
    548, 328, 752, 31, 813, 1, 0, 0, 0;
    624, 817, 653, 870, 562, 678, 1, 0, 0;
    640, 989, 142, 17, 650, 839, 988, 1, 0;
    621, 135, 460, 44, 29, 325, 81, 248, 1]

private def firstUpper82 : Matrix (Fin 9) (Fin 9) F :=
  !![38, 560, 521, 956, 661, 869, 391, 608, 198;
    0, 160, 844, 106, 430, 257, 400, 732, 178;
    0, 0, 597, 1002, 960, 498, 865, 65, 408;
    0, 0, 0, 474, 990, 213, 604, 865, 545;
    0, 0, 0, 0, 877, 962, 651, 30, 667;
    0, 0, 0, 0, 0, 39, 608, 299, 451;
    0, 0, 0, 0, 0, 0, 304, 502, 165;
    0, 0, 0, 0, 0, 0, 0, 946, 519;
    0, 0, 0, 0, 0, 0, 0, 0, 90]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt82 : residualMinor (82 : F) 0 = firstValue 82 := by
  apply value_of_factors firstLower82 firstUpper82
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower82 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    776, 1, 0, 0, 0, 0, 0, 0, 0;
    321, 485, 1, 0, 0, 0, 0, 0, 0;
    14, 98, 217, 1, 0, 0, 0, 0, 0;
    560, 357, 66, 638, 1, 0, 0, 0, 0;
    528, 291, 239, 82, 559, 1, 0, 0, 0;
    557, 970, 101, 929, 906, 473, 1, 0, 0;
    638, 174, 835, 188, 106, 435, 80, 1, 0;
    313, 911, 376, 502, 613, 179, 624, 875, 1]

private def secondUpper82 : Matrix (Fin 9) (Fin 9) F :=
  !![21, 409, 819, 610, 51, 263, 524, 318, 848;
    0, 101, 982, 754, 594, 619, 137, 327, 142;
    0, 0, 78, 964, 486, 703, 975, 936, 310;
    0, 0, 0, 74, 553, 962, 26, 447, 730;
    0, 0, 0, 0, 986, 635, 981, 352, 862;
    0, 0, 0, 0, 0, 738, 508, 900, 86;
    0, 0, 0, 0, 0, 0, 238, 619, 166;
    0, 0, 0, 0, 0, 0, 0, 903, 406;
    0, 0, 0, 0, 0, 0, 0, 0, 120]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt82 : residualMinor (82 : F) 1 = secondValue 82 := by
  apply value_of_factors secondLower82 secondUpper82
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower83 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    78, 1, 0, 0, 0, 0, 0, 0, 0;
    428, 857, 1, 0, 0, 0, 0, 0, 0;
    822, 421, 757, 1, 0, 0, 0, 0, 0;
    831, 140, 112, 130, 1, 0, 0, 0, 0;
    180, 172, 376, 49, 613, 1, 0, 0, 0;
    476, 644, 959, 274, 805, 462, 1, 0, 0;
    104, 949, 924, 966, 79, 48, 575, 1, 0;
    747, 325, 528, 822, 696, 408, 733, 963, 1]

private def firstUpper83 : Matrix (Fin 9) (Fin 9) F :=
  !![90, 611, 541, 780, 645, 368, 504, 489, 166;
    0, 603, 42, 599, 81, 352, 509, 121, 901;
    0, 0, 699, 417, 775, 424, 195, 323, 466;
    0, 0, 0, 993, 936, 620, 213, 424, 771;
    0, 0, 0, 0, 890, 906, 852, 782, 397;
    0, 0, 0, 0, 0, 642, 426, 600, 941;
    0, 0, 0, 0, 0, 0, 879, 90, 394;
    0, 0, 0, 0, 0, 0, 0, 156, 960;
    0, 0, 0, 0, 0, 0, 0, 0, 72]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt83 : residualMinor (83 : F) 0 = firstValue 83 := by
  apply value_of_factors firstLower83 firstUpper83
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower83 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    662, 1, 0, 0, 0, 0, 0, 0, 0;
    362, 35, 1, 0, 0, 0, 0, 0, 0;
    523, 231, 368, 1, 0, 0, 0, 0, 0;
    364, 649, 993, 638, 1, 0, 0, 0, 0;
    999, 358, 41, 976, 870, 1, 0, 0, 0;
    674, 114, 901, 371, 350, 878, 1, 0, 0;
    958, 579, 631, 470, 429, 376, 84, 1, 0;
    672, 483, 743, 490, 789, 551, 658, 733, 1]

private def secondUpper83 : Matrix (Fin 9) (Fin 9) F :=
  !![272, 643, 323, 74, 158, 223, 280, 977, 653;
    0, 970, 953, 343, 281, 492, 766, 925, 298;
    0, 0, 916, 598, 737, 424, 279, 920, 536;
    0, 0, 0, 226, 607, 525, 224, 895, 370;
    0, 0, 0, 0, 90, 623, 728, 26, 487;
    0, 0, 0, 0, 0, 238, 1008, 462, 576;
    0, 0, 0, 0, 0, 0, 753, 991, 969;
    0, 0, 0, 0, 0, 0, 0, 774, 836;
    0, 0, 0, 0, 0, 0, 0, 0, 429]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt83 : residualMinor (83 : F) 1 = secondValue 83 := by
  apply value_of_factors secondLower83 secondUpper83
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower84 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    845, 1, 0, 0, 0, 0, 0, 0, 0;
    650, 286, 1, 0, 0, 0, 0, 0, 0;
    366, 535, 57, 1, 0, 0, 0, 0, 0;
    430, 705, 549, 821, 1, 0, 0, 0, 0;
    833, 325, 906, 969, 935, 1, 0, 0, 0;
    51, 981, 532, 9, 839, 412, 1, 0, 0;
    605, 607, 920, 227, 763, 20, 433, 1, 0;
    10, 291, 737, 380, 493, 197, 200, 165, 1]

private def firstUpper84 : Matrix (Fin 9) (Fin 9) F :=
  !![891, 108, 976, 834, 638, 218, 18, 930, 266;
    0, 13, 436, 58, 915, 855, 768, 432, 107;
    0, 0, 100, 56, 394, 159, 736, 75, 151;
    0, 0, 0, 233, 316, 338, 551, 149, 871;
    0, 0, 0, 0, 536, 977, 56, 409, 526;
    0, 0, 0, 0, 0, 666, 791, 30, 571;
    0, 0, 0, 0, 0, 0, 492, 87, 600;
    0, 0, 0, 0, 0, 0, 0, 696, 171;
    0, 0, 0, 0, 0, 0, 0, 0, 247]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt84 : residualMinor (84 : F) 0 = firstValue 84 := by
  apply value_of_factors firstLower84 firstUpper84
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower84 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    836, 1, 0, 0, 0, 0, 0, 0, 0;
    1006, 940, 1, 0, 0, 0, 0, 0, 0;
    656, 550, 433, 1, 0, 0, 0, 0, 0;
    123, 134, 707, 722, 1, 0, 0, 0, 0;
    943, 183, 799, 220, 845, 1, 0, 0, 0;
    195, 958, 332, 216, 624, 651, 1, 0, 0;
    561, 55, 859, 65, 257, 26, 568, 1, 0;
    552, 119, 192, 942, 672, 277, 790, 176, 1]

private def secondUpper84 : Matrix (Fin 9) (Fin 9) F :=
  !![698, 480, 221, 930, 891, 986, 574, 745, 522;
    0, 765, 694, 965, 985, 475, 254, 4, 375;
    0, 0, 545, 521, 762, 360, 91, 122, 33;
    0, 0, 0, 438, 960, 285, 179, 899, 672;
    0, 0, 0, 0, 958, 346, 585, 510, 102;
    0, 0, 0, 0, 0, 117, 413, 680, 171;
    0, 0, 0, 0, 0, 0, 6, 821, 943;
    0, 0, 0, 0, 0, 0, 0, 526, 947;
    0, 0, 0, 0, 0, 0, 0, 0, 604]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt84 : residualMinor (84 : F) 1 = secondValue 84 := by
  apply value_of_factors secondLower84 secondUpper84
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower85 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    717, 1, 0, 0, 0, 0, 0, 0, 0;
    306, 901, 1, 0, 0, 0, 0, 0, 0;
    290, 159, 973, 1, 0, 0, 0, 0, 0;
    810, 368, 866, 381, 1, 0, 0, 0, 0;
    86, 167, 990, 758, 676, 1, 0, 0, 0;
    606, 324, 20, 731, 686, 558, 1, 0, 0;
    209, 422, 946, 795, 37, 88, 79, 1, 0;
    622, 46, 248, 298, 313, 559, 824, 418, 1]

private def firstUpper85 : Matrix (Fin 9) (Fin 9) F :=
  !![929, 860, 711, 863, 996, 158, 821, 779, 561;
    0, 220, 245, 296, 375, 229, 262, 687, 153;
    0, 0, 417, 728, 372, 753, 583, 596, 778;
    0, 0, 0, 425, 323, 539, 289, 622, 95;
    0, 0, 0, 0, 439, 134, 636, 685, 578;
    0, 0, 0, 0, 0, 789, 7, 1008, 474;
    0, 0, 0, 0, 0, 0, 858, 229, 264;
    0, 0, 0, 0, 0, 0, 0, 650, 696;
    0, 0, 0, 0, 0, 0, 0, 0, 698]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt85 : residualMinor (85 : F) 0 = firstValue 85 := by
  apply value_of_factors firstLower85 firstUpper85
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower85 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    7, 1, 0, 0, 0, 0, 0, 0, 0;
    233, 1001, 1, 0, 0, 0, 0, 0, 0;
    738, 193, 52, 1, 0, 0, 0, 0, 0;
    738, 168, 845, 945, 1, 0, 0, 0, 0;
    29, 242, 493, 911, 554, 1, 0, 0, 0;
    87, 308, 262, 835, 655, 922, 1, 0, 0;
    844, 345, 829, 605, 307, 909, 908, 1, 0;
    654, 673, 761, 467, 629, 698, 42, 257, 1]

private def secondUpper85 : Matrix (Fin 9) (Fin 9) F :=
  !![624, 157, 148, 705, 582, 336, 199, 252, 681;
    0, 251, 460, 660, 97, 173, 288, 498, 77;
    0, 0, 288, 196, 666, 942, 857, 61, 890;
    0, 0, 0, 136, 850, 778, 940, 795, 1003;
    0, 0, 0, 0, 344, 199, 181, 109, 710;
    0, 0, 0, 0, 0, 558, 979, 966, 260;
    0, 0, 0, 0, 0, 0, 696, 348, 842;
    0, 0, 0, 0, 0, 0, 0, 702, 799;
    0, 0, 0, 0, 0, 0, 0, 0, 352]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt85 : residualMinor (85 : F) 1 = secondValue 85 := by
  apply value_of_factors secondLower85 secondUpper85
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower86 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    697, 1, 0, 0, 0, 0, 0, 0, 0;
    104, 599, 1, 0, 0, 0, 0, 0, 0;
    510, 103, 891, 1, 0, 0, 0, 0, 0;
    243, 2, 151, 85, 1, 0, 0, 0, 0;
    956, 350, 242, 499, 816, 1, 0, 0, 0;
    629, 582, 11, 809, 964, 586, 1, 0, 0;
    923, 367, 156, 954, 745, 389, 445, 1, 0;
    871, 508, 343, 17, 598, 968, 442, 502, 1]

private def firstUpper86 : Matrix (Fin 9) (Fin 9) F :=
  !![138, 704, 676, 950, 272, 702, 350, 59, 891;
    0, 2, 170, 62, 833, 275, 89, 587, 935;
    0, 0, 593, 582, 400, 304, 5, 885, 681;
    0, 0, 0, 250, 359, 220, 467, 878, 127;
    0, 0, 0, 0, 159, 487, 774, 91, 84;
    0, 0, 0, 0, 0, 345, 216, 1004, 87;
    0, 0, 0, 0, 0, 0, 894, 734, 968;
    0, 0, 0, 0, 0, 0, 0, 132, 381;
    0, 0, 0, 0, 0, 0, 0, 0, 897]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt86 : residualMinor (86 : F) 0 = firstValue 86 := by
  apply value_of_factors firstLower86 firstUpper86
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower86 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    22, 1, 0, 0, 0, 0, 0, 0, 0;
    606, 244, 1, 0, 0, 0, 0, 0, 0;
    461, 980, 243, 1, 0, 0, 0, 0, 0;
    606, 270, 841, 184, 1, 0, 0, 0, 0;
    974, 290, 537, 717, 119, 1, 0, 0, 0;
    687, 698, 181, 230, 326, 544, 1, 0, 0;
    486, 922, 807, 853, 988, 318, 843, 1, 0;
    319, 66, 212, 154, 113, 997, 520, 447, 1]

private def secondUpper86 : Matrix (Fin 9) (Fin 9) F :=
  !![498, 618, 565, 499, 357, 143, 415, 498, 144;
    0, 846, 826, 429, 943, 85, 821, 484, 277;
    0, 0, 105, 871, 501, 478, 133, 299, 112;
    0, 0, 0, 272, 434, 560, 836, 491, 488;
    0, 0, 0, 0, 950, 965, 78, 510, 181;
    0, 0, 0, 0, 0, 811, 188, 566, 343;
    0, 0, 0, 0, 0, 0, 334, 363, 346;
    0, 0, 0, 0, 0, 0, 0, 147, 354;
    0, 0, 0, 0, 0, 0, 0, 0, 265]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt86 : residualMinor (86 : F) 1 = secondValue 86 := by
  apply value_of_factors secondLower86 secondUpper86
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower87 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    495, 1, 0, 0, 0, 0, 0, 0, 0;
    75, 136, 1, 0, 0, 0, 0, 0, 0;
    597, 763, 239, 1, 0, 0, 0, 0, 0;
    964, 867, 520, 118, 1, 0, 0, 0, 0;
    991, 477, 830, 334, 185, 1, 0, 0, 0;
    895, 312, 366, 804, 145, 12, 1, 0, 0;
    820, 331, 144, 141, 186, 392, 555, 1, 0;
    791, 23, 684, 752, 430, 720, 14, 985, 1]

private def firstUpper87 : Matrix (Fin 9) (Fin 9) F :=
  !![270, 632, 446, 544, 817, 6, 881, 818, 838;
    0, 821, 215, 538, 38, 26, 476, 996, 474;
    0, 0, 950, 249, 91, 752, 864, 363, 707;
    0, 0, 0, 644, 682, 90, 862, 4, 352;
    0, 0, 0, 0, 865, 324, 259, 883, 328;
    0, 0, 0, 0, 0, 79, 794, 539, 411;
    0, 0, 0, 0, 0, 0, 737, 765, 569;
    0, 0, 0, 0, 0, 0, 0, 73, 416;
    0, 0, 0, 0, 0, 0, 0, 0, 764]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt87 : residualMinor (87 : F) 0 = firstValue 87 := by
  apply value_of_factors firstLower87 firstUpper87
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower87 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    794, 1, 0, 0, 0, 0, 0, 0, 0;
    530, 88, 1, 0, 0, 0, 0, 0, 0;
    977, 432, 837, 1, 0, 0, 0, 0, 0;
    980, 794, 974, 545, 1, 0, 0, 0, 0;
    222, 415, 595, 156, 82, 1, 0, 0, 0;
    360, 251, 699, 250, 691, 510, 1, 0, 0;
    396, 63, 305, 237, 629, 692, 840, 1, 0;
    100, 924, 408, 121, 568, 399, 661, 189, 1]

private def secondUpper87 : Matrix (Fin 9) (Fin 9) F :=
  !![659, 346, 231, 697, 781, 759, 135, 815, 762;
    0, 595, 238, 938, 265, 705, 447, 956, 957;
    0, 0, 986, 278, 596, 532, 609, 944, 158;
    0, 0, 0, 217, 275, 344, 440, 611, 442;
    0, 0, 0, 0, 785, 157, 655, 624, 333;
    0, 0, 0, 0, 0, 435, 720, 258, 943;
    0, 0, 0, 0, 0, 0, 549, 788, 822;
    0, 0, 0, 0, 0, 0, 0, 545, 106;
    0, 0, 0, 0, 0, 0, 0, 0, 690]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt87 : residualMinor (87 : F) 1 = secondValue 87 := by
  apply value_of_factors secondLower87 secondUpper87
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 80 through 87. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((80 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt80, secondAt80⟩
  · exact ⟨firstAt81, secondAt81⟩
  · exact ⟨firstAt82, secondAt82⟩
  · exact ⟨firstAt83, secondAt83⟩
  · exact ⟨firstAt84, secondAt84⟩
  · exact ⟨firstAt85, secondAt85⟩
  · exact ⟨firstAt86, secondAt86⟩
  · exact ⟨firstAt87, secondAt87⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch80
