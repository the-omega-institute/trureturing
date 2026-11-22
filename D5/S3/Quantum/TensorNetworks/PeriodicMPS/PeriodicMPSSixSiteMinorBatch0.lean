/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch0
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch0
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch0

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower0 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    874, 1, 0, 0, 0, 0, 0, 0, 0;
    886, 533, 1, 0, 0, 0, 0, 0, 0;
    419, 36, 344, 1, 0, 0, 0, 0, 0;
    891, 819, 444, 781, 1, 0, 0, 0, 0;
    213, 586, 270, 227, 759, 1, 0, 0, 0;
    938, 933, 442, 712, 112, 162, 1, 0, 0;
    124, 6, 232, 308, 350, 989, 620, 1, 0;
    992, 128, 742, 513, 462, 804, 910, 880, 1]

private def firstUpper0 : Matrix (Fin 9) (Fin 9) F :=
  !![773, 496, 985, 190, 356, 132, 285, 948, 553;
    0, 689, 120, 690, 177, 51, 17, 1008, 9;
    0, 0, 199, 631, 291, 446, 87, 337, 553;
    0, 0, 0, 159, 283, 711, 10, 133, 883;
    0, 0, 0, 0, 620, 392, 553, 409, 166;
    0, 0, 0, 0, 0, 968, 290, 528, 745;
    0, 0, 0, 0, 0, 0, 47, 540, 38;
    0, 0, 0, 0, 0, 0, 0, 70, 59;
    0, 0, 0, 0, 0, 0, 0, 0, 197]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt0 : residualMinor (0 : F) 0 = firstValue 0 := by
  apply value_of_factors firstLower0 firstUpper0
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower0 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    134, 1, 0, 0, 0, 0, 0, 0, 0;
    838, 678, 1, 0, 0, 0, 0, 0, 0;
    363, 702, 295, 1, 0, 0, 0, 0, 0;
    317, 655, 311, 662, 1, 0, 0, 0, 0;
    512, 281, 948, 306, 902, 1, 0, 0, 0;
    192, 910, 600, 251, 317, 907, 1, 0, 0;
    454, 146, 993, 791, 94, 251, 494, 1, 0;
    489, 548, 768, 850, 5, 705, 632, 36, 1]

private def secondUpper0 : Matrix (Fin 9) (Fin 9) F :=
  !![415, 121, 929, 101, 993, 271, 116, 754, 820;
    0, 253, 963, 857, 675, 403, 484, 26, 121;
    0, 0, 872, 209, 112, 426, 765, 560, 558;
    0, 0, 0, 116, 28, 976, 500, 588, 41;
    0, 0, 0, 0, 714, 544, 569, 820, 557;
    0, 0, 0, 0, 0, 328, 139, 476, 787;
    0, 0, 0, 0, 0, 0, 242, 857, 210;
    0, 0, 0, 0, 0, 0, 0, 388, 691;
    0, 0, 0, 0, 0, 0, 0, 0, 788]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt0 : residualMinor (0 : F) 1 = secondValue 0 := by
  apply value_of_factors secondLower0 secondUpper0
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower1 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    788, 1, 0, 0, 0, 0, 0, 0, 0;
    764, 993, 1, 0, 0, 0, 0, 0, 0;
    714, 996, 579, 1, 0, 0, 0, 0, 0;
    909, 25, 656, 148, 1, 0, 0, 0, 0;
    974, 308, 980, 38, 830, 1, 0, 0, 0;
    388, 865, 411, 828, 788, 892, 1, 0, 0;
    181, 121, 779, 89, 766, 74, 90, 1, 0;
    795, 758, 111, 218, 615, 869, 871, 609, 1]

private def firstUpper1 : Matrix (Fin 9) (Fin 9) F :=
  !![376, 625, 129, 934, 126, 587, 636, 275, 208;
    0, 152, 266, 747, 653, 898, 1000, 823, 470;
    0, 0, 542, 750, 3, 688, 879, 579, 712;
    0, 0, 0, 205, 174, 688, 91, 523, 137;
    0, 0, 0, 0, 263, 642, 386, 21, 832;
    0, 0, 0, 0, 0, 979, 281, 422, 934;
    0, 0, 0, 0, 0, 0, 272, 565, 437;
    0, 0, 0, 0, 0, 0, 0, 903, 158;
    0, 0, 0, 0, 0, 0, 0, 0, 746]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt1 : residualMinor (1 : F) 0 = firstValue 1 := by
  apply value_of_factors firstLower1 firstUpper1
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower1 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    388, 1, 0, 0, 0, 0, 0, 0, 0;
    9, 103, 1, 0, 0, 0, 0, 0, 0;
    571, 515, 77, 1, 0, 0, 0, 0, 0;
    879, 852, 839, 153, 1, 0, 0, 0, 0;
    985, 703, 30, 776, 234, 1, 0, 0, 0;
    492, 60, 180, 39, 170, 399, 1, 0, 0;
    151, 645, 227, 347, 776, 435, 706, 1, 0;
    579, 307, 471, 879, 156, 330, 421, 16, 1]

private def secondUpper1 : Matrix (Fin 9) (Fin 9) F :=
  !![73, 641, 604, 274, 148, 780, 349, 900, 489;
    0, 775, 754, 811, 139, 383, 489, 502, 876;
    0, 0, 645, 885, 549, 863, 558, 481, 971;
    0, 0, 0, 351, 46, 544, 997, 522, 902;
    0, 0, 0, 0, 650, 938, 850, 264, 996;
    0, 0, 0, 0, 0, 104, 271, 97, 8;
    0, 0, 0, 0, 0, 0, 4, 832, 666;
    0, 0, 0, 0, 0, 0, 0, 30, 460;
    0, 0, 0, 0, 0, 0, 0, 0, 786]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt1 : residualMinor (1 : F) 1 = secondValue 1 := by
  apply value_of_factors secondLower1 secondUpper1
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower2 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    439, 1, 0, 0, 0, 0, 0, 0, 0;
    920, 53, 1, 0, 0, 0, 0, 0, 0;
    142, 662, 441, 1, 0, 0, 0, 0, 0;
    720, 901, 206, 585, 1, 0, 0, 0, 0;
    207, 288, 560, 964, 45, 1, 0, 0, 0;
    715, 891, 130, 853, 468, 279, 1, 0, 0;
    853, 829, 586, 393, 356, 954, 6, 1, 0;
    697, 179, 293, 416, 632, 91, 118, 898, 1]

private def firstUpper2 : Matrix (Fin 9) (Fin 9) F :=
  !![825, 61, 447, 23, 979, 18, 417, 67, 628;
    0, 741, 326, 509, 528, 817, 498, 948, 84;
    0, 0, 856, 78, 257, 128, 85, 196, 984;
    0, 0, 0, 481, 439, 569, 317, 925, 650;
    0, 0, 0, 0, 205, 680, 857, 509, 659;
    0, 0, 0, 0, 0, 412, 592, 443, 39;
    0, 0, 0, 0, 0, 0, 146, 357, 104;
    0, 0, 0, 0, 0, 0, 0, 251, 931;
    0, 0, 0, 0, 0, 0, 0, 0, 597]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt2 : residualMinor (2 : F) 0 = firstValue 2 := by
  apply value_of_factors firstLower2 firstUpper2
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower2 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    453, 1, 0, 0, 0, 0, 0, 0, 0;
    343, 557, 1, 0, 0, 0, 0, 0, 0;
    957, 901, 234, 1, 0, 0, 0, 0, 0;
    803, 367, 150, 149, 1, 0, 0, 0, 0;
    815, 208, 548, 826, 492, 1, 0, 0, 0;
    546, 983, 576, 877, 86, 772, 1, 0, 0;
    553, 223, 757, 50, 754, 29, 279, 1, 0;
    674, 342, 664, 854, 320, 67, 979, 640, 1]

private def secondUpper2 : Matrix (Fin 9) (Fin 9) F :=
  !![170, 377, 723, 621, 709, 218, 163, 739, 215;
    0, 17, 210, 714, 160, 775, 750, 312, 797;
    0, 0, 848, 536, 295, 527, 27, 636, 946;
    0, 0, 0, 888, 210, 42, 305, 982, 211;
    0, 0, 0, 0, 972, 172, 688, 998, 762;
    0, 0, 0, 0, 0, 979, 451, 826, 346;
    0, 0, 0, 0, 0, 0, 441, 287, 109;
    0, 0, 0, 0, 0, 0, 0, 780, 829;
    0, 0, 0, 0, 0, 0, 0, 0, 961]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt2 : residualMinor (2 : F) 1 = secondValue 2 := by
  apply value_of_factors secondLower2 secondUpper2
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower3 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    71, 1, 0, 0, 0, 0, 0, 0, 0;
    743, 45, 1, 0, 0, 0, 0, 0, 0;
    271, 214, 828, 1, 0, 0, 0, 0, 0;
    47, 935, 466, 587, 1, 0, 0, 0, 0;
    393, 695, 608, 299, 602, 1, 0, 0, 0;
    587, 463, 890, 993, 134, 270, 1, 0, 0;
    897, 780, 837, 14, 517, 480, 277, 1, 0;
    706, 305, 168, 923, 638, 1000, 316, 840, 1]

private def firstUpper3 : Matrix (Fin 9) (Fin 9) F :=
  !![7, 752, 236, 241, 773, 558, 823, 535, 799;
    0, 79, 773, 456, 546, 506, 918, 70, 894;
    0, 0, 819, 40, 180, 857, 765, 187, 949;
    0, 0, 0, 388, 313, 243, 68, 522, 315;
    0, 0, 0, 0, 215, 642, 603, 325, 268;
    0, 0, 0, 0, 0, 945, 118, 756, 736;
    0, 0, 0, 0, 0, 0, 894, 919, 762;
    0, 0, 0, 0, 0, 0, 0, 839, 556;
    0, 0, 0, 0, 0, 0, 0, 0, 569]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt3 : residualMinor (3 : F) 0 = firstValue 3 := by
  apply value_of_factors firstLower3 firstUpper3
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower3 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    384, 1, 0, 0, 0, 0, 0, 0, 0;
    395, 81, 1, 0, 0, 0, 0, 0, 0;
    76, 846, 588, 1, 0, 0, 0, 0, 0;
    133, 732, 745, 964, 1, 0, 0, 0, 0;
    366, 10, 744, 72, 193, 1, 0, 0, 0;
    773, 518, 235, 307, 444, 509, 1, 0, 0;
    808, 963, 372, 438, 69, 943, 721, 1, 0;
    54, 906, 870, 509, 810, 239, 731, 110, 1]

private def secondUpper3 : Matrix (Fin 9) (Fin 9) F :=
  !![973, 805, 46, 398, 228, 584, 393, 234, 446;
    0, 637, 874, 950, 165, 515, 258, 667, 376;
    0, 0, 908, 778, 245, 350, 174, 117, 394;
    0, 0, 0, 765, 145, 947, 261, 458, 832;
    0, 0, 0, 0, 216, 909, 676, 464, 92;
    0, 0, 0, 0, 0, 802, 543, 424, 823;
    0, 0, 0, 0, 0, 0, 423, 41, 159;
    0, 0, 0, 0, 0, 0, 0, 167, 694;
    0, 0, 0, 0, 0, 0, 0, 0, 877]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt3 : residualMinor (3 : F) 1 = secondValue 3 := by
  apply value_of_factors secondLower3 secondUpper3
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower4 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    656, 1, 0, 0, 0, 0, 0, 0, 0;
    411, 496, 1, 0, 0, 0, 0, 0, 0;
    391, 627, 52, 1, 0, 0, 0, 0, 0;
    781, 844, 353, 626, 1, 0, 0, 0, 0;
    347, 253, 716, 683, 400, 1, 0, 0, 0;
    851, 273, 877, 153, 293, 479, 1, 0, 0;
    722, 463, 339, 569, 252, 581, 830, 1, 0;
    312, 764, 305, 83, 776, 175, 282, 449, 1]

private def firstUpper4 : Matrix (Fin 9) (Fin 9) F :=
  !![582, 795, 249, 703, 762, 791, 94, 436, 299;
    0, 811, 906, 997, 784, 486, 732, 619, 679;
    0, 0, 783, 954, 176, 187, 272, 0, 792;
    0, 0, 0, 363, 853, 445, 1002, 299, 471;
    0, 0, 0, 0, 415, 691, 817, 949, 667;
    0, 0, 0, 0, 0, 704, 631, 526, 959;
    0, 0, 0, 0, 0, 0, 826, 213, 913;
    0, 0, 0, 0, 0, 0, 0, 871, 936;
    0, 0, 0, 0, 0, 0, 0, 0, 560]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt4 : residualMinor (4 : F) 0 = firstValue 4 := by
  apply value_of_factors firstLower4 firstUpper4
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower4 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    923, 1, 0, 0, 0, 0, 0, 0, 0;
    14, 769, 1, 0, 0, 0, 0, 0, 0;
    522, 646, 789, 1, 0, 0, 0, 0, 0;
    111, 869, 683, 436, 1, 0, 0, 0, 0;
    957, 108, 78, 472, 24, 1, 0, 0, 0;
    150, 37, 725, 259, 502, 335, 1, 0, 0;
    810, 109, 608, 234, 44, 307, 493, 1, 0;
    59, 591, 928, 255, 492, 262, 262, 996, 1]

private def secondUpper4 : Matrix (Fin 9) (Fin 9) F :=
  !![602, 867, 786, 484, 10, 863, 165, 262, 764;
    0, 574, 785, 298, 43, 308, 911, 413, 187;
    0, 0, 387, 574, 48, 584, 800, 488, 239;
    0, 0, 0, 462, 147, 280, 120, 346, 223;
    0, 0, 0, 0, 668, 474, 559, 343, 118;
    0, 0, 0, 0, 0, 556, 380, 849, 49;
    0, 0, 0, 0, 0, 0, 466, 967, 177;
    0, 0, 0, 0, 0, 0, 0, 619, 190;
    0, 0, 0, 0, 0, 0, 0, 0, 128]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt4 : residualMinor (4 : F) 1 = secondValue 4 := by
  apply value_of_factors secondLower4 secondUpper4
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower5 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    993, 1, 0, 0, 0, 0, 0, 0, 0;
    931, 176, 1, 0, 0, 0, 0, 0, 0;
    51, 392, 351, 1, 0, 0, 0, 0, 0;
    517, 704, 490, 796, 1, 0, 0, 0, 0;
    625, 583, 27, 744, 916, 1, 0, 0, 0;
    714, 512, 550, 407, 731, 83, 1, 0, 0;
    704, 689, 713, 33, 362, 597, 924, 1, 0;
    910, 663, 96, 366, 864, 867, 493, 743, 1]

private def firstUpper5 : Matrix (Fin 9) (Fin 9) F :=
  !![76, 112, 813, 579, 585, 225, 817, 677, 786;
    0, 914, 378, 934, 809, 391, 416, 88, 738;
    0, 0, 54, 299, 1003, 224, 439, 836, 642;
    0, 0, 0, 200, 34, 126, 859, 180, 266;
    0, 0, 0, 0, 726, 640, 147, 20, 904;
    0, 0, 0, 0, 0, 220, 765, 143, 243;
    0, 0, 0, 0, 0, 0, 87, 725, 625;
    0, 0, 0, 0, 0, 0, 0, 370, 161;
    0, 0, 0, 0, 0, 0, 0, 0, 202]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt5 : residualMinor (5 : F) 0 = firstValue 5 := by
  apply value_of_factors firstLower5 firstUpper5
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower5 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    345, 1, 0, 0, 0, 0, 0, 0, 0;
    844, 854, 1, 0, 0, 0, 0, 0, 0;
    796, 183, 594, 1, 0, 0, 0, 0, 0;
    696, 916, 932, 439, 1, 0, 0, 0, 0;
    106, 536, 890, 520, 486, 1, 0, 0, 0;
    748, 613, 370, 311, 20, 204, 1, 0, 0;
    984, 439, 939, 311, 672, 852, 453, 1, 0;
    558, 161, 468, 850, 484, 225, 698, 905, 1]

private def secondUpper5 : Matrix (Fin 9) (Fin 9) F :=
  !![572, 774, 670, 49, 299, 663, 915, 20, 166;
    0, 486, 398, 999, 293, 126, 603, 518, 513;
    0, 0, 851, 940, 797, 813, 101, 694, 561;
    0, 0, 0, 118, 603, 825, 819, 120, 786;
    0, 0, 0, 0, 56, 295, 674, 1003, 793;
    0, 0, 0, 0, 0, 460, 530, 217, 702;
    0, 0, 0, 0, 0, 0, 893, 240, 112;
    0, 0, 0, 0, 0, 0, 0, 459, 712;
    0, 0, 0, 0, 0, 0, 0, 0, 381]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt5 : residualMinor (5 : F) 1 = secondValue 5 := by
  apply value_of_factors secondLower5 secondUpper5
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower6 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    486, 1, 0, 0, 0, 0, 0, 0, 0;
    842, 775, 1, 0, 0, 0, 0, 0, 0;
    132, 339, 506, 1, 0, 0, 0, 0, 0;
    498, 950, 743, 664, 1, 0, 0, 0, 0;
    631, 399, 545, 336, 698, 1, 0, 0, 0;
    124, 140, 253, 267, 335, 636, 1, 0, 0;
    414, 342, 778, 601, 301, 878, 53, 1, 0;
    745, 676, 105, 435, 89, 181, 55, 377, 1]

private def firstUpper6 : Matrix (Fin 9) (Fin 9) F :=
  !![22, 793, 480, 338, 985, 226, 769, 603, 809;
    0, 835, 394, 179, 909, 747, 999, 474, 586;
    0, 0, 660, 36, 228, 575, 681, 822, 669;
    0, 0, 0, 955, 295, 726, 77, 490, 498;
    0, 0, 0, 0, 417, 920, 99, 425, 91;
    0, 0, 0, 0, 0, 848, 512, 556, 766;
    0, 0, 0, 0, 0, 0, 866, 605, 28;
    0, 0, 0, 0, 0, 0, 0, 816, 414;
    0, 0, 0, 0, 0, 0, 0, 0, 908]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt6 : residualMinor (6 : F) 0 = firstValue 6 := by
  apply value_of_factors firstLower6 firstUpper6
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower6 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    386, 1, 0, 0, 0, 0, 0, 0, 0;
    596, 897, 1, 0, 0, 0, 0, 0, 0;
    782, 641, 735, 1, 0, 0, 0, 0, 0;
    39, 952, 304, 977, 1, 0, 0, 0, 0;
    751, 625, 989, 970, 906, 1, 0, 0, 0;
    930, 134, 324, 881, 160, 120, 1, 0, 0;
    621, 800, 572, 402, 108, 494, 900, 1, 0;
    4, 903, 168, 452, 618, 650, 713, 98, 1]

private def secondUpper6 : Matrix (Fin 9) (Fin 9) F :=
  !![126, 781, 982, 337, 356, 610, 75, 602, 250;
    0, 11, 927, 59, 152, 239, 705, 620, 614;
    0, 0, 688, 70, 987, 139, 677, 317, 351;
    0, 0, 0, 708, 452, 770, 680, 494, 204;
    0, 0, 0, 0, 233, 423, 900, 1000, 211;
    0, 0, 0, 0, 0, 981, 488, 610, 537;
    0, 0, 0, 0, 0, 0, 69, 368, 207;
    0, 0, 0, 0, 0, 0, 0, 400, 536;
    0, 0, 0, 0, 0, 0, 0, 0, 984]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt6 : residualMinor (6 : F) 1 = secondValue 6 := by
  apply value_of_factors secondLower6 secondUpper6
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower7 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    788, 1, 0, 0, 0, 0, 0, 0, 0;
    246, 948, 1, 0, 0, 0, 0, 0, 0;
    15, 917, 618, 1, 0, 0, 0, 0, 0;
    490, 654, 614, 709, 1, 0, 0, 0, 0;
    2, 12, 69, 68, 953, 1, 0, 0, 0;
    546, 401, 900, 548, 976, 915, 1, 0, 0;
    116, 805, 670, 456, 620, 716, 1008, 1, 0;
    985, 770, 405, 755, 896, 875, 815, 281, 1]

private def firstUpper7 : Matrix (Fin 9) (Fin 9) F :=
  !![991, 264, 47, 904, 616, 515, 919, 933, 624;
    0, 866, 155, 8, 20, 165, 388, 302, 790;
    0, 0, 427, 41, 766, 369, 192, 390, 398;
    0, 0, 0, 927, 490, 289, 899, 417, 213;
    0, 0, 0, 0, 84, 618, 478, 830, 276;
    0, 0, 0, 0, 0, 435, 28, 991, 46;
    0, 0, 0, 0, 0, 0, 572, 6, 632;
    0, 0, 0, 0, 0, 0, 0, 71, 348;
    0, 0, 0, 0, 0, 0, 0, 0, 941]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt7 : residualMinor (7 : F) 0 = firstValue 7 := by
  apply value_of_factors firstLower7 firstUpper7
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower7 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    381, 1, 0, 0, 0, 0, 0, 0, 0;
    797, 638, 1, 0, 0, 0, 0, 0, 0;
    112, 470, 152, 1, 0, 0, 0, 0, 0;
    67, 490, 572, 985, 1, 0, 0, 0, 0;
    159, 64, 578, 911, 299, 1, 0, 0, 0;
    599, 168, 543, 513, 471, 585, 1, 0, 0;
    596, 976, 236, 284, 234, 111, 429, 1, 0;
    157, 953, 455, 125, 737, 374, 353, 278, 1]

private def secondUpper7 : Matrix (Fin 9) (Fin 9) F :=
  !![346, 493, 256, 652, 260, 284, 99, 230, 353;
    0, 885, 195, 817, 930, 126, 721, 98, 823;
    0, 0, 1008, 355, 318, 959, 703, 967, 552;
    0, 0, 0, 327, 19, 224, 34, 772, 532;
    0, 0, 0, 0, 921, 911, 368, 312, 841;
    0, 0, 0, 0, 0, 524, 868, 258, 351;
    0, 0, 0, 0, 0, 0, 885, 803, 418;
    0, 0, 0, 0, 0, 0, 0, 662, 700;
    0, 0, 0, 0, 0, 0, 0, 0, 918]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt7 : residualMinor (7 : F) 1 = secondValue 7 := by
  apply value_of_factors secondLower7 secondUpper7
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 0 through 7. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((0 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt0, secondAt0⟩
  · exact ⟨firstAt1, secondAt1⟩
  · exact ⟨firstAt2, secondAt2⟩
  · exact ⟨firstAt3, secondAt3⟩
  · exact ⟨firstAt4, secondAt4⟩
  · exact ⟨firstAt5, secondAt5⟩
  · exact ⟨firstAt6, secondAt6⟩
  · exact ⟨firstAt7, secondAt7⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch0
