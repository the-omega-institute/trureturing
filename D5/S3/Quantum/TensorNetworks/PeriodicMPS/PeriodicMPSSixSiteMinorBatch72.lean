/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch72
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch72
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch72

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower72 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    911, 1, 0, 0, 0, 0, 0, 0, 0;
    379, 495, 1, 0, 0, 0, 0, 0, 0;
    655, 830, 945, 1, 0, 0, 0, 0, 0;
    352, 307, 42, 196, 1, 0, 0, 0, 0;
    619, 506, 156, 286, 729, 1, 0, 0, 0;
    7, 607, 994, 1007, 677, 712, 1, 0, 0;
    462, 171, 657, 94, 905, 262, 743, 1, 0;
    339, 91, 39, 464, 326, 606, 799, 329, 1]

private def firstUpper72 : Matrix (Fin 9) (Fin 9) F :=
  !![824, 897, 997, 604, 287, 231, 261, 319, 241;
    0, 628, 920, 802, 24, 523, 974, 649, 670;
    0, 0, 903, 600, 789, 811, 589, 337, 391;
    0, 0, 0, 707, 922, 166, 395, 939, 964;
    0, 0, 0, 0, 687, 961, 592, 32, 698;
    0, 0, 0, 0, 0, 243, 612, 810, 608;
    0, 0, 0, 0, 0, 0, 74, 89, 592;
    0, 0, 0, 0, 0, 0, 0, 183, 452;
    0, 0, 0, 0, 0, 0, 0, 0, 5]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt72 : residualMinor (72 : F) 0 = firstValue 72 := by
  apply value_of_factors firstLower72 firstUpper72
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower72 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    767, 1, 0, 0, 0, 0, 0, 0, 0;
    583, 483, 1, 0, 0, 0, 0, 0, 0;
    925, 816, 444, 1, 0, 0, 0, 0, 0;
    607, 817, 786, 154, 1, 0, 0, 0, 0;
    1001, 202, 255, 818, 40, 1, 0, 0, 0;
    661, 367, 560, 823, 663, 563, 1, 0, 0;
    361, 219, 1000, 777, 877, 704, 515, 1, 0;
    268, 803, 738, 380, 960, 451, 72, 784, 1]

private def secondUpper72 : Matrix (Fin 9) (Fin 9) F :=
  !![79, 98, 132, 636, 796, 727, 673, 353, 655;
    0, 5, 743, 676, 63, 451, 29, 327, 356;
    0, 0, 795, 849, 275, 199, 715, 51, 737;
    0, 0, 0, 116, 228, 120, 623, 1004, 57;
    0, 0, 0, 0, 155, 812, 832, 114, 46;
    0, 0, 0, 0, 0, 706, 704, 331, 78;
    0, 0, 0, 0, 0, 0, 430, 898, 105;
    0, 0, 0, 0, 0, 0, 0, 374, 686;
    0, 0, 0, 0, 0, 0, 0, 0, 714]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt72 : residualMinor (72 : F) 1 = secondValue 72 := by
  apply value_of_factors secondLower72 secondUpper72
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower73 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    665, 1, 0, 0, 0, 0, 0, 0, 0;
    617, 702, 1, 0, 0, 0, 0, 0, 0;
    604, 704, 430, 1, 0, 0, 0, 0, 0;
    128, 915, 139, 542, 1, 0, 0, 0, 0;
    291, 662, 346, 718, 289, 1, 0, 0, 0;
    511, 111, 476, 710, 25, 504, 1, 0, 0;
    688, 145, 381, 701, 375, 875, 575, 1, 0;
    52, 555, 70, 959, 1004, 829, 296, 187, 1]

private def firstUpper73 : Matrix (Fin 9) (Fin 9) F :=
  !![136, 138, 50, 272, 407, 2, 490, 917, 226;
    0, 167, 994, 662, 486, 202, 254, 204, 513;
    0, 0, 262, 76, 919, 802, 834, 159, 243;
    0, 0, 0, 799, 290, 673, 690, 360, 382;
    0, 0, 0, 0, 521, 167, 911, 65, 158;
    0, 0, 0, 0, 0, 194, 866, 319, 980;
    0, 0, 0, 0, 0, 0, 962, 270, 678;
    0, 0, 0, 0, 0, 0, 0, 258, 720;
    0, 0, 0, 0, 0, 0, 0, 0, 609]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt73 : residualMinor (73 : F) 0 = firstValue 73 := by
  apply value_of_factors firstLower73 firstUpper73
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower73 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    130, 1, 0, 0, 0, 0, 0, 0, 0;
    526, 792, 1, 0, 0, 0, 0, 0, 0;
    916, 378, 11, 1, 0, 0, 0, 0, 0;
    302, 411, 335, 980, 1, 0, 0, 0, 0;
    695, 258, 139, 284, 527, 1, 0, 0, 0;
    294, 356, 424, 989, 944, 23, 1, 0, 0;
    556, 873, 614, 340, 688, 314, 359, 1, 0;
    397, 115, 110, 918, 308, 258, 258, 881, 1]

private def secondUpper73 : Matrix (Fin 9) (Fin 9) F :=
  !![404, 150, 332, 451, 481, 823, 952, 192, 630;
    0, 798, 165, 823, 757, 487, 544, 838, 291;
    0, 0, 817, 877, 982, 259, 895, 972, 517;
    0, 0, 0, 588, 701, 178, 845, 546, 573;
    0, 0, 0, 0, 45, 21, 548, 844, 433;
    0, 0, 0, 0, 0, 904, 558, 12, 130;
    0, 0, 0, 0, 0, 0, 78, 257, 227;
    0, 0, 0, 0, 0, 0, 0, 668, 547;
    0, 0, 0, 0, 0, 0, 0, 0, 287]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt73 : residualMinor (73 : F) 1 = secondValue 73 := by
  apply value_of_factors secondLower73 secondUpper73
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower74 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    139, 1, 0, 0, 0, 0, 0, 0, 0;
    334, 606, 1, 0, 0, 0, 0, 0, 0;
    601, 957, 504, 1, 0, 0, 0, 0, 0;
    952, 922, 857, 770, 1, 0, 0, 0, 0;
    592, 676, 701, 737, 935, 1, 0, 0, 0;
    257, 766, 292, 663, 605, 567, 1, 0, 0;
    439, 922, 397, 286, 699, 481, 875, 1, 0;
    84, 151, 644, 671, 422, 497, 949, 875, 1]

private def firstUpper74 : Matrix (Fin 9) (Fin 9) F :=
  !![414, 250, 682, 513, 429, 496, 275, 446, 660;
    0, 61, 466, 929, 20, 907, 740, 147, 951;
    0, 0, 120, 755, 343, 593, 23, 478, 35;
    0, 0, 0, 229, 750, 26, 508, 230, 299;
    0, 0, 0, 0, 381, 930, 184, 916, 855;
    0, 0, 0, 0, 0, 879, 955, 62, 76;
    0, 0, 0, 0, 0, 0, 174, 473, 853;
    0, 0, 0, 0, 0, 0, 0, 206, 750;
    0, 0, 0, 0, 0, 0, 0, 0, 832]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt74 : residualMinor (74 : F) 0 = firstValue 74 := by
  apply value_of_factors firstLower74 firstUpper74
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower74 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    677, 1, 0, 0, 0, 0, 0, 0, 0;
    609, 159, 1, 0, 0, 0, 0, 0, 0;
    29, 460, 56, 1, 0, 0, 0, 0, 0;
    65, 931, 817, 676, 1, 0, 0, 0, 0;
    895, 93, 435, 370, 554, 1, 0, 0, 0;
    563, 774, 199, 145, 481, 939, 1, 0, 0;
    849, 969, 395, 134, 961, 505, 532, 1, 0;
    809, 758, 537, 725, 745, 56, 695, 126, 1]

private def secondUpper74 : Matrix (Fin 9) (Fin 9) F :=
  !![15, 242, 743, 915, 105, 339, 755, 459, 640;
    0, 129, 898, 668, 674, 779, 42, 621, 453;
    0, 0, 800, 994, 782, 149, 183, 505, 6;
    0, 0, 0, 34, 886, 776, 658, 745, 647;
    0, 0, 0, 0, 652, 44, 645, 963, 937;
    0, 0, 0, 0, 0, 871, 725, 104, 713;
    0, 0, 0, 0, 0, 0, 117, 211, 921;
    0, 0, 0, 0, 0, 0, 0, 437, 984;
    0, 0, 0, 0, 0, 0, 0, 0, 764]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt74 : residualMinor (74 : F) 1 = secondValue 74 := by
  apply value_of_factors secondLower74 secondUpper74
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower75 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    963, 1, 0, 0, 0, 0, 0, 0, 0;
    739, 267, 1, 0, 0, 0, 0, 0, 0;
    455, 943, 310, 1, 0, 0, 0, 0, 0;
    900, 150, 29, 102, 1, 0, 0, 0, 0;
    323, 532, 479, 402, 43, 1, 0, 0, 0;
    847, 997, 587, 172, 901, 807, 1, 0, 0;
    548, 982, 941, 31, 465, 951, 547, 1, 0;
    850, 58, 289, 996, 812, 928, 943, 160, 1]

private def firstUpper75 : Matrix (Fin 9) (Fin 9) F :=
  !![673, 593, 382, 512, 437, 864, 323, 816, 707;
    0, 314, 105, 92, 565, 588, 389, 155, 841;
    0, 0, 96, 9, 537, 371, 170, 940, 293;
    0, 0, 0, 369, 473, 48, 992, 528, 905;
    0, 0, 0, 0, 220, 426, 850, 704, 137;
    0, 0, 0, 0, 0, 279, 422, 531, 908;
    0, 0, 0, 0, 0, 0, 473, 160, 166;
    0, 0, 0, 0, 0, 0, 0, 575, 456;
    0, 0, 0, 0, 0, 0, 0, 0, 12]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt75 : residualMinor (75 : F) 0 = firstValue 75 := by
  apply value_of_factors firstLower75 firstUpper75
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower75 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    622, 1, 0, 0, 0, 0, 0, 0, 0;
    678, 140, 1, 0, 0, 0, 0, 0, 0;
    577, 484, 951, 1, 0, 0, 0, 0, 0;
    859, 451, 887, 359, 1, 0, 0, 0, 0;
    551, 108, 584, 874, 374, 1, 0, 0, 0;
    704, 1004, 175, 950, 424, 164, 1, 0, 0;
    356, 400, 236, 802, 645, 172, 899, 1, 0;
    904, 956, 772, 502, 826, 499, 513, 678, 1]

private def secondUpper75 : Matrix (Fin 9) (Fin 9) F :=
  !![198, 48, 828, 806, 203, 591, 23, 48, 50;
    0, 693, 269, 897, 502, 878, 486, 366, 786;
    0, 0, 968, 296, 45, 824, 792, 561, 1000;
    0, 0, 0, 828, 260, 426, 676, 392, 586;
    0, 0, 0, 0, 992, 494, 381, 891, 218;
    0, 0, 0, 0, 0, 543, 317, 175, 522;
    0, 0, 0, 0, 0, 0, 422, 600, 321;
    0, 0, 0, 0, 0, 0, 0, 319, 671;
    0, 0, 0, 0, 0, 0, 0, 0, 145]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt75 : residualMinor (75 : F) 1 = secondValue 75 := by
  apply value_of_factors secondLower75 secondUpper75
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower76 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    696, 1, 0, 0, 0, 0, 0, 0, 0;
    818, 355, 1, 0, 0, 0, 0, 0, 0;
    796, 667, 643, 1, 0, 0, 0, 0, 0;
    528, 711, 330, 981, 1, 0, 0, 0, 0;
    571, 993, 751, 1006, 519, 1, 0, 0, 0;
    6, 803, 893, 79, 829, 730, 1, 0, 0;
    450, 68, 406, 804, 572, 859, 566, 1, 0;
    65, 608, 781, 870, 626, 915, 631, 441, 1]

private def firstUpper76 : Matrix (Fin 9) (Fin 9) F :=
  !![582, 398, 771, 13, 905, 657, 848, 890, 402;
    0, 286, 60, 645, 383, 793, 993, 706, 179;
    0, 0, 220, 2, 424, 745, 936, 543, 471;
    0, 0, 0, 239, 931, 694, 588, 1002, 123;
    0, 0, 0, 0, 365, 369, 135, 760, 852;
    0, 0, 0, 0, 0, 559, 591, 374, 833;
    0, 0, 0, 0, 0, 0, 546, 247, 601;
    0, 0, 0, 0, 0, 0, 0, 245, 367;
    0, 0, 0, 0, 0, 0, 0, 0, 621]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt76 : residualMinor (76 : F) 0 = firstValue 76 := by
  apply value_of_factors firstLower76 firstUpper76
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower76 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    852, 1, 0, 0, 0, 0, 0, 0, 0;
    754, 893, 1, 0, 0, 0, 0, 0, 0;
    843, 432, 52, 1, 0, 0, 0, 0, 0;
    446, 720, 172, 508, 1, 0, 0, 0, 0;
    684, 21, 509, 380, 223, 1, 0, 0, 0;
    905, 831, 876, 604, 526, 829, 1, 0, 0;
    607, 635, 310, 935, 806, 362, 394, 1, 0;
    444, 90, 761, 43, 969, 642, 976, 596, 1]

private def secondUpper76 : Matrix (Fin 9) (Fin 9) F :=
  !![650, 230, 882, 52, 816, 271, 497, 70, 299;
    0, 614, 129, 704, 616, 148, 263, 511, 1007;
    0, 0, 116, 556, 910, 886, 621, 905, 689;
    0, 0, 0, 636, 879, 533, 638, 952, 281;
    0, 0, 0, 0, 740, 586, 998, 608, 311;
    0, 0, 0, 0, 0, 36, 586, 402, 142;
    0, 0, 0, 0, 0, 0, 623, 971, 885;
    0, 0, 0, 0, 0, 0, 0, 472, 898;
    0, 0, 0, 0, 0, 0, 0, 0, 716]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt76 : residualMinor (76 : F) 1 = secondValue 76 := by
  apply value_of_factors secondLower76 secondUpper76
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower77 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    1005, 1, 0, 0, 0, 0, 0, 0, 0;
    569, 340, 1, 0, 0, 0, 0, 0, 0;
    924, 329, 346, 1, 0, 0, 0, 0, 0;
    56, 22, 373, 390, 1, 0, 0, 0, 0;
    824, 106, 953, 799, 591, 1, 0, 0, 0;
    793, 964, 330, 477, 512, 967, 1, 0, 0;
    734, 618, 604, 696, 973, 794, 1006, 1, 0;
    731, 544, 748, 816, 212, 221, 108, 36, 1]

private def firstUpper77 : Matrix (Fin 9) (Fin 9) F :=
  !![259, 687, 300, 652, 672, 229, 936, 41, 223;
    0, 522, 70, 676, 353, 456, 453, 174, 274;
    0, 0, 534, 977, 511, 205, 94, 859, 334;
    0, 0, 0, 536, 431, 65, 372, 960, 108;
    0, 0, 0, 0, 285, 128, 217, 73, 962;
    0, 0, 0, 0, 0, 124, 125, 496, 369;
    0, 0, 0, 0, 0, 0, 302, 359, 82;
    0, 0, 0, 0, 0, 0, 0, 895, 990;
    0, 0, 0, 0, 0, 0, 0, 0, 479]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt77 : residualMinor (77 : F) 0 = firstValue 77 := by
  apply value_of_factors firstLower77 firstUpper77
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower77 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    783, 1, 0, 0, 0, 0, 0, 0, 0;
    548, 253, 1, 0, 0, 0, 0, 0, 0;
    727, 841, 22, 1, 0, 0, 0, 0, 0;
    121, 557, 827, 557, 1, 0, 0, 0, 0;
    793, 399, 900, 100, 413, 1, 0, 0, 0;
    54, 550, 590, 687, 183, 735, 1, 0, 0;
    515, 637, 477, 432, 262, 25, 60, 1, 0;
    286, 113, 411, 756, 948, 1, 221, 180, 1]

private def secondUpper77 : Matrix (Fin 9) (Fin 9) F :=
  !![640, 907, 838, 478, 913, 879, 428, 351, 313;
    0, 956, 584, 151, 185, 430, 609, 634, 499;
    0, 0, 739, 976, 166, 791, 422, 1, 303;
    0, 0, 0, 512, 504, 779, 280, 439, 154;
    0, 0, 0, 0, 882, 552, 618, 514, 163;
    0, 0, 0, 0, 0, 546, 243, 178, 152;
    0, 0, 0, 0, 0, 0, 877, 246, 139;
    0, 0, 0, 0, 0, 0, 0, 999, 955;
    0, 0, 0, 0, 0, 0, 0, 0, 234]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt77 : residualMinor (77 : F) 1 = secondValue 77 := by
  apply value_of_factors secondLower77 secondUpper77
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower78 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    298, 1, 0, 0, 0, 0, 0, 0, 0;
    217, 799, 1, 0, 0, 0, 0, 0, 0;
    131, 457, 992, 1, 0, 0, 0, 0, 0;
    166, 623, 997, 145, 1, 0, 0, 0, 0;
    63, 949, 658, 729, 1004, 1, 0, 0, 0;
    794, 89, 31, 183, 295, 591, 1, 0, 0;
    72, 385, 82, 598, 303, 645, 33, 1, 0;
    628, 978, 910, 953, 713, 482, 928, 772, 1]

private def firstUpper78 : Matrix (Fin 9) (Fin 9) F :=
  !![514, 632, 467, 209, 255, 872, 486, 305, 505;
    0, 942, 60, 81, 126, 691, 354, 354, 452;
    0, 0, 79, 120, 606, 322, 611, 746, 570;
    0, 0, 0, 553, 388, 365, 169, 574, 1005;
    0, 0, 0, 0, 810, 370, 319, 958, 306;
    0, 0, 0, 0, 0, 913, 593, 836, 454;
    0, 0, 0, 0, 0, 0, 746, 468, 784;
    0, 0, 0, 0, 0, 0, 0, 632, 29;
    0, 0, 0, 0, 0, 0, 0, 0, 82]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt78 : residualMinor (78 : F) 0 = firstValue 78 := by
  apply value_of_factors firstLower78 firstUpper78
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower78 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    855, 1, 0, 0, 0, 0, 0, 0, 0;
    920, 236, 1, 0, 0, 0, 0, 0, 0;
    6, 171, 100, 1, 0, 0, 0, 0, 0;
    475, 902, 453, 535, 1, 0, 0, 0, 0;
    227, 459, 827, 109, 390, 1, 0, 0, 0;
    657, 415, 659, 812, 558, 594, 1, 0, 0;
    369, 443, 290, 474, 750, 327, 898, 1, 0;
    873, 916, 158, 450, 930, 70, 504, 658, 1]

private def secondUpper78 : Matrix (Fin 9) (Fin 9) F :=
  !![85, 370, 11, 288, 569, 289, 281, 234, 792;
    0, 62, 669, 770, 284, 335, 782, 146, 480;
    0, 0, 525, 518, 990, 178, 333, 150, 695;
    0, 0, 0, 809, 725, 995, 104, 941, 748;
    0, 0, 0, 0, 476, 88, 871, 357, 541;
    0, 0, 0, 0, 0, 322, 72, 637, 328;
    0, 0, 0, 0, 0, 0, 578, 392, 937;
    0, 0, 0, 0, 0, 0, 0, 161, 361;
    0, 0, 0, 0, 0, 0, 0, 0, 880]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt78 : residualMinor (78 : F) 1 = secondValue 78 := by
  apply value_of_factors secondLower78 secondUpper78
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower79 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    313, 1, 0, 0, 0, 0, 0, 0, 0;
    434, 593, 1, 0, 0, 0, 0, 0, 0;
    4, 983, 282, 1, 0, 0, 0, 0, 0;
    496, 95, 203, 531, 1, 0, 0, 0, 0;
    519, 592, 563, 854, 873, 1, 0, 0, 0;
    587, 812, 623, 1007, 557, 828, 1, 0, 0;
    824, 774, 754, 956, 516, 609, 939, 1, 0;
    480, 292, 947, 910, 800, 638, 152, 799, 1]

private def firstUpper79 : Matrix (Fin 9) (Fin 9) F :=
  !![915, 699, 363, 87, 911, 357, 968, 991, 756;
    0, 123, 821, 287, 302, 342, 131, 278, 507;
    0, 0, 491, 903, 194, 446, 525, 912, 388;
    0, 0, 0, 789, 725, 667, 458, 948, 829;
    0, 0, 0, 0, 32, 808, 796, 219, 77;
    0, 0, 0, 0, 0, 908, 299, 912, 408;
    0, 0, 0, 0, 0, 0, 613, 347, 203;
    0, 0, 0, 0, 0, 0, 0, 104, 521;
    0, 0, 0, 0, 0, 0, 0, 0, 227]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt79 : residualMinor (79 : F) 0 = firstValue 79 := by
  apply value_of_factors firstLower79 firstUpper79
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower79 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    471, 1, 0, 0, 0, 0, 0, 0, 0;
    172, 291, 1, 0, 0, 0, 0, 0, 0;
    93, 124, 571, 1, 0, 0, 0, 0, 0;
    204, 194, 829, 222, 1, 0, 0, 0, 0;
    740, 540, 697, 160, 247, 1, 0, 0, 0;
    737, 620, 303, 91, 525, 374, 1, 0, 0;
    908, 152, 881, 1008, 972, 155, 516, 1, 0;
    502, 309, 933, 710, 846, 101, 243, 603, 1]

private def secondUpper79 : Matrix (Fin 9) (Fin 9) F :=
  !![516, 492, 854, 338, 697, 235, 199, 305, 878;
    0, 295, 780, 499, 545, 389, 523, 321, 172;
    0, 0, 606, 462, 538, 753, 118, 984, 259;
    0, 0, 0, 181, 91, 323, 255, 183, 566;
    0, 0, 0, 0, 112, 203, 783, 826, 873;
    0, 0, 0, 0, 0, 69, 895, 50, 156;
    0, 0, 0, 0, 0, 0, 909, 789, 385;
    0, 0, 0, 0, 0, 0, 0, 51, 326;
    0, 0, 0, 0, 0, 0, 0, 0, 196]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt79 : residualMinor (79 : F) 1 = secondValue 79 := by
  apply value_of_factors secondLower79 secondUpper79
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 72 through 79. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((72 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt72, secondAt72⟩
  · exact ⟨firstAt73, secondAt73⟩
  · exact ⟨firstAt74, secondAt74⟩
  · exact ⟨firstAt75, secondAt75⟩
  · exact ⟨firstAt76, secondAt76⟩
  · exact ⟨firstAt77, secondAt77⟩
  · exact ⟨firstAt78, secondAt78⟩
  · exact ⟨firstAt79, secondAt79⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch72
