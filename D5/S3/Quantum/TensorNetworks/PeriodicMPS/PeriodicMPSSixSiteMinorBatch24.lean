/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch24
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch24
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch24

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower24 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0, 0, 0;
    443, 103, 1, 0, 0, 0, 0, 0, 0;
    76, 478, 41, 1, 0, 0, 0, 0, 0;
    583, 798, 968, 291, 1, 0, 0, 0, 0;
    878, 902, 704, 722, 501, 1, 0, 0, 0;
    996, 826, 493, 590, 98, 878, 1, 0, 0;
    882, 758, 453, 1002, 310, 979, 231, 1, 0;
    272, 324, 558, 251, 673, 383, 24, 797, 1]

private def firstUpper24 : Matrix (Fin 9) (Fin 9) F :=
  !![937, 37, 52, 87, 269, 942, 525, 644, 139;
    0, 1004, 127, 739, 62, 593, 300, 901, 564;
    0, 0, 345, 381, 774, 244, 760, 35, 495;
    0, 0, 0, 716, 479, 138, 507, 59, 359;
    0, 0, 0, 0, 130, 614, 47, 834, 463;
    0, 0, 0, 0, 0, 557, 733, 171, 33;
    0, 0, 0, 0, 0, 0, 142, 161, 346;
    0, 0, 0, 0, 0, 0, 0, 778, 483;
    0, 0, 0, 0, 0, 0, 0, 0, 752]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt24 : residualMinor (24 : F) 0 = firstValue 24 := by
  apply value_of_factors firstLower24 firstUpper24
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower24 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    877, 1, 0, 0, 0, 0, 0, 0, 0;
    979, 793, 1, 0, 0, 0, 0, 0, 0;
    99, 205, 772, 1, 0, 0, 0, 0, 0;
    719, 978, 579, 753, 1, 0, 0, 0, 0;
    513, 223, 316, 915, 556, 1, 0, 0, 0;
    153, 971, 797, 241, 962, 141, 1, 0, 0;
    881, 215, 29, 524, 805, 736, 690, 1, 0;
    541, 403, 889, 845, 312, 829, 452, 202, 1]

private def secondUpper24 : Matrix (Fin 9) (Fin 9) F :=
  !![414, 590, 354, 221, 380, 135, 362, 515, 912;
    0, 293, 597, 911, 579, 50, 218, 183, 285;
    0, 0, 468, 610, 451, 78, 312, 247, 221;
    0, 0, 0, 346, 577, 855, 529, 132, 656;
    0, 0, 0, 0, 895, 282, 924, 506, 758;
    0, 0, 0, 0, 0, 374, 326, 593, 877;
    0, 0, 0, 0, 0, 0, 171, 730, 675;
    0, 0, 0, 0, 0, 0, 0, 122, 794;
    0, 0, 0, 0, 0, 0, 0, 0, 285]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt24 : residualMinor (24 : F) 1 = secondValue 24 := by
  apply value_of_factors secondLower24 secondUpper24
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower25 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    719, 1, 0, 0, 0, 0, 0, 0, 0;
    801, 599, 1, 0, 0, 0, 0, 0, 0;
    47, 906, 308, 1, 0, 0, 0, 0, 0;
    910, 123, 939, 719, 1, 0, 0, 0, 0;
    578, 661, 75, 774, 991, 1, 0, 0, 0;
    753, 440, 946, 210, 800, 302, 1, 0, 0;
    311, 952, 221, 83, 480, 342, 31, 1, 0;
    962, 478, 482, 355, 845, 198, 918, 710, 1]

private def firstUpper25 : Matrix (Fin 9) (Fin 9) F :=
  !![860, 482, 338, 224, 989, 134, 855, 22, 898;
    0, 667, 703, 894, 127, 396, 35, 231, 129;
    0, 0, 253, 446, 40, 957, 938, 627, 353;
    0, 0, 0, 491, 619, 1007, 363, 730, 94;
    0, 0, 0, 0, 11, 498, 350, 783, 424;
    0, 0, 0, 0, 0, 149, 241, 313, 84;
    0, 0, 0, 0, 0, 0, 930, 713, 468;
    0, 0, 0, 0, 0, 0, 0, 133, 159;
    0, 0, 0, 0, 0, 0, 0, 0, 691]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt25 : residualMinor (25 : F) 0 = firstValue 25 := by
  apply value_of_factors firstLower25 firstUpper25
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower25 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    713, 1, 0, 0, 0, 0, 0, 0, 0;
    982, 65, 1, 0, 0, 0, 0, 0, 0;
    913, 267, 741, 1, 0, 0, 0, 0, 0;
    246, 698, 404, 605, 1, 0, 0, 0, 0;
    500, 273, 803, 633, 728, 1, 0, 0, 0;
    424, 254, 457, 874, 721, 655, 1, 0, 0;
    647, 741, 747, 548, 127, 190, 111, 1, 0;
    530, 889, 181, 445, 805, 144, 165, 768, 1]

private def secondUpper25 : Matrix (Fin 9) (Fin 9) F :=
  !![758, 872, 968, 328, 739, 483, 126, 735, 55;
    0, 946, 528, 734, 673, 577, 262, 530, 167;
    0, 0, 811, 492, 986, 169, 956, 753, 532;
    0, 0, 0, 464, 42, 101, 526, 250, 862;
    0, 0, 0, 0, 61, 669, 185, 232, 732;
    0, 0, 0, 0, 0, 38, 273, 751, 42;
    0, 0, 0, 0, 0, 0, 948, 967, 621;
    0, 0, 0, 0, 0, 0, 0, 957, 978;
    0, 0, 0, 0, 0, 0, 0, 0, 330]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt25 : residualMinor (25 : F) 1 = secondValue 25 := by
  apply value_of_factors secondLower25 secondUpper25
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower26 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    803, 1, 0, 0, 0, 0, 0, 0, 0;
    873, 597, 1, 0, 0, 0, 0, 0, 0;
    487, 87, 552, 1, 0, 0, 0, 0, 0;
    304, 809, 811, 353, 1, 0, 0, 0, 0;
    317, 752, 266, 260, 623, 1, 0, 0, 0;
    407, 200, 686, 86, 201, 194, 1, 0, 0;
    96, 355, 45, 625, 366, 678, 695, 1, 0;
    473, 949, 108, 59, 585, 432, 653, 151, 1]

private def firstUpper26 : Matrix (Fin 9) (Fin 9) F :=
  !![67, 895, 871, 867, 915, 818, 611, 720, 946;
    0, 58, 65, 120, 721, 95, 879, 655, 51;
    0, 0, 722, 197, 834, 381, 385, 371, 243;
    0, 0, 0, 667, 585, 284, 292, 645, 666;
    0, 0, 0, 0, 20, 637, 631, 560, 311;
    0, 0, 0, 0, 0, 219, 742, 110, 879;
    0, 0, 0, 0, 0, 0, 580, 552, 739;
    0, 0, 0, 0, 0, 0, 0, 226, 526;
    0, 0, 0, 0, 0, 0, 0, 0, 15]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt26 : residualMinor (26 : F) 0 = firstValue 26 := by
  apply value_of_factors firstLower26 firstUpper26
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower26 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    584, 1, 0, 0, 0, 0, 0, 0, 0;
    299, 932, 1, 0, 0, 0, 0, 0, 0;
    867, 671, 665, 1, 0, 0, 0, 0, 0;
    597, 783, 765, 102, 1, 0, 0, 0, 0;
    767, 52, 256, 409, 267, 1, 0, 0, 0;
    123, 305, 906, 134, 631, 164, 1, 0, 0;
    63, 25, 512, 514, 513, 514, 121, 1, 0;
    84, 260, 34, 3, 342, 776, 386, 265, 1]

private def secondUpper26 : Matrix (Fin 9) (Fin 9) F :=
  !![681, 510, 690, 466, 948, 808, 835, 629, 928;
    0, 150, 881, 397, 214, 430, 845, 598, 802;
    0, 0, 542, 546, 506, 715, 157, 111, 115;
    0, 0, 0, 973, 255, 246, 715, 282, 56;
    0, 0, 0, 0, 402, 124, 1001, 622, 246;
    0, 0, 0, 0, 0, 648, 332, 237, 58;
    0, 0, 0, 0, 0, 0, 170, 665, 851;
    0, 0, 0, 0, 0, 0, 0, 736, 968;
    0, 0, 0, 0, 0, 0, 0, 0, 304]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt26 : residualMinor (26 : F) 1 = secondValue 26 := by
  apply value_of_factors secondLower26 secondUpper26
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower27 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    724, 1, 0, 0, 0, 0, 0, 0, 0;
    682, 955, 1, 0, 0, 0, 0, 0, 0;
    939, 450, 560, 1, 0, 0, 0, 0, 0;
    880, 374, 555, 52, 1, 0, 0, 0, 0;
    876, 988, 201, 482, 623, 1, 0, 0, 0;
    594, 83, 254, 947, 261, 805, 1, 0, 0;
    905, 285, 745, 733, 389, 466, 740, 1, 0;
    508, 292, 194, 100, 101, 830, 555, 593, 1]

private def firstUpper27 : Matrix (Fin 9) (Fin 9) F :=
  !![415, 986, 859, 194, 755, 337, 2, 883, 951;
    0, 905, 320, 638, 380, 772, 825, 274, 996;
    0, 0, 731, 435, 303, 379, 782, 132, 227;
    0, 0, 0, 231, 999, 903, 482, 364, 68;
    0, 0, 0, 0, 144, 333, 712, 576, 252;
    0, 0, 0, 0, 0, 309, 628, 599, 612;
    0, 0, 0, 0, 0, 0, 851, 521, 172;
    0, 0, 0, 0, 0, 0, 0, 277, 730;
    0, 0, 0, 0, 0, 0, 0, 0, 916]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt27 : residualMinor (27 : F) 0 = firstValue 27 := by
  apply value_of_factors firstLower27 firstUpper27
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower27 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    730, 1, 0, 0, 0, 0, 0, 0, 0;
    843, 214, 1, 0, 0, 0, 0, 0, 0;
    242, 160, 0, 1, 0, 0, 0, 0, 0;
    570, 756, 776, 876, 1, 0, 0, 0, 0;
    132, 285, 924, 170, 290, 1, 0, 0, 0;
    687, 116, 996, 332, 677, 755, 1, 0, 0;
    60, 36, 581, 975, 607, 519, 342, 1, 0;
    444, 199, 211, 478, 697, 336, 751, 419, 1]

private def secondUpper27 : Matrix (Fin 9) (Fin 9) F :=
  !![582, 204, 131, 851, 371, 9, 209, 842, 922;
    0, 809, 917, 148, 713, 66, 44, 690, 316;
    0, 0, 278, 31, 97, 329, 27, 488, 387;
    0, 0, 0, 164, 211, 544, 189, 203, 37;
    0, 0, 0, 0, 27, 553, 343, 413, 846;
    0, 0, 0, 0, 0, 596, 926, 487, 164;
    0, 0, 0, 0, 0, 0, 95, 999, 749;
    0, 0, 0, 0, 0, 0, 0, 959, 116;
    0, 0, 0, 0, 0, 0, 0, 0, 461]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt27 : residualMinor (27 : F) 1 = secondValue 27 := by
  apply value_of_factors secondLower27 secondUpper27
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower28 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    328, 1, 0, 0, 0, 0, 0, 0, 0;
    480, 510, 1, 0, 0, 0, 0, 0, 0;
    991, 495, 801, 1, 0, 0, 0, 0, 0;
    835, 939, 708, 400, 1, 0, 0, 0, 0;
    815, 16, 1004, 313, 766, 1, 0, 0, 0;
    94, 570, 867, 584, 334, 777, 1, 0, 0;
    972, 498, 939, 219, 864, 121, 137, 1, 0;
    53, 984, 798, 111, 138, 444, 958, 520, 1]

private def firstUpper28 : Matrix (Fin 9) (Fin 9) F :=
  !![484, 940, 40, 295, 360, 1001, 134, 292, 642;
    0, 695, 414, 930, 835, 124, 69, 604, 372;
    0, 0, 167, 957, 729, 635, 450, 815, 570;
    0, 0, 0, 278, 182, 826, 586, 77, 322;
    0, 0, 0, 0, 534, 113, 517, 35, 297;
    0, 0, 0, 0, 0, 749, 632, 406, 547;
    0, 0, 0, 0, 0, 0, 603, 676, 567;
    0, 0, 0, 0, 0, 0, 0, 759, 860;
    0, 0, 0, 0, 0, 0, 0, 0, 939]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt28 : residualMinor (28 : F) 0 = firstValue 28 := by
  apply value_of_factors firstLower28 firstUpper28
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower28 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    578, 1, 0, 0, 0, 0, 0, 0, 0;
    581, 26, 1, 0, 0, 0, 0, 0, 0;
    555, 690, 751, 1, 0, 0, 0, 0, 0;
    434, 808, 292, 985, 1, 0, 0, 0, 0;
    307, 553, 533, 882, 982, 1, 0, 0, 0;
    45, 98, 847, 126, 453, 151, 1, 0, 0;
    246, 993, 458, 773, 369, 555, 708, 1, 0;
    510, 976, 13, 231, 927, 416, 374, 290, 1]

private def secondUpper28 : Matrix (Fin 9) (Fin 9) F :=
  !![383, 246, 696, 944, 831, 255, 760, 77, 519;
    0, 342, 720, 54, 828, 451, 269, 415, 767;
    0, 0, 130, 395, 194, 45, 520, 987, 394;
    0, 0, 0, 810, 411, 728, 249, 401, 627;
    0, 0, 0, 0, 341, 368, 818, 637, 841;
    0, 0, 0, 0, 0, 61, 879, 524, 559;
    0, 0, 0, 0, 0, 0, 305, 435, 305;
    0, 0, 0, 0, 0, 0, 0, 948, 550;
    0, 0, 0, 0, 0, 0, 0, 0, 422]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt28 : residualMinor (28 : F) 1 = secondValue 28 := by
  apply value_of_factors secondLower28 secondUpper28
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower29 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    671, 1, 0, 0, 0, 0, 0, 0, 0;
    480, 918, 1, 0, 0, 0, 0, 0, 0;
    116, 6, 749, 1, 0, 0, 0, 0, 0;
    705, 147, 485, 730, 1, 0, 0, 0, 0;
    426, 707, 696, 962, 118, 1, 0, 0, 0;
    167, 697, 402, 982, 751, 155, 1, 0, 0;
    185, 601, 304, 980, 506, 468, 823, 1, 0;
    803, 57, 127, 219, 293, 867, 116, 711, 1]

private def firstUpper29 : Matrix (Fin 9) (Fin 9) F :=
  !![228, 109, 147, 676, 945, 865, 950, 656, 872;
    0, 265, 258, 441, 285, 37, 472, 852, 903;
    0, 0, 303, 454, 211, 923, 464, 288, 504;
    0, 0, 0, 895, 317, 574, 884, 721, 59;
    0, 0, 0, 0, 377, 958, 427, 846, 13;
    0, 0, 0, 0, 0, 98, 67, 225, 591;
    0, 0, 0, 0, 0, 0, 459, 27, 116;
    0, 0, 0, 0, 0, 0, 0, 952, 92;
    0, 0, 0, 0, 0, 0, 0, 0, 679]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt29 : residualMinor (29 : F) 0 = firstValue 29 := by
  apply value_of_factors firstLower29 firstUpper29
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower29 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    918, 1, 0, 0, 0, 0, 0, 0, 0;
    695, 575, 1, 0, 0, 0, 0, 0, 0;
    311, 569, 1008, 1, 0, 0, 0, 0, 0;
    940, 557, 245, 833, 1, 0, 0, 0, 0;
    1004, 536, 208, 230, 40, 1, 0, 0, 0;
    297, 219, 601, 366, 632, 770, 1, 0, 0;
    358, 813, 754, 405, 487, 370, 972, 1, 0;
    502, 392, 803, 463, 354, 192, 348, 343, 1]

private def secondUpper29 : Matrix (Fin 9) (Fin 9) F :=
  !![931, 417, 821, 489, 783, 895, 706, 218, 221;
    0, 361, 58, 90, 342, 1002, 913, 762, 726;
    0, 0, 408, 152, 840, 592, 240, 117, 943;
    0, 0, 0, 922, 918, 67, 104, 200, 216;
    0, 0, 0, 0, 866, 685, 707, 127, 840;
    0, 0, 0, 0, 0, 898, 1002, 745, 400;
    0, 0, 0, 0, 0, 0, 916, 974, 847;
    0, 0, 0, 0, 0, 0, 0, 592, 432;
    0, 0, 0, 0, 0, 0, 0, 0, 266]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt29 : residualMinor (29 : F) 1 = secondValue 29 := by
  apply value_of_factors secondLower29 secondUpper29
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower30 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    873, 1, 0, 0, 0, 0, 0, 0, 0;
    344, 56, 1, 0, 0, 0, 0, 0, 0;
    493, 789, 714, 1, 0, 0, 0, 0, 0;
    273, 168, 887, 278, 1, 0, 0, 0, 0;
    255, 567, 49, 987, 905, 1, 0, 0, 0;
    647, 30, 521, 460, 59, 79, 1, 0, 0;
    318, 585, 73, 443, 297, 14, 645, 1, 0;
    853, 927, 101, 419, 980, 709, 309, 935, 1]

private def firstUpper30 : Matrix (Fin 9) (Fin 9) F :=
  !![675, 529, 540, 369, 263, 19, 418, 694, 451;
    0, 819, 102, 281, 129, 263, 289, 619, 236;
    0, 0, 448, 912, 609, 83, 843, 485, 438;
    0, 0, 0, 590, 297, 286, 507, 548, 108;
    0, 0, 0, 0, 745, 809, 830, 797, 402;
    0, 0, 0, 0, 0, 399, 857, 814, 922;
    0, 0, 0, 0, 0, 0, 646, 997, 127;
    0, 0, 0, 0, 0, 0, 0, 346, 925;
    0, 0, 0, 0, 0, 0, 0, 0, 421]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt30 : residualMinor (30 : F) 0 = firstValue 30 := by
  apply value_of_factors firstLower30 firstUpper30
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower30 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    248, 1, 0, 0, 0, 0, 0, 0, 0;
    259, 302, 1, 0, 0, 0, 0, 0, 0;
    337, 713, 240, 1, 0, 0, 0, 0, 0;
    868, 826, 114, 272, 1, 0, 0, 0, 0;
    358, 548, 812, 720, 518, 1, 0, 0, 0;
    199, 176, 216, 586, 857, 835, 1, 0, 0;
    637, 890, 269, 510, 957, 411, 512, 1, 0;
    122, 649, 283, 89, 900, 728, 935, 19, 1]

private def secondUpper30 : Matrix (Fin 9) (Fin 9) F :=
  !![468, 799, 566, 347, 711, 62, 142, 276, 385;
    0, 126, 202, 256, 932, 465, 44, 236, 824;
    0, 0, 466, 615, 977, 65, 772, 968, 846;
    0, 0, 0, 899, 172, 202, 113, 678, 872;
    0, 0, 0, 0, 212, 704, 945, 204, 111;
    0, 0, 0, 0, 0, 990, 902, 863, 825;
    0, 0, 0, 0, 0, 0, 664, 980, 222;
    0, 0, 0, 0, 0, 0, 0, 388, 144;
    0, 0, 0, 0, 0, 0, 0, 0, 132]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt30 : residualMinor (30 : F) 1 = secondValue 30 := by
  apply value_of_factors secondLower30 secondUpper30
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower31 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    588, 1, 0, 0, 0, 0, 0, 0, 0;
    173, 242, 1, 0, 0, 0, 0, 0, 0;
    477, 1007, 976, 1, 0, 0, 0, 0, 0;
    609, 96, 30, 766, 1, 0, 0, 0, 0;
    1008, 269, 61, 504, 887, 1, 0, 0, 0;
    234, 931, 507, 84, 367, 679, 1, 0, 0;
    657, 812, 391, 838, 979, 786, 621, 1, 0;
    14, 235, 99, 340, 626, 529, 4, 156, 1]

private def firstUpper31 : Matrix (Fin 9) (Fin 9) F :=
  !![946, 69, 766, 48, 818, 568, 977, 833, 188;
    0, 174, 332, 189, 469, 920, 129, 403, 937;
    0, 0, 832, 542, 414, 459, 583, 254, 842;
    0, 0, 0, 440, 840, 491, 504, 500, 573;
    0, 0, 0, 0, 128, 575, 112, 253, 823;
    0, 0, 0, 0, 0, 213, 114, 595, 420;
    0, 0, 0, 0, 0, 0, 953, 238, 235;
    0, 0, 0, 0, 0, 0, 0, 898, 372;
    0, 0, 0, 0, 0, 0, 0, 0, 922]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt31 : residualMinor (31 : F) 0 = firstValue 31 := by
  apply value_of_factors firstLower31 firstUpper31
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower31 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    202, 1, 0, 0, 0, 0, 0, 0, 0;
    76, 8, 1, 0, 0, 0, 0, 0, 0;
    184, 74, 551, 1, 0, 0, 0, 0, 0;
    967, 913, 752, 749, 1, 0, 0, 0, 0;
    709, 367, 130, 357, 857, 1, 0, 0, 0;
    594, 760, 150, 225, 556, 143, 1, 0, 0;
    331, 135, 898, 36, 213, 748, 691, 1, 0;
    356, 956, 275, 791, 635, 863, 445, 579, 1]

private def secondUpper31 : Matrix (Fin 9) (Fin 9) F :=
  !![223, 552, 748, 496, 36, 339, 47, 545, 622;
    0, 881, 980, 869, 960, 50, 71, 733, 972;
    0, 0, 683, 855, 832, 571, 936, 877, 245;
    0, 0, 0, 950, 761, 877, 136, 127, 549;
    0, 0, 0, 0, 329, 625, 189, 32, 721;
    0, 0, 0, 0, 0, 300, 906, 45, 849;
    0, 0, 0, 0, 0, 0, 742, 286, 401;
    0, 0, 0, 0, 0, 0, 0, 872, 419;
    0, 0, 0, 0, 0, 0, 0, 0, 952]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt31 : residualMinor (31 : F) 1 = secondValue 31 := by
  apply value_of_factors secondLower31 secondUpper31
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 24 through 31. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((24 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt24, secondAt24⟩
  · exact ⟨firstAt25, secondAt25⟩
  · exact ⟨firstAt26, secondAt26⟩
  · exact ⟨firstAt27, secondAt27⟩
  · exact ⟨firstAt28, secondAt28⟩
  · exact ⟨firstAt29, secondAt29⟩
  · exact ⟨firstAt30, secondAt30⟩
  · exact ⟨firstAt31, secondAt31⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch24
