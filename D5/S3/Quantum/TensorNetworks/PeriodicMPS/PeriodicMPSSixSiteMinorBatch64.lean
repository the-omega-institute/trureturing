/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch64
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch64
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch64

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower64 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    627, 1, 0, 0, 0, 0, 0, 0, 0;
    523, 896, 1, 0, 0, 0, 0, 0, 0;
    867, 543, 10, 1, 0, 0, 0, 0, 0;
    524, 118, 84, 133, 1, 0, 0, 0, 0;
    240, 700, 239, 317, 28, 1, 0, 0, 0;
    942, 841, 374, 333, 574, 180, 1, 0, 0;
    932, 190, 240, 518, 343, 787, 502, 1, 0;
    718, 336, 84, 148, 255, 544, 573, 83, 1]

private def firstUpper64 : Matrix (Fin 9) (Fin 9) F :=
  !![400, 967, 628, 104, 503, 611, 94, 123, 99;
    0, 198, 552, 706, 163, 706, 677, 255, 923;
    0, 0, 687, 33, 60, 337, 764, 253, 566;
    0, 0, 0, 491, 782, 236, 584, 535, 148;
    0, 0, 0, 0, 469, 86, 352, 880, 225;
    0, 0, 0, 0, 0, 325, 87, 511, 839;
    0, 0, 0, 0, 0, 0, 38, 24, 494;
    0, 0, 0, 0, 0, 0, 0, 272, 378;
    0, 0, 0, 0, 0, 0, 0, 0, 6]

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
    677, 1, 0, 0, 0, 0, 0, 0, 0;
    54, 674, 1, 0, 0, 0, 0, 0, 0;
    647, 752, 33, 1, 0, 0, 0, 0, 0;
    289, 200, 613, 993, 1, 0, 0, 0, 0;
    707, 130, 597, 156, 477, 1, 0, 0, 0;
    410, 327, 671, 787, 568, 284, 1, 0, 0;
    901, 894, 658, 572, 702, 931, 853, 1, 0;
    214, 496, 267, 393, 796, 481, 951, 821, 1]

private def secondUpper64 : Matrix (Fin 9) (Fin 9) F :=
  !![631, 31, 851, 120, 167, 738, 4, 660, 879;
    0, 300, 810, 818, 685, 212, 403, 859, 665;
    0, 0, 768, 37, 18, 868, 251, 327, 255;
    0, 0, 0, 312, 102, 915, 128, 853, 951;
    0, 0, 0, 0, 901, 900, 438, 717, 795;
    0, 0, 0, 0, 0, 872, 244, 658, 196;
    0, 0, 0, 0, 0, 0, 540, 334, 823;
    0, 0, 0, 0, 0, 0, 0, 801, 653;
    0, 0, 0, 0, 0, 0, 0, 0, 643]

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
    843, 1, 0, 0, 0, 0, 0, 0, 0;
    691, 797, 1, 0, 0, 0, 0, 0, 0;
    575, 1007, 761, 1, 0, 0, 0, 0, 0;
    57, 742, 43, 103, 1, 0, 0, 0, 0;
    68, 643, 858, 639, 707, 1, 0, 0, 0;
    294, 938, 428, 781, 934, 886, 1, 0, 0;
    179, 411, 612, 335, 877, 57, 276, 1, 0;
    564, 662, 522, 662, 947, 337, 391, 853, 1]

private def firstUpper65 : Matrix (Fin 9) (Fin 9) F :=
  !![846, 251, 272, 986, 108, 281, 205, 14, 291;
    0, 469, 571, 409, 198, 580, 818, 193, 762;
    0, 0, 895, 874, 285, 114, 772, 31, 203;
    0, 0, 0, 195, 703, 839, 725, 34, 300;
    0, 0, 0, 0, 985, 501, 676, 52, 748;
    0, 0, 0, 0, 0, 48, 751, 627, 114;
    0, 0, 0, 0, 0, 0, 351, 948, 507;
    0, 0, 0, 0, 0, 0, 0, 546, 492;
    0, 0, 0, 0, 0, 0, 0, 0, 743]

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
    463, 1, 0, 0, 0, 0, 0, 0, 0;
    657, 79, 1, 0, 0, 0, 0, 0, 0;
    183, 745, 569, 1, 0, 0, 0, 0, 0;
    651, 581, 706, 999, 1, 0, 0, 0, 0;
    614, 13, 92, 260, 423, 1, 0, 0, 0;
    59, 219, 986, 754, 126, 601, 1, 0, 0;
    654, 799, 564, 41, 97, 628, 795, 1, 0;
    372, 549, 89, 642, 908, 56, 299, 297, 1]

private def secondUpper65 : Matrix (Fin 9) (Fin 9) F :=
  !![388, 217, 825, 2, 49, 122, 572, 51, 450;
    0, 601, 251, 274, 952, 366, 616, 490, 392;
    0, 0, 351, 429, 202, 599, 611, 499, 687;
    0, 0, 0, 869, 88, 646, 46, 573, 260;
    0, 0, 0, 0, 334, 216, 893, 35, 646;
    0, 0, 0, 0, 0, 341, 178, 722, 712;
    0, 0, 0, 0, 0, 0, 236, 36, 711;
    0, 0, 0, 0, 0, 0, 0, 281, 384;
    0, 0, 0, 0, 0, 0, 0, 0, 913]

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
    612, 1, 0, 0, 0, 0, 0, 0, 0;
    860, 961, 1, 0, 0, 0, 0, 0, 0;
    796, 277, 682, 1, 0, 0, 0, 0, 0;
    816, 799, 472, 701, 1, 0, 0, 0, 0;
    390, 61, 0, 724, 12, 1, 0, 0, 0;
    871, 272, 221, 123, 94, 504, 1, 0, 0;
    378, 527, 448, 6, 898, 447, 670, 1, 0;
    832, 187, 211, 247, 831, 906, 338, 441, 1]

private def firstUpper66 : Matrix (Fin 9) (Fin 9) F :=
  !![940, 198, 982, 730, 790, 211, 859, 967, 558;
    0, 910, 624, 263, 641, 127, 50, 264, 455;
    0, 0, 854, 779, 333, 320, 390, 830, 614;
    0, 0, 0, 317, 4, 370, 1004, 344, 443;
    0, 0, 0, 0, 827, 535, 468, 814, 514;
    0, 0, 0, 0, 0, 276, 397, 235, 868;
    0, 0, 0, 0, 0, 0, 377, 437, 513;
    0, 0, 0, 0, 0, 0, 0, 329, 985;
    0, 0, 0, 0, 0, 0, 0, 0, 128]

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
    398, 1, 0, 0, 0, 0, 0, 0, 0;
    334, 708, 1, 0, 0, 0, 0, 0, 0;
    930, 841, 34, 1, 0, 0, 0, 0, 0;
    823, 12, 1000, 527, 1, 0, 0, 0, 0;
    187, 982, 1007, 995, 856, 1, 0, 0, 0;
    437, 646, 291, 117, 928, 127, 1, 0, 0;
    707, 988, 390, 618, 845, 399, 700, 1, 0;
    238, 398, 43, 77, 61, 803, 495, 420, 1]

private def secondUpper66 : Matrix (Fin 9) (Fin 9) F :=
  !![24, 605, 695, 177, 527, 289, 700, 440, 818;
    0, 358, 100, 220, 936, 111, 962, 231, 243;
    0, 0, 929, 504, 960, 570, 427, 734, 281;
    0, 0, 0, 461, 47, 893, 592, 880, 611;
    0, 0, 0, 0, 892, 114, 927, 444, 360;
    0, 0, 0, 0, 0, 582, 53, 102, 560;
    0, 0, 0, 0, 0, 0, 962, 913, 461;
    0, 0, 0, 0, 0, 0, 0, 25, 852;
    0, 0, 0, 0, 0, 0, 0, 0, 852]

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
    102, 1, 0, 0, 0, 0, 0, 0, 0;
    821, 221, 1, 0, 0, 0, 0, 0, 0;
    727, 433, 697, 1, 0, 0, 0, 0, 0;
    445, 241, 436, 229, 1, 0, 0, 0, 0;
    690, 267, 880, 618, 213, 1, 0, 0, 0;
    173, 636, 932, 52, 545, 731, 1, 0, 0;
    304, 461, 150, 764, 407, 466, 81, 1, 0;
    110, 402, 954, 197, 418, 211, 732, 502, 1]

private def firstUpper67 : Matrix (Fin 9) (Fin 9) F :=
  !![349, 646, 361, 708, 963, 221, 477, 951, 298;
    0, 131, 494, 204, 362, 1, 850, 641, 912;
    0, 0, 208, 370, 438, 816, 729, 680, 782;
    0, 0, 0, 841, 359, 334, 868, 453, 221;
    0, 0, 0, 0, 60, 473, 510, 345, 267;
    0, 0, 0, 0, 0, 753, 54, 131, 746;
    0, 0, 0, 0, 0, 0, 718, 338, 604;
    0, 0, 0, 0, 0, 0, 0, 724, 257;
    0, 0, 0, 0, 0, 0, 0, 0, 265]

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
    45, 1, 0, 0, 0, 0, 0, 0, 0;
    298, 656, 1, 0, 0, 0, 0, 0, 0;
    701, 205, 151, 1, 0, 0, 0, 0, 0;
    372, 335, 227, 273, 1, 0, 0, 0, 0;
    595, 172, 680, 211, 517, 1, 0, 0, 0;
    147, 305, 51, 322, 262, 825, 1, 0, 0;
    794, 281, 882, 445, 799, 363, 221, 1, 0;
    289, 71, 930, 697, 111, 685, 582, 150, 1]

private def secondUpper67 : Matrix (Fin 9) (Fin 9) F :=
  !![903, 532, 251, 985, 140, 446, 882, 879, 26;
    0, 714, 796, 852, 469, 455, 733, 575, 877;
    0, 0, 499, 296, 26, 313, 979, 441, 147;
    0, 0, 0, 370, 686, 536, 698, 974, 257;
    0, 0, 0, 0, 194, 650, 263, 797, 227;
    0, 0, 0, 0, 0, 596, 713, 826, 654;
    0, 0, 0, 0, 0, 0, 399, 830, 937;
    0, 0, 0, 0, 0, 0, 0, 30, 226;
    0, 0, 0, 0, 0, 0, 0, 0, 73]

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
    956, 1, 0, 0, 0, 0, 0, 0, 0;
    638, 328, 1, 0, 0, 0, 0, 0, 0;
    125, 591, 276, 1, 0, 0, 0, 0, 0;
    211, 686, 825, 249, 1, 0, 0, 0, 0;
    669, 830, 166, 526, 304, 1, 0, 0, 0;
    583, 828, 88, 679, 267, 155, 1, 0, 0;
    249, 99, 918, 334, 314, 310, 238, 1, 0;
    819, 351, 706, 529, 859, 286, 557, 267, 1]

private def firstUpper68 : Matrix (Fin 9) (Fin 9) F :=
  !![560, 893, 667, 982, 803, 574, 782, 577, 501;
    0, 623, 523, 854, 342, 10, 1003, 565, 218;
    0, 0, 580, 262, 851, 390, 932, 588, 905;
    0, 0, 0, 294, 978, 794, 270, 795, 30;
    0, 0, 0, 0, 210, 961, 879, 693, 15;
    0, 0, 0, 0, 0, 691, 455, 949, 346;
    0, 0, 0, 0, 0, 0, 997, 168, 571;
    0, 0, 0, 0, 0, 0, 0, 574, 987;
    0, 0, 0, 0, 0, 0, 0, 0, 788]

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
    429, 1, 0, 0, 0, 0, 0, 0, 0;
    717, 643, 1, 0, 0, 0, 0, 0, 0;
    599, 952, 605, 1, 0, 0, 0, 0, 0;
    752, 186, 445, 757, 1, 0, 0, 0, 0;
    171, 586, 45, 333, 360, 1, 0, 0, 0;
    710, 820, 439, 958, 93, 277, 1, 0, 0;
    996, 917, 355, 752, 423, 584, 523, 1, 0;
    327, 976, 513, 106, 584, 897, 666, 34, 1]

private def secondUpper68 : Matrix (Fin 9) (Fin 9) F :=
  !![727, 513, 676, 703, 151, 6, 348, 805, 555;
    0, 602, 66, 371, 967, 311, 966, 996, 937;
    0, 0, 919, 828, 229, 131, 556, 343, 48;
    0, 0, 0, 980, 227, 901, 169, 761, 9;
    0, 0, 0, 0, 719, 58, 559, 673, 80;
    0, 0, 0, 0, 0, 586, 912, 809, 0;
    0, 0, 0, 0, 0, 0, 191, 867, 355;
    0, 0, 0, 0, 0, 0, 0, 952, 418;
    0, 0, 0, 0, 0, 0, 0, 0, 188]

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
    845, 1, 0, 0, 0, 0, 0, 0, 0;
    519, 527, 1, 0, 0, 0, 0, 0, 0;
    129, 497, 780, 1, 0, 0, 0, 0, 0;
    252, 228, 1004, 968, 1, 0, 0, 0, 0;
    133, 705, 719, 349, 931, 1, 0, 0, 0;
    21, 726, 951, 897, 62, 1003, 1, 0, 0;
    510, 720, 618, 304, 754, 226, 824, 1, 0;
    779, 595, 975, 942, 578, 52, 340, 404, 1]

private def firstUpper69 : Matrix (Fin 9) (Fin 9) F :=
  !![963, 13, 847, 567, 999, 322, 273, 871, 582;
    0, 697, 312, 246, 560, 23, 991, 568, 999;
    0, 0, 571, 402, 949, 116, 832, 471, 561;
    0, 0, 0, 68, 562, 161, 929, 584, 584;
    0, 0, 0, 0, 552, 205, 630, 876, 486;
    0, 0, 0, 0, 0, 268, 32, 912, 628;
    0, 0, 0, 0, 0, 0, 189, 834, 162;
    0, 0, 0, 0, 0, 0, 0, 196, 113;
    0, 0, 0, 0, 0, 0, 0, 0, 778]

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
    196, 1, 0, 0, 0, 0, 0, 0, 0;
    360, 47, 1, 0, 0, 0, 0, 0, 0;
    201, 40, 26, 1, 0, 0, 0, 0, 0;
    637, 408, 611, 116, 1, 0, 0, 0, 0;
    315, 373, 180, 36, 830, 1, 0, 0, 0;
    1005, 742, 943, 139, 331, 264, 1, 0, 0;
    115, 754, 734, 730, 124, 582, 907, 1, 0;
    858, 350, 362, 773, 274, 571, 810, 997, 1]

private def secondUpper69 : Matrix (Fin 9) (Fin 9) F :=
  !![333, 778, 250, 181, 931, 234, 517, 451, 521;
    0, 454, 78, 934, 335, 233, 183, 389, 190;
    0, 0, 368, 451, 514, 417, 870, 119, 968;
    0, 0, 0, 795, 753, 739, 470, 491, 480;
    0, 0, 0, 0, 12, 288, 621, 159, 975;
    0, 0, 0, 0, 0, 433, 83, 352, 815;
    0, 0, 0, 0, 0, 0, 701, 766, 589;
    0, 0, 0, 0, 0, 0, 0, 128, 657;
    0, 0, 0, 0, 0, 0, 0, 0, 167]

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
    918, 1, 0, 0, 0, 0, 0, 0, 0;
    358, 719, 1, 0, 0, 0, 0, 0, 0;
    390, 278, 971, 1, 0, 0, 0, 0, 0;
    749, 809, 270, 355, 1, 0, 0, 0, 0;
    40, 478, 34, 984, 795, 1, 0, 0, 0;
    595, 162, 319, 440, 89, 996, 1, 0, 0;
    511, 18, 584, 362, 676, 933, 431, 1, 0;
    407, 225, 872, 931, 930, 824, 856, 149, 1]

private def firstUpper70 : Matrix (Fin 9) (Fin 9) F :=
  !![911, 716, 599, 863, 147, 815, 132, 627, 625;
    0, 179, 679, 641, 451, 730, 884, 999, 924;
    0, 0, 685, 844, 394, 356, 577, 73, 476;
    0, 0, 0, 165, 902, 709, 182, 857, 170;
    0, 0, 0, 0, 899, 925, 796, 645, 331;
    0, 0, 0, 0, 0, 543, 652, 87, 823;
    0, 0, 0, 0, 0, 0, 454, 53, 534;
    0, 0, 0, 0, 0, 0, 0, 645, 214;
    0, 0, 0, 0, 0, 0, 0, 0, 669]

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
    90, 1, 0, 0, 0, 0, 0, 0, 0;
    37, 339, 1, 0, 0, 0, 0, 0, 0;
    745, 457, 585, 1, 0, 0, 0, 0, 0;
    672, 618, 600, 929, 1, 0, 0, 0, 0;
    656, 838, 478, 950, 521, 1, 0, 0, 0;
    889, 427, 667, 414, 405, 425, 1, 0, 0;
    885, 972, 20, 893, 901, 45, 290, 1, 0;
    747, 676, 572, 434, 171, 36, 253, 328, 1]

private def secondUpper70 : Matrix (Fin 9) (Fin 9) F :=
  !![498, 739, 939, 216, 792, 43, 1008, 337, 421;
    0, 692, 902, 541, 550, 388, 61, 386, 1005;
    0, 0, 576, 120, 95, 780, 883, 369, 567;
    0, 0, 0, 468, 171, 733, 195, 101, 632;
    0, 0, 0, 0, 124, 938, 683, 837, 319;
    0, 0, 0, 0, 0, 734, 185, 867, 192;
    0, 0, 0, 0, 0, 0, 97, 970, 376;
    0, 0, 0, 0, 0, 0, 0, 943, 115;
    0, 0, 0, 0, 0, 0, 0, 0, 8]

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
    244, 1, 0, 0, 0, 0, 0, 0, 0;
    767, 273, 1, 0, 0, 0, 0, 0, 0;
    60, 438, 69, 1, 0, 0, 0, 0, 0;
    990, 462, 546, 407, 1, 0, 0, 0, 0;
    367, 481, 80, 484, 989, 1, 0, 0, 0;
    16, 258, 862, 38, 858, 197, 1, 0, 0;
    990, 99, 668, 936, 942, 516, 298, 1, 0;
    248, 108, 49, 166, 869, 625, 179, 134, 1]

private def firstUpper71 : Matrix (Fin 9) (Fin 9) F :=
  !![567, 803, 991, 887, 827, 745, 766, 310, 360;
    0, 596, 184, 308, 862, 287, 206, 596, 469;
    0, 0, 803, 7, 143, 262, 290, 604, 648;
    0, 0, 0, 179, 351, 263, 533, 323, 692;
    0, 0, 0, 0, 890, 949, 478, 850, 351;
    0, 0, 0, 0, 0, 565, 243, 994, 583;
    0, 0, 0, 0, 0, 0, 393, 705, 993;
    0, 0, 0, 0, 0, 0, 0, 266, 797;
    0, 0, 0, 0, 0, 0, 0, 0, 75]

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
    248, 1, 0, 0, 0, 0, 0, 0, 0;
    3, 881, 1, 0, 0, 0, 0, 0, 0;
    169, 532, 928, 1, 0, 0, 0, 0, 0;
    728, 852, 872, 79, 1, 0, 0, 0, 0;
    616, 274, 947, 665, 861, 1, 0, 0, 0;
    115, 289, 105, 939, 665, 983, 1, 0, 0;
    780, 809, 834, 237, 465, 980, 434, 1, 0;
    762, 814, 312, 152, 217, 532, 913, 753, 1]

private def secondUpper71 : Matrix (Fin 9) (Fin 9) F :=
  !![521, 211, 474, 444, 544, 464, 898, 323, 415;
    0, 922, 329, 679, 135, 401, 730, 168, 524;
    0, 0, 226, 422, 533, 727, 244, 864, 438;
    0, 0, 0, 612, 994, 282, 622, 463, 370;
    0, 0, 0, 0, 16, 437, 405, 189, 715;
    0, 0, 0, 0, 0, 218, 237, 693, 743;
    0, 0, 0, 0, 0, 0, 455, 622, 187;
    0, 0, 0, 0, 0, 0, 0, 499, 605;
    0, 0, 0, 0, 0, 0, 0, 0, 966]

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch64
