/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch56
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch56
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch56

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower56 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    688, 1, 0, 0, 0, 0, 0, 0, 0;
    572, 970, 1, 0, 0, 0, 0, 0, 0;
    813, 683, 672, 1, 0, 0, 0, 0, 0;
    539, 888, 680, 42, 1, 0, 0, 0, 0;
    656, 269, 488, 175, 570, 1, 0, 0, 0;
    26, 653, 835, 564, 749, 87, 1, 0, 0;
    644, 245, 771, 837, 318, 498, 318, 1, 0;
    421, 945, 957, 735, 985, 38, 423, 727, 1]

private def firstUpper56 : Matrix (Fin 9) (Fin 9) F :=
  !![350, 395, 360, 473, 774, 655, 168, 884, 253;
    0, 196, 1002, 427, 144, 913, 510, 303, 312;
    0, 0, 213, 961, 323, 895, 754, 971, 340;
    0, 0, 0, 42, 658, 350, 758, 848, 285;
    0, 0, 0, 0, 469, 513, 341, 656, 878;
    0, 0, 0, 0, 0, 46, 820, 613, 62;
    0, 0, 0, 0, 0, 0, 813, 837, 556;
    0, 0, 0, 0, 0, 0, 0, 664, 906;
    0, 0, 0, 0, 0, 0, 0, 0, 794]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt56 : residualMinor (56 : F) 0 = firstValue 56 := by
  apply value_of_factors firstLower56 firstUpper56
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower56 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    946, 1, 0, 0, 0, 0, 0, 0, 0;
    614, 77, 1, 0, 0, 0, 0, 0, 0;
    121, 265, 272, 1, 0, 0, 0, 0, 0;
    337, 942, 767, 586, 1, 0, 0, 0, 0;
    342, 208, 154, 10, 772, 1, 0, 0, 0;
    902, 398, 347, 106, 2, 870, 1, 0, 0;
    506, 140, 118, 119, 903, 447, 513, 1, 0;
    703, 431, 821, 919, 60, 686, 575, 65, 1]

private def secondUpper56 : Matrix (Fin 9) (Fin 9) F :=
  !![660, 352, 573, 973, 599, 602, 906, 267, 89;
    0, 513, 243, 703, 308, 114, 633, 745, 381;
    0, 0, 340, 857, 528, 893, 651, 60, 473;
    0, 0, 0, 899, 844, 345, 120, 60, 533;
    0, 0, 0, 0, 590, 983, 504, 67, 74;
    0, 0, 0, 0, 0, 302, 33, 312, 801;
    0, 0, 0, 0, 0, 0, 152, 442, 460;
    0, 0, 0, 0, 0, 0, 0, 689, 273;
    0, 0, 0, 0, 0, 0, 0, 0, 179]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt56 : residualMinor (56 : F) 1 = secondValue 56 := by
  apply value_of_factors secondLower56 secondUpper56
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower57 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    782, 1, 0, 0, 0, 0, 0, 0, 0;
    850, 317, 1, 0, 0, 0, 0, 0, 0;
    602, 893, 193, 1, 0, 0, 0, 0, 0;
    553, 108, 131, 142, 1, 0, 0, 0, 0;
    10, 820, 597, 402, 891, 1, 0, 0, 0;
    537, 52, 489, 688, 64, 247, 1, 0, 0;
    622, 739, 313, 270, 327, 959, 947, 1, 0;
    529, 78, 709, 409, 107, 571, 365, 483, 1]

private def firstUpper57 : Matrix (Fin 9) (Fin 9) F :=
  !![146, 174, 256, 29, 621, 719, 978, 427, 954;
    0, 653, 311, 159, 787, 791, 272, 423, 382;
    0, 0, 622, 302, 39, 701, 434, 900, 437;
    0, 0, 0, 35, 587, 17, 223, 714, 425;
    0, 0, 0, 0, 823, 23, 87, 165, 1007;
    0, 0, 0, 0, 0, 570, 306, 275, 116;
    0, 0, 0, 0, 0, 0, 488, 173, 673;
    0, 0, 0, 0, 0, 0, 0, 506, 871;
    0, 0, 0, 0, 0, 0, 0, 0, 697]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt57 : residualMinor (57 : F) 0 = firstValue 57 := by
  apply value_of_factors firstLower57 firstUpper57
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower57 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    230, 1, 0, 0, 0, 0, 0, 0, 0;
    379, 592, 1, 0, 0, 0, 0, 0, 0;
    835, 275, 285, 1, 0, 0, 0, 0, 0;
    980, 26, 800, 743, 1, 0, 0, 0, 0;
    580, 617, 103, 901, 667, 1, 0, 0, 0;
    204, 937, 895, 742, 744, 0, 1, 0, 0;
    550, 302, 477, 409, 942, 263, 319, 1, 0;
    135, 345, 731, 414, 126, 438, 602, 846, 1]

private def secondUpper57 : Matrix (Fin 9) (Fin 9) F :=
  !![797, 274, 33, 359, 596, 491, 1007, 360, 206;
    0, 44, 194, 807, 215, 105, 706, 296, 802;
    0, 0, 771, 356, 424, 877, 300, 613, 189;
    0, 0, 0, 234, 495, 486, 978, 252, 843;
    0, 0, 0, 0, 997, 344, 665, 933, 940;
    0, 0, 0, 0, 0, 19, 401, 652, 862;
    0, 0, 0, 0, 0, 0, 954, 357, 823;
    0, 0, 0, 0, 0, 0, 0, 372, 425;
    0, 0, 0, 0, 0, 0, 0, 0, 16]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt57 : residualMinor (57 : F) 1 = secondValue 57 := by
  apply value_of_factors secondLower57 secondUpper57
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower58 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    770, 1, 0, 0, 0, 0, 0, 0, 0;
    616, 273, 1, 0, 0, 0, 0, 0, 0;
    920, 153, 936, 1, 0, 0, 0, 0, 0;
    749, 310, 406, 49, 1, 0, 0, 0, 0;
    144, 331, 345, 922, 76, 1, 0, 0, 0;
    206, 188, 722, 178, 896, 626, 1, 0, 0;
    91, 369, 314, 968, 45, 525, 564, 1, 0;
    1008, 795, 886, 127, 565, 407, 51, 226, 1]

private def firstUpper58 : Matrix (Fin 9) (Fin 9) F :=
  !![684, 646, 710, 49, 919, 593, 559, 934, 255;
    0, 809, 288, 444, 683, 20, 766, 213, 73;
    0, 0, 833, 756, 900, 296, 313, 679, 654;
    0, 0, 0, 429, 795, 756, 884, 824, 935;
    0, 0, 0, 0, 229, 596, 51, 915, 646;
    0, 0, 0, 0, 0, 478, 604, 644, 774;
    0, 0, 0, 0, 0, 0, 863, 170, 242;
    0, 0, 0, 0, 0, 0, 0, 614, 104;
    0, 0, 0, 0, 0, 0, 0, 0, 631]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt58 : residualMinor (58 : F) 0 = firstValue 58 := by
  apply value_of_factors firstLower58 firstUpper58
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower58 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    13, 1, 0, 0, 0, 0, 0, 0, 0;
    409, 752, 1, 0, 0, 0, 0, 0, 0;
    382, 179, 848, 1, 0, 0, 0, 0, 0;
    501, 350, 61, 396, 1, 0, 0, 0, 0;
    579, 368, 161, 214, 226, 1, 0, 0, 0;
    769, 611, 25, 180, 596, 229, 1, 0, 0;
    47, 109, 149, 610, 529, 719, 381, 1, 0;
    745, 518, 382, 414, 904, 648, 782, 826, 1]

private def secondUpper58 : Matrix (Fin 9) (Fin 9) F :=
  !![768, 127, 612, 524, 1003, 544, 64, 874, 434;
    0, 150, 226, 83, 73, 553, 530, 722, 80;
    0, 0, 702, 536, 775, 77, 896, 138, 537;
    0, 0, 0, 154, 164, 291, 799, 656, 375;
    0, 0, 0, 0, 451, 957, 857, 695, 37;
    0, 0, 0, 0, 0, 371, 900, 168, 34;
    0, 0, 0, 0, 0, 0, 717, 433, 698;
    0, 0, 0, 0, 0, 0, 0, 212, 77;
    0, 0, 0, 0, 0, 0, 0, 0, 653]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt58 : residualMinor (58 : F) 1 = secondValue 58 := by
  apply value_of_factors secondLower58 secondUpper58
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower59 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    915, 1, 0, 0, 0, 0, 0, 0, 0;
    355, 419, 1, 0, 0, 0, 0, 0, 0;
    68, 205, 671, 1, 0, 0, 0, 0, 0;
    255, 882, 458, 263, 1, 0, 0, 0, 0;
    797, 325, 806, 311, 101, 1, 0, 0, 0;
    799, 211, 494, 401, 499, 41, 1, 0, 0;
    253, 393, 635, 280, 169, 87, 195, 1, 0;
    952, 77, 73, 879, 668, 365, 385, 16, 1]

private def firstUpper59 : Matrix (Fin 9) (Fin 9) F :=
  !![103, 123, 987, 927, 839, 197, 74, 308, 611;
    0, 840, 792, 23, 14, 803, 649, 969, 829;
    0, 0, 298, 402, 680, 519, 65, 261, 345;
    0, 0, 0, 774, 97, 800, 347, 536, 152;
    0, 0, 0, 0, 349, 658, 914, 437, 407;
    0, 0, 0, 0, 0, 244, 748, 195, 521;
    0, 0, 0, 0, 0, 0, 263, 161, 694;
    0, 0, 0, 0, 0, 0, 0, 584, 796;
    0, 0, 0, 0, 0, 0, 0, 0, 300]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt59 : residualMinor (59 : F) 0 = firstValue 59 := by
  apply value_of_factors firstLower59 firstUpper59
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower59 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    113, 1, 0, 0, 0, 0, 0, 0, 0;
    241, 861, 1, 0, 0, 0, 0, 0, 0;
    570, 245, 712, 1, 0, 0, 0, 0, 0;
    541, 581, 848, 684, 1, 0, 0, 0, 0;
    242, 1003, 864, 977, 552, 1, 0, 0, 0;
    275, 820, 395, 411, 331, 919, 1, 0, 0;
    694, 55, 87, 569, 627, 781, 429, 1, 0;
    423, 884, 534, 507, 214, 652, 121, 449, 1]

private def secondUpper59 : Matrix (Fin 9) (Fin 9) F :=
  !![257, 760, 779, 215, 439, 279, 248, 22, 347;
    0, 262, 598, 589, 693, 199, 984, 810, 39;
    0, 0, 94, 142, 474, 839, 710, 574, 408;
    0, 0, 0, 578, 956, 391, 379, 585, 794;
    0, 0, 0, 0, 712, 109, 668, 303, 36;
    0, 0, 0, 0, 0, 134, 585, 862, 472;
    0, 0, 0, 0, 0, 0, 162, 763, 533;
    0, 0, 0, 0, 0, 0, 0, 772, 340;
    0, 0, 0, 0, 0, 0, 0, 0, 387]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt59 : residualMinor (59 : F) 1 = secondValue 59 := by
  apply value_of_factors secondLower59 secondUpper59
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower60 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    406, 1, 0, 0, 0, 0, 0, 0, 0;
    684, 469, 1, 0, 0, 0, 0, 0, 0;
    80, 906, 789, 1, 0, 0, 0, 0, 0;
    158, 294, 446, 471, 1, 0, 0, 0, 0;
    57, 41, 92, 461, 698, 1, 0, 0, 0;
    708, 141, 277, 326, 74, 46, 1, 0, 0;
    452, 875, 632, 763, 975, 833, 762, 1, 0;
    657, 347, 1005, 139, 58, 452, 664, 278, 1]

private def firstUpper60 : Matrix (Fin 9) (Fin 9) F :=
  !![677, 241, 949, 366, 73, 649, 934, 320, 164;
    0, 393, 248, 29, 49, 394, 448, 994, 523;
    0, 0, 631, 118, 344, 760, 166, 361, 132;
    0, 0, 0, 565, 41, 405, 527, 422, 84;
    0, 0, 0, 0, 20, 687, 735, 678, 384;
    0, 0, 0, 0, 0, 436, 743, 741, 611;
    0, 0, 0, 0, 0, 0, 484, 751, 141;
    0, 0, 0, 0, 0, 0, 0, 530, 694;
    0, 0, 0, 0, 0, 0, 0, 0, 94]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt60 : residualMinor (60 : F) 0 = firstValue 60 := by
  apply value_of_factors firstLower60 firstUpper60
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower60 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    435, 1, 0, 0, 0, 0, 0, 0, 0;
    53, 925, 1, 0, 0, 0, 0, 0, 0;
    846, 624, 707, 1, 0, 0, 0, 0, 0;
    834, 729, 100, 211, 1, 0, 0, 0, 0;
    465, 241, 906, 352, 34, 1, 0, 0, 0;
    648, 662, 961, 372, 50, 270, 1, 0, 0;
    758, 419, 769, 211, 431, 55, 137, 1, 0;
    263, 995, 780, 106, 822, 811, 567, 221, 1]

private def secondUpper60 : Matrix (Fin 9) (Fin 9) F :=
  !![499, 257, 982, 459, 899, 918, 522, 72, 415;
    0, 570, 750, 419, 853, 773, 223, 712, 599;
    0, 0, 83, 484, 398, 989, 712, 813, 478;
    0, 0, 0, 787, 657, 195, 173, 254, 590;
    0, 0, 0, 0, 725, 32, 581, 351, 462;
    0, 0, 0, 0, 0, 856, 1005, 261, 254;
    0, 0, 0, 0, 0, 0, 906, 565, 534;
    0, 0, 0, 0, 0, 0, 0, 798, 988;
    0, 0, 0, 0, 0, 0, 0, 0, 207]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt60 : residualMinor (60 : F) 1 = secondValue 60 := by
  apply value_of_factors secondLower60 secondUpper60
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower61 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    728, 1, 0, 0, 0, 0, 0, 0, 0;
    77, 302, 1, 0, 0, 0, 0, 0, 0;
    215, 464, 454, 1, 0, 0, 0, 0, 0;
    4, 655, 156, 776, 1, 0, 0, 0, 0;
    603, 65, 913, 683, 657, 1, 0, 0, 0;
    451, 190, 895, 154, 371, 401, 1, 0, 0;
    983, 624, 148, 294, 743, 175, 744, 1, 0;
    962, 552, 952, 55, 447, 546, 915, 346, 1]

private def firstUpper61 : Matrix (Fin 9) (Fin 9) F :=
  !![253, 387, 522, 847, 771, 706, 530, 393, 902;
    0, 768, 905, 581, 759, 364, 806, 373, 61;
    0, 0, 950, 738, 828, 251, 336, 72, 526;
    0, 0, 0, 716, 636, 586, 367, 371, 577;
    0, 0, 0, 0, 942, 750, 192, 405, 561;
    0, 0, 0, 0, 0, 883, 292, 975, 890;
    0, 0, 0, 0, 0, 0, 925, 693, 90;
    0, 0, 0, 0, 0, 0, 0, 852, 990;
    0, 0, 0, 0, 0, 0, 0, 0, 698]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt61 : residualMinor (61 : F) 0 = firstValue 61 := by
  apply value_of_factors firstLower61 firstUpper61
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower61 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    651, 1, 0, 0, 0, 0, 0, 0, 0;
    146, 980, 1, 0, 0, 0, 0, 0, 0;
    515, 812, 840, 1, 0, 0, 0, 0, 0;
    962, 55, 715, 809, 1, 0, 0, 0, 0;
    702, 173, 334, 660, 23, 1, 0, 0, 0;
    890, 356, 466, 356, 332, 669, 1, 0, 0;
    534, 483, 306, 789, 115, 388, 642, 1, 0;
    516, 337, 482, 37, 610, 1006, 413, 798, 1]

private def secondUpper61 : Matrix (Fin 9) (Fin 9) F :=
  !![356, 498, 967, 913, 87, 511, 261, 928, 888;
    0, 684, 627, 636, 910, 51, 809, 184, 936;
    0, 0, 754, 440, 401, 604, 510, 719, 24;
    0, 0, 0, 306, 949, 655, 288, 735, 24;
    0, 0, 0, 0, 251, 170, 465, 950, 914;
    0, 0, 0, 0, 0, 872, 329, 231, 917;
    0, 0, 0, 0, 0, 0, 340, 875, 563;
    0, 0, 0, 0, 0, 0, 0, 539, 494;
    0, 0, 0, 0, 0, 0, 0, 0, 964]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt61 : residualMinor (61 : F) 1 = secondValue 61 := by
  apply value_of_factors secondLower61 secondUpper61
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower62 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    491, 1, 0, 0, 0, 0, 0, 0, 0;
    623, 873, 1, 0, 0, 0, 0, 0, 0;
    990, 267, 666, 1, 0, 0, 0, 0, 0;
    477, 526, 171, 59, 1, 0, 0, 0, 0;
    988, 867, 74, 94, 885, 1, 0, 0, 0;
    400, 666, 53, 896, 559, 926, 1, 0, 0;
    969, 695, 580, 389, 260, 240, 62, 1, 0;
    911, 612, 544, 671, 564, 820, 545, 562, 1]

private def firstUpper62 : Matrix (Fin 9) (Fin 9) F :=
  !![630, 83, 137, 549, 509, 405, 769, 165, 713;
    0, 336, 791, 661, 381, 565, 662, 381, 644;
    0, 0, 425, 646, 734, 188, 616, 923, 133;
    0, 0, 0, 534, 397, 944, 273, 188, 44;
    0, 0, 0, 0, 780, 440, 575, 623, 587;
    0, 0, 0, 0, 0, 708, 242, 574, 318;
    0, 0, 0, 0, 0, 0, 181, 243, 52;
    0, 0, 0, 0, 0, 0, 0, 443, 650;
    0, 0, 0, 0, 0, 0, 0, 0, 6]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt62 : residualMinor (62 : F) 0 = firstValue 62 := by
  apply value_of_factors firstLower62 firstUpper62
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower62 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    868, 1, 0, 0, 0, 0, 0, 0, 0;
    922, 912, 1, 0, 0, 0, 0, 0, 0;
    310, 59, 249, 1, 0, 0, 0, 0, 0;
    223, 541, 774, 52, 1, 0, 0, 0, 0;
    398, 814, 856, 452, 32, 1, 0, 0, 0;
    1005, 280, 806, 410, 868, 85, 1, 0, 0;
    209, 30, 424, 780, 897, 680, 756, 1, 0;
    125, 434, 260, 689, 82, 911, 39, 486, 1]

private def secondUpper62 : Matrix (Fin 9) (Fin 9) F :=
  !![625, 552, 701, 331, 951, 925, 747, 426, 569;
    0, 868, 414, 65, 971, 911, 257, 202, 113;
    0, 0, 643, 314, 1007, 436, 314, 595, 495;
    0, 0, 0, 523, 653, 860, 548, 612, 242;
    0, 0, 0, 0, 708, 840, 580, 239, 966;
    0, 0, 0, 0, 0, 839, 769, 655, 978;
    0, 0, 0, 0, 0, 0, 846, 379, 652;
    0, 0, 0, 0, 0, 0, 0, 131, 781;
    0, 0, 0, 0, 0, 0, 0, 0, 219]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt62 : residualMinor (62 : F) 1 = secondValue 62 := by
  apply value_of_factors secondLower62 secondUpper62
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower63 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    786, 1, 0, 0, 0, 0, 0, 0, 0;
    705, 271, 1, 0, 0, 0, 0, 0, 0;
    969, 908, 717, 1, 0, 0, 0, 0, 0;
    621, 326, 375, 381, 1, 0, 0, 0, 0;
    913, 596, 990, 361, 704, 1, 0, 0, 0;
    488, 81, 140, 498, 445, 965, 1, 0, 0;
    88, 950, 862, 696, 712, 750, 890, 1, 0;
    451, 732, 424, 519, 829, 635, 956, 907, 1]

private def firstUpper63 : Matrix (Fin 9) (Fin 9) F :=
  !![795, 395, 450, 902, 495, 673, 446, 269, 789;
    0, 322, 923, 963, 183, 846, 1007, 502, 685;
    0, 0, 109, 282, 295, 813, 311, 433, 47;
    0, 0, 0, 649, 889, 947, 752, 257, 589;
    0, 0, 0, 0, 579, 457, 222, 966, 209;
    0, 0, 0, 0, 0, 43, 267, 810, 660;
    0, 0, 0, 0, 0, 0, 684, 749, 329;
    0, 0, 0, 0, 0, 0, 0, 241, 411;
    0, 0, 0, 0, 0, 0, 0, 0, 236]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt63 : residualMinor (63 : F) 0 = firstValue 63 := by
  apply value_of_factors firstLower63 firstUpper63
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower63 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    146, 1, 0, 0, 0, 0, 0, 0, 0;
    884, 389, 1, 0, 0, 0, 0, 0, 0;
    621, 185, 900, 1, 0, 0, 0, 0, 0;
    431, 615, 428, 919, 1, 0, 0, 0, 0;
    615, 332, 439, 71, 282, 1, 0, 0, 0;
    809, 205, 572, 138, 717, 166, 1, 0, 0;
    213, 195, 122, 673, 690, 235, 577, 1, 0;
    853, 381, 687, 609, 861, 882, 834, 730, 1]

private def secondUpper63 : Matrix (Fin 9) (Fin 9) F :=
  !![146, 251, 838, 708, 901, 684, 371, 985, 182;
    0, 707, 205, 158, 412, 126, 751, 523, 975;
    0, 0, 214, 968, 88, 424, 832, 611, 973;
    0, 0, 0, 742, 4, 23, 111, 925, 471;
    0, 0, 0, 0, 727, 972, 375, 491, 265;
    0, 0, 0, 0, 0, 985, 900, 923, 593;
    0, 0, 0, 0, 0, 0, 372, 121, 644;
    0, 0, 0, 0, 0, 0, 0, 152, 618;
    0, 0, 0, 0, 0, 0, 0, 0, 106]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt63 : residualMinor (63 : F) 1 = secondValue 63 := by
  apply value_of_factors secondLower63 secondUpper63
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 56 through 63. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((56 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt56, secondAt56⟩
  · exact ⟨firstAt57, secondAt57⟩
  · exact ⟨firstAt58, secondAt58⟩
  · exact ⟨firstAt59, secondAt59⟩
  · exact ⟨firstAt60, secondAt60⟩
  · exact ⟨firstAt61, secondAt61⟩
  · exact ⟨firstAt62, secondAt62⟩
  · exact ⟨firstAt63, secondAt63⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch56
