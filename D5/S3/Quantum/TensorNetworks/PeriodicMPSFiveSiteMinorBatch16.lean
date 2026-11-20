/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch16
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch16
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch16

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower16 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    740, 1, 0, 0, 0, 0, 0, 0, 0;
    34, 950, 1, 0, 0, 0, 0, 0, 0;
    619, 357, 741, 1, 0, 0, 0, 0, 0;
    92, 470, 501, 544, 1, 0, 0, 0, 0;
    722, 6, 892, 482, 37, 1, 0, 0, 0;
    757, 824, 875, 679, 914, 159, 1, 0, 0;
    287, 506, 643, 688, 553, 426, 129, 1, 0;
    713, 209, 297, 264, 102, 613, 745, 141, 1]

private def firstUpper16 : Matrix (Fin 9) (Fin 9) F :=
  !![399, 61, 350, 432, 587, 342, 898, 831, 848;
    0, 574, 403, 810, 281, 611, 340, 326, 796;
    0, 0, 176, 755, 116, 393, 237, 291, 349;
    0, 0, 0, 87, 694, 381, 229, 973, 617;
    0, 0, 0, 0, 573, 458, 596, 384, 677;
    0, 0, 0, 0, 0, 222, 363, 518, 78;
    0, 0, 0, 0, 0, 0, 566, 969, 778;
    0, 0, 0, 0, 0, 0, 0, 41, 4;
    0, 0, 0, 0, 0, 0, 0, 0, 996]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt16 : residualMinor (16 : F) 0 = firstValue 16 := by
  apply value_of_factors firstLower16 firstUpper16
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower16 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    990, 1, 0, 0, 0, 0, 0, 0, 0;
    420, 600, 1, 0, 0, 0, 0, 0, 0;
    1000, 607, 156, 1, 0, 0, 0, 0, 0;
    375, 662, 447, 996, 1, 0, 0, 0, 0;
    257, 837, 903, 827, 571, 1, 0, 0, 0;
    482, 97, 670, 149, 860, 974, 1, 0, 0;
    309, 507, 211, 512, 648, 828, 834, 1, 0;
    839, 998, 627, 524, 55, 176, 833, 593, 1]

private def secondUpper16 : Matrix (Fin 9) (Fin 9) F :=
  !![975, 614, 944, 694, 791, 887, 383, 265, 60;
    0, 876, 873, 706, 685, 132, 143, 775, 849;
    0, 0, 335, 242, 881, 480, 155, 69, 549;
    0, 0, 0, 222, 172, 277, 912, 286, 696;
    0, 0, 0, 0, 268, 462, 913, 242, 148;
    0, 0, 0, 0, 0, 323, 665, 730, 615;
    0, 0, 0, 0, 0, 0, 248, 158, 22;
    0, 0, 0, 0, 0, 0, 0, 649, 80;
    0, 0, 0, 0, 0, 0, 0, 0, 329]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt16 : residualMinor (16 : F) 1 = secondValue 16 := by
  apply value_of_factors secondLower16 secondUpper16
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower17 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    570, 1, 0, 0, 0, 0, 0, 0, 0;
    188, 336, 1, 0, 0, 0, 0, 0, 0;
    648, 751, 461, 1, 0, 0, 0, 0, 0;
    188, 77, 427, 552, 1, 0, 0, 0, 0;
    3, 988, 1003, 577, 468, 1, 0, 0, 0;
    991, 535, 463, 856, 549, 178, 1, 0, 0;
    116, 658, 139, 555, 122, 736, 90, 1, 0;
    912, 827, 491, 116, 317, 630, 718, 89, 1]

private def firstUpper17 : Matrix (Fin 9) (Fin 9) F :=
  !![28, 107, 272, 578, 109, 571, 649, 320, 455;
    0, 371, 248, 106, 497, 1005, 398, 655, 895;
    0, 0, 124, 350, 500, 31, 647, 586, 398;
    0, 0, 0, 247, 79, 957, 6, 317, 91;
    0, 0, 0, 0, 938, 431, 776, 307, 368;
    0, 0, 0, 0, 0, 270, 667, 845, 529;
    0, 0, 0, 0, 0, 0, 39, 790, 988;
    0, 0, 0, 0, 0, 0, 0, 237, 438;
    0, 0, 0, 0, 0, 0, 0, 0, 363]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt17 : residualMinor (17 : F) 0 = firstValue 17 := by
  apply value_of_factors firstLower17 firstUpper17
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower17 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    298, 1, 0, 0, 0, 0, 0, 0, 0;
    666, 300, 1, 0, 0, 0, 0, 0, 0;
    394, 543, 511, 1, 0, 0, 0, 0, 0;
    311, 500, 72, 569, 1, 0, 0, 0, 0;
    241, 456, 1006, 283, 823, 1, 0, 0, 0;
    331, 61, 634, 487, 394, 754, 1, 0, 0;
    515, 929, 481, 809, 51, 672, 773, 1, 0;
    305, 410, 325, 915, 230, 441, 787, 533, 1]

private def secondUpper17 : Matrix (Fin 9) (Fin 9) F :=
  !![356, 859, 118, 769, 814, 305, 833, 624, 917;
    0, 116, 53, 513, 666, 488, 5, 130, 96;
    0, 0, 749, 229, 1, 683, 791, 799, 395;
    0, 0, 0, 930, 674, 226, 85, 815, 513;
    0, 0, 0, 0, 907, 168, 550, 968, 970;
    0, 0, 0, 0, 0, 259, 501, 787, 302;
    0, 0, 0, 0, 0, 0, 603, 245, 938;
    0, 0, 0, 0, 0, 0, 0, 928, 970;
    0, 0, 0, 0, 0, 0, 0, 0, 162]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt17 : residualMinor (17 : F) 1 = secondValue 17 := by
  apply value_of_factors secondLower17 secondUpper17
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower18 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    182, 1, 0, 0, 0, 0, 0, 0, 0;
    787, 138, 1, 0, 0, 0, 0, 0, 0;
    7, 812, 528, 1, 0, 0, 0, 0, 0;
    556, 108, 968, 540, 1, 0, 0, 0, 0;
    413, 271, 215, 238, 930, 1, 0, 0, 0;
    692, 232, 897, 323, 347, 252, 1, 0, 0;
    235, 378, 58, 387, 386, 474, 317, 1, 0;
    659, 613, 187, 99, 195, 596, 408, 209, 1]

private def firstUpper18 : Matrix (Fin 9) (Fin 9) F :=
  !![293, 695, 881, 228, 253, 849, 332, 813, 524;
    0, 670, 753, 377, 296, 885, 155, 954, 242;
    0, 0, 332, 452, 820, 197, 503, 671, 931;
    0, 0, 0, 890, 280, 587, 668, 1, 772;
    0, 0, 0, 0, 737, 261, 889, 537, 397;
    0, 0, 0, 0, 0, 400, 474, 379, 730;
    0, 0, 0, 0, 0, 0, 450, 542, 593;
    0, 0, 0, 0, 0, 0, 0, 190, 677;
    0, 0, 0, 0, 0, 0, 0, 0, 712]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt18 : residualMinor (18 : F) 0 = firstValue 18 := by
  apply value_of_factors firstLower18 firstUpper18
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower18 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    15, 1, 0, 0, 0, 0, 0, 0, 0;
    773, 485, 1, 0, 0, 0, 0, 0, 0;
    416, 19, 953, 1, 0, 0, 0, 0, 0;
    894, 797, 433, 528, 1, 0, 0, 0, 0;
    454, 664, 265, 540, 768, 1, 0, 0, 0;
    781, 71, 851, 709, 127, 567, 1, 0, 0;
    615, 373, 19, 290, 376, 294, 39, 1, 0;
    171, 674, 624, 434, 407, 443, 781, 860, 1]

private def secondUpper18 : Matrix (Fin 9) (Fin 9) F :=
  !![196, 4, 993, 371, 349, 335, 471, 574, 967;
    0, 975, 904, 993, 747, 37, 37, 59, 385;
    0, 0, 209, 314, 199, 9, 31, 164, 855;
    0, 0, 0, 155, 432, 460, 760, 852, 862;
    0, 0, 0, 0, 632, 350, 941, 511, 493;
    0, 0, 0, 0, 0, 576, 743, 457, 5;
    0, 0, 0, 0, 0, 0, 588, 69, 987;
    0, 0, 0, 0, 0, 0, 0, 769, 207;
    0, 0, 0, 0, 0, 0, 0, 0, 147]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt18 : residualMinor (18 : F) 1 = secondValue 18 := by
  apply value_of_factors secondLower18 secondUpper18
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower19 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    846, 1, 0, 0, 0, 0, 0, 0, 0;
    559, 590, 1, 0, 0, 0, 0, 0, 0;
    411, 908, 615, 1, 0, 0, 0, 0, 0;
    314, 60, 362, 417, 1, 0, 0, 0, 0;
    761, 160, 197, 575, 217, 1, 0, 0, 0;
    339, 747, 313, 625, 77, 190, 1, 0, 0;
    401, 5, 910, 248, 763, 969, 646, 1, 0;
    759, 402, 855, 422, 101, 762, 971, 398, 1]

private def firstUpper19 : Matrix (Fin 9) (Fin 9) F :=
  !![655, 765, 22, 443, 0, 714, 229, 205, 249;
    0, 421, 141, 48, 769, 487, 52, 462, 641;
    0, 0, 366, 792, 500, 780, 447, 365, 248;
    0, 0, 0, 226, 933, 105, 2, 485, 22;
    0, 0, 0, 0, 503, 759, 95, 247, 23;
    0, 0, 0, 0, 0, 988, 202, 171, 944;
    0, 0, 0, 0, 0, 0, 22, 991, 362;
    0, 0, 0, 0, 0, 0, 0, 942, 603;
    0, 0, 0, 0, 0, 0, 0, 0, 325]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt19 : residualMinor (19 : F) 0 = firstValue 19 := by
  apply value_of_factors firstLower19 firstUpper19
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower19 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    203, 1, 0, 0, 0, 0, 0, 0, 0;
    47, 497, 1, 0, 0, 0, 0, 0, 0;
    826, 144, 138, 1, 0, 0, 0, 0, 0;
    218, 297, 540, 491, 1, 0, 0, 0, 0;
    143, 589, 721, 333, 312, 1, 0, 0, 0;
    105, 889, 561, 830, 97, 585, 1, 0, 0;
    959, 472, 319, 1006, 157, 1002, 675, 1, 0;
    464, 713, 315, 89, 715, 149, 729, 107, 1]

private def secondUpper19 : Matrix (Fin 9) (Fin 9) F :=
  !![458, 437, 146, 955, 883, 267, 681, 886, 725;
    0, 923, 214, 350, 113, 425, 48, 88, 553;
    0, 0, 796, 401, 371, 331, 357, 471, 859;
    0, 0, 0, 15, 994, 115, 367, 934, 534;
    0, 0, 0, 0, 919, 253, 742, 3, 708;
    0, 0, 0, 0, 0, 435, 817, 142, 752;
    0, 0, 0, 0, 0, 0, 92, 59, 43;
    0, 0, 0, 0, 0, 0, 0, 224, 79;
    0, 0, 0, 0, 0, 0, 0, 0, 153]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt19 : residualMinor (19 : F) 1 = secondValue 19 := by
  apply value_of_factors secondLower19 secondUpper19
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower20 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    809, 1, 0, 0, 0, 0, 0, 0, 0;
    656, 681, 1, 0, 0, 0, 0, 0, 0;
    319, 134, 170, 1, 0, 0, 0, 0, 0;
    379, 203, 20, 233, 1, 0, 0, 0, 0;
    962, 222, 292, 701, 217, 1, 0, 0, 0;
    975, 435, 1005, 737, 49, 560, 1, 0, 0;
    516, 763, 733, 510, 783, 316, 287, 1, 0;
    977, 519, 820, 306, 683, 311, 246, 182, 1]

private def firstUpper20 : Matrix (Fin 9) (Fin 9) F :=
  !![73, 567, 196, 296, 430, 592, 975, 436, 909;
    0, 197, 379, 723, 192, 119, 2, 354, 993;
    0, 0, 401, 467, 529, 777, 28, 871, 408;
    0, 0, 0, 947, 964, 649, 722, 408, 489;
    0, 0, 0, 0, 555, 205, 732, 99, 602;
    0, 0, 0, 0, 0, 167, 709, 34, 88;
    0, 0, 0, 0, 0, 0, 532, 796, 948;
    0, 0, 0, 0, 0, 0, 0, 306, 159;
    0, 0, 0, 0, 0, 0, 0, 0, 747]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt20 : residualMinor (20 : F) 0 = firstValue 20 := by
  apply value_of_factors firstLower20 firstUpper20
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower20 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    862, 1, 0, 0, 0, 0, 0, 0, 0;
    829, 316, 1, 0, 0, 0, 0, 0, 0;
    767, 914, 848, 1, 0, 0, 0, 0, 0;
    50, 290, 744, 811, 1, 0, 0, 0, 0;
    695, 931, 567, 550, 973, 1, 0, 0, 0;
    408, 927, 221, 207, 786, 921, 1, 0, 0;
    526, 868, 616, 323, 137, 834, 596, 1, 0;
    284, 997, 9, 18, 703, 415, 765, 785, 1]

private def secondUpper20 : Matrix (Fin 9) (Fin 9) F :=
  !![735, 784, 74, 252, 995, 535, 703, 1, 722;
    0, 27, 309, 765, 926, 724, 162, 75, 1002;
    0, 0, 52, 252, 172, 678, 957, 950, 589;
    0, 0, 0, 905, 808, 190, 518, 905, 984;
    0, 0, 0, 0, 69, 539, 234, 61, 852;
    0, 0, 0, 0, 0, 744, 375, 558, 691;
    0, 0, 0, 0, 0, 0, 283, 50, 220;
    0, 0, 0, 0, 0, 0, 0, 60, 118;
    0, 0, 0, 0, 0, 0, 0, 0, 458]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt20 : residualMinor (20 : F) 1 = secondValue 20 := by
  apply value_of_factors secondLower20 secondUpper20
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower21 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    625, 1, 0, 0, 0, 0, 0, 0, 0;
    431, 753, 1, 0, 0, 0, 0, 0, 0;
    309, 49, 350, 1, 0, 0, 0, 0, 0;
    420, 727, 567, 48, 1, 0, 0, 0, 0;
    441, 599, 510, 195, 249, 1, 0, 0, 0;
    176, 956, 872, 313, 733, 791, 1, 0, 0;
    245, 168, 287, 177, 46, 846, 741, 1, 0;
    899, 886, 539, 346, 9, 18, 372, 262, 1]

private def firstUpper21 : Matrix (Fin 9) (Fin 9) F :=
  !![508, 219, 165, 814, 308, 342, 185, 870, 652;
    0, 389, 935, 172, 918, 178, 623, 580, 348;
    0, 0, 523, 38, 767, 569, 528, 159, 665;
    0, 0, 0, 209, 512, 414, 407, 447, 683;
    0, 0, 0, 0, 528, 535, 630, 490, 1007;
    0, 0, 0, 0, 0, 329, 578, 672, 524;
    0, 0, 0, 0, 0, 0, 641, 596, 180;
    0, 0, 0, 0, 0, 0, 0, 558, 242;
    0, 0, 0, 0, 0, 0, 0, 0, 234]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt21 : residualMinor (21 : F) 0 = firstValue 21 := by
  apply value_of_factors firstLower21 firstUpper21
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower21 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    760, 1, 0, 0, 0, 0, 0, 0, 0;
    19, 966, 1, 0, 0, 0, 0, 0, 0;
    569, 328, 79, 1, 0, 0, 0, 0, 0;
    526, 264, 521, 839, 1, 0, 0, 0, 0;
    411, 646, 44, 502, 473, 1, 0, 0, 0;
    110, 872, 683, 226, 579, 648, 1, 0, 0;
    138, 615, 330, 889, 797, 868, 132, 1, 0;
    552, 517, 692, 548, 66, 817, 844, 487, 1]

private def secondUpper21 : Matrix (Fin 9) (Fin 9) F :=
  !![28, 1003, 656, 782, 402, 578, 867, 940, 714;
    0, 564, 19, 367, 906, 664, 170, 451, 414;
    0, 0, 233, 18, 457, 911, 404, 148, 70;
    0, 0, 0, 326, 475, 39, 654, 918, 220;
    0, 0, 0, 0, 978, 712, 714, 358, 711;
    0, 0, 0, 0, 0, 659, 584, 269, 2;
    0, 0, 0, 0, 0, 0, 370, 503, 981;
    0, 0, 0, 0, 0, 0, 0, 821, 525;
    0, 0, 0, 0, 0, 0, 0, 0, 378]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt21 : residualMinor (21 : F) 1 = secondValue 21 := by
  apply value_of_factors secondLower21 secondUpper21
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower22 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    466, 1, 0, 0, 0, 0, 0, 0, 0;
    219, 916, 1, 0, 0, 0, 0, 0, 0;
    436, 15, 143, 1, 0, 0, 0, 0, 0;
    440, 58, 868, 690, 1, 0, 0, 0, 0;
    304, 59, 294, 460, 846, 1, 0, 0, 0;
    472, 575, 927, 804, 401, 37, 1, 0, 0;
    598, 357, 786, 3, 390, 143, 383, 1, 0;
    721, 750, 450, 172, 808, 632, 813, 718, 1]

private def firstUpper22 : Matrix (Fin 9) (Fin 9) F :=
  !![81, 76, 785, 314, 629, 105, 595, 521, 851;
    0, 943, 799, 261, 41, 907, 18, 680, 521;
    0, 0, 216, 670, 397, 30, 231, 2, 511;
    0, 0, 0, 159, 265, 258, 581, 215, 561;
    0, 0, 0, 0, 251, 883, 817, 929, 508;
    0, 0, 0, 0, 0, 954, 370, 751, 597;
    0, 0, 0, 0, 0, 0, 106, 722, 40;
    0, 0, 0, 0, 0, 0, 0, 89, 521;
    0, 0, 0, 0, 0, 0, 0, 0, 441]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt22 : residualMinor (22 : F) 0 = firstValue 22 := by
  apply value_of_factors firstLower22 firstUpper22
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower22 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    376, 1, 0, 0, 0, 0, 0, 0, 0;
    414, 147, 1, 0, 0, 0, 0, 0, 0;
    531, 606, 751, 1, 0, 0, 0, 0, 0;
    324, 997, 648, 547, 1, 0, 0, 0, 0;
    721, 734, 578, 705, 793, 1, 0, 0, 0;
    878, 208, 488, 199, 448, 549, 1, 0, 0;
    437, 622, 203, 673, 122, 629, 21, 1, 0;
    651, 124, 270, 420, 448, 177, 296, 144, 1]

private def secondUpper22 : Matrix (Fin 9) (Fin 9) F :=
  !![946, 986, 257, 548, 387, 637, 110, 879, 226;
    0, 611, 574, 68, 329, 17, 831, 745, 330;
    0, 0, 885, 5, 420, 382, 516, 211, 389;
    0, 0, 0, 728, 69, 605, 651, 665, 791;
    0, 0, 0, 0, 144, 387, 603, 542, 498;
    0, 0, 0, 0, 0, 87, 412, 462, 584;
    0, 0, 0, 0, 0, 0, 262, 163, 613;
    0, 0, 0, 0, 0, 0, 0, 345, 899;
    0, 0, 0, 0, 0, 0, 0, 0, 639]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt22 : residualMinor (22 : F) 1 = secondValue 22 := by
  apply value_of_factors secondLower22 secondUpper22
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower23 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    176, 1, 0, 0, 0, 0, 0, 0, 0;
    931, 324, 1, 0, 0, 0, 0, 0, 0;
    2, 70, 601, 1, 0, 0, 0, 0, 0;
    886, 216, 847, 215, 1, 0, 0, 0, 0;
    369, 506, 352, 741, 203, 1, 0, 0, 0;
    224, 667, 314, 86, 797, 116, 1, 0, 0;
    85, 387, 394, 557, 913, 74, 352, 1, 0;
    670, 389, 678, 549, 984, 641, 583, 198, 1]

private def firstUpper23 : Matrix (Fin 9) (Fin 9) F :=
  !![702, 677, 900, 971, 916, 861, 559, 350, 57;
    0, 418, 892, 1007, 265, 856, 346, 932, 206;
    0, 0, 1006, 971, 26, 711, 442, 947, 833;
    0, 0, 0, 335, 614, 445, 508, 760, 322;
    0, 0, 0, 0, 855, 803, 126, 920, 12;
    0, 0, 0, 0, 0, 148, 682, 688, 215;
    0, 0, 0, 0, 0, 0, 290, 843, 999;
    0, 0, 0, 0, 0, 0, 0, 631, 282;
    0, 0, 0, 0, 0, 0, 0, 0, 749]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt23 : residualMinor (23 : F) 0 = firstValue 23 := by
  apply value_of_factors firstLower23 firstUpper23
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower23 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    850, 1, 0, 0, 0, 0, 0, 0, 0;
    581, 891, 1, 0, 0, 0, 0, 0, 0;
    784, 339, 769, 1, 0, 0, 0, 0, 0;
    194, 15, 276, 143, 1, 0, 0, 0, 0;
    838, 515, 435, 331, 508, 1, 0, 0, 0;
    961, 481, 312, 15, 993, 634, 1, 0, 0;
    6, 572, 780, 681, 636, 456, 614, 1, 0;
    654, 974, 926, 129, 86, 656, 616, 980, 1]

private def secondUpper23 : Matrix (Fin 9) (Fin 9) F :=
  !![852, 409, 765, 313, 735, 380, 11, 434, 857;
    0, 963, 425, 699, 871, 922, 588, 368, 196;
    0, 0, 56, 780, 953, 31, 767, 291, 14;
    0, 0, 0, 972, 242, 377, 227, 537, 479;
    0, 0, 0, 0, 329, 73, 504, 38, 634;
    0, 0, 0, 0, 0, 713, 100, 646, 690;
    0, 0, 0, 0, 0, 0, 729, 865, 71;
    0, 0, 0, 0, 0, 0, 0, 63, 275;
    0, 0, 0, 0, 0, 0, 0, 0, 955]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt23 : residualMinor (23 : F) 1 = secondValue 23 := by
  apply value_of_factors secondLower23 secondUpper23
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 16 through 23. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((16 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt16, secondAt16⟩
  · exact ⟨firstAt17, secondAt17⟩
  · exact ⟨firstAt18, secondAt18⟩
  · exact ⟨firstAt19, secondAt19⟩
  · exact ⟨firstAt20, secondAt20⟩
  · exact ⟨firstAt21, secondAt21⟩
  · exact ⟨firstAt22, secondAt22⟩
  · exact ⟨firstAt23, secondAt23⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch16
