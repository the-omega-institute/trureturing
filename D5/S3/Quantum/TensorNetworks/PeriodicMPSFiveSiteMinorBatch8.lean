/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch8
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch8
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch8

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower8 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    1005, 1, 0, 0, 0, 0, 0, 0, 0;
    866, 991, 1, 0, 0, 0, 0, 0, 0;
    785, 713, 57, 1, 0, 0, 0, 0, 0;
    171, 1008, 292, 100, 1, 0, 0, 0, 0;
    285, 1001, 741, 86, 599, 1, 0, 0, 0;
    387, 96, 392, 434, 961, 616, 1, 0, 0;
    890, 286, 378, 89, 731, 85, 618, 1, 0;
    747, 380, 282, 213, 647, 416, 329, 876, 1]

private def firstUpper8 : Matrix (Fin 9) (Fin 9) F :=
  !![59, 824, 215, 209, 92, 541, 58, 17, 273;
    0, 960, 213, 4, 475, 63, 708, 197, 168;
    0, 0, 626, 447, 305, 208, 133, 491, 628;
    0, 0, 0, 730, 551, 190, 1000, 592, 843;
    0, 0, 0, 0, 877, 473, 114, 617, 913;
    0, 0, 0, 0, 0, 700, 23, 927, 966;
    0, 0, 0, 0, 0, 0, 332, 123, 744;
    0, 0, 0, 0, 0, 0, 0, 732, 871;
    0, 0, 0, 0, 0, 0, 0, 0, 708]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt8 : residualMinor (8 : F) 0 = firstValue 8 := by
  apply value_of_factors firstLower8 firstUpper8
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower8 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    553, 1, 0, 0, 0, 0, 0, 0, 0;
    868, 894, 1, 0, 0, 0, 0, 0, 0;
    410, 866, 885, 1, 0, 0, 0, 0, 0;
    63, 749, 699, 831, 1, 0, 0, 0, 0;
    719, 309, 208, 237, 357, 1, 0, 0, 0;
    795, 702, 165, 566, 973, 664, 1, 0, 0;
    609, 527, 797, 151, 433, 320, 145, 1, 0;
    801, 639, 875, 185, 661, 608, 485, 925, 1]

private def secondUpper8 : Matrix (Fin 9) (Fin 9) F :=
  !![835, 171, 823, 767, 848, 320, 561, 24, 956;
    0, 974, 302, 815, 348, 541, 6, 983, 133;
    0, 0, 785, 830, 963, 794, 364, 962, 693;
    0, 0, 0, 248, 95, 580, 560, 550, 981;
    0, 0, 0, 0, 218, 813, 990, 455, 856;
    0, 0, 0, 0, 0, 485, 935, 872, 689;
    0, 0, 0, 0, 0, 0, 531, 97, 58;
    0, 0, 0, 0, 0, 0, 0, 317, 562;
    0, 0, 0, 0, 0, 0, 0, 0, 31]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt8 : residualMinor (8 : F) 1 = secondValue 8 := by
  apply value_of_factors secondLower8 secondUpper8
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower9 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    735, 1, 0, 0, 0, 0, 0, 0, 0;
    767, 760, 1, 0, 0, 0, 0, 0, 0;
    185, 615, 35, 1, 0, 0, 0, 0, 0;
    696, 521, 94, 835, 1, 0, 0, 0, 0;
    460, 610, 389, 29, 974, 1, 0, 0, 0;
    699, 549, 769, 170, 445, 109, 1, 0, 0;
    259, 742, 747, 44, 7, 15, 694, 1, 0;
    40, 616, 159, 251, 403, 366, 272, 832, 1]

private def firstUpper9 : Matrix (Fin 9) (Fin 9) F :=
  !![679, 157, 53, 152, 632, 848, 1007, 132, 285;
    0, 511, 254, 986, 444, 494, 779, 70, 252;
    0, 0, 848, 617, 562, 657, 652, 151, 680;
    0, 0, 0, 527, 8, 790, 806, 751, 506;
    0, 0, 0, 0, 743, 770, 872, 785, 905;
    0, 0, 0, 0, 0, 144, 775, 158, 326;
    0, 0, 0, 0, 0, 0, 41, 489, 247;
    0, 0, 0, 0, 0, 0, 0, 803, 650;
    0, 0, 0, 0, 0, 0, 0, 0, 824]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt9 : residualMinor (9 : F) 0 = firstValue 9 := by
  apply value_of_factors firstLower9 firstUpper9
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower9 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    351, 1, 0, 0, 0, 0, 0, 0, 0;
    256, 139, 1, 0, 0, 0, 0, 0, 0;
    868, 953, 429, 1, 0, 0, 0, 0, 0;
    762, 801, 936, 47, 1, 0, 0, 0, 0;
    546, 197, 263, 241, 558, 1, 0, 0, 0;
    86, 99, 29, 279, 240, 710, 1, 0, 0;
    639, 576, 175, 870, 238, 882, 348, 1, 0;
    702, 710, 247, 174, 696, 393, 188, 240, 1]

private def secondUpper9 : Matrix (Fin 9) (Fin 9) F :=
  !![326, 889, 650, 719, 630, 956, 523, 181, 686;
    0, 622, 751, 588, 665, 653, 383, 262, 220;
    0, 0, 74, 410, 964, 854, 433, 202, 781;
    0, 0, 0, 568, 83, 899, 103, 807, 963;
    0, 0, 0, 0, 110, 309, 992, 884, 635;
    0, 0, 0, 0, 0, 668, 241, 857, 1001;
    0, 0, 0, 0, 0, 0, 912, 519, 465;
    0, 0, 0, 0, 0, 0, 0, 127, 639;
    0, 0, 0, 0, 0, 0, 0, 0, 398]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt9 : residualMinor (9 : F) 1 = secondValue 9 := by
  apply value_of_factors secondLower9 secondUpper9
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower10 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    181, 1, 0, 0, 0, 0, 0, 0, 0;
    378, 350, 1, 0, 0, 0, 0, 0, 0;
    799, 609, 1, 1, 0, 0, 0, 0, 0;
    158, 185, 905, 955, 1, 0, 0, 0, 0;
    316, 783, 528, 525, 275, 1, 0, 0, 0;
    271, 883, 185, 906, 428, 885, 1, 0, 0;
    723, 913, 746, 223, 617, 958, 42, 1, 0;
    471, 868, 630, 3, 278, 339, 797, 237, 1]

private def firstUpper10 : Matrix (Fin 9) (Fin 9) F :=
  !![855, 239, 922, 341, 363, 339, 107, 850, 844;
    0, 952, 850, 135, 425, 190, 426, 904, 306;
    0, 0, 798, 490, 404, 543, 526, 367, 59;
    0, 0, 0, 686, 908, 77, 472, 491, 113;
    0, 0, 0, 0, 608, 976, 851, 481, 775;
    0, 0, 0, 0, 0, 696, 451, 20, 41;
    0, 0, 0, 0, 0, 0, 349, 326, 323;
    0, 0, 0, 0, 0, 0, 0, 287, 561;
    0, 0, 0, 0, 0, 0, 0, 0, 997]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt10 : residualMinor (10 : F) 0 = firstValue 10 := by
  apply value_of_factors firstLower10 firstUpper10
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower10 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    897, 1, 0, 0, 0, 0, 0, 0, 0;
    222, 340, 1, 0, 0, 0, 0, 0, 0;
    471, 252, 84, 1, 0, 0, 0, 0, 0;
    833, 15, 996, 76, 1, 0, 0, 0, 0;
    31, 196, 167, 194, 101, 1, 0, 0, 0;
    290, 683, 458, 149, 924, 710, 1, 0, 0;
    186, 298, 897, 728, 672, 634, 743, 1, 0;
    820, 572, 959, 885, 633, 950, 893, 916, 1]

private def secondUpper10 : Matrix (Fin 9) (Fin 9) F :=
  !![407, 401, 951, 144, 986, 342, 349, 965, 865;
    0, 331, 805, 291, 994, 971, 359, 494, 727;
    0, 0, 552, 325, 937, 2, 624, 600, 98;
    0, 0, 0, 729, 750, 420, 320, 786, 700;
    0, 0, 0, 0, 933, 413, 711, 737, 523;
    0, 0, 0, 0, 0, 976, 892, 554, 770;
    0, 0, 0, 0, 0, 0, 112, 567, 438;
    0, 0, 0, 0, 0, 0, 0, 125, 67;
    0, 0, 0, 0, 0, 0, 0, 0, 819]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt10 : residualMinor (10 : F) 1 = secondValue 10 := by
  apply value_of_factors secondLower10 secondUpper10
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower11 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    143, 1, 0, 0, 0, 0, 0, 0, 0;
    908, 547, 1, 0, 0, 0, 0, 0, 0;
    341, 676, 150, 1, 0, 0, 0, 0, 0;
    666, 236, 764, 158, 1, 0, 0, 0, 0;
    43, 52, 34, 667, 37, 1, 0, 0, 0;
    344, 204, 482, 993, 322, 873, 1, 0, 0;
    757, 742, 340, 513, 809, 810, 807, 1, 0;
    581, 553, 495, 695, 478, 277, 931, 770, 1]

private def firstUpper11 : Matrix (Fin 9) (Fin 9) F :=
  !![930, 866, 821, 303, 865, 952, 229, 848, 874;
    0, 72, 359, 44, 979, 520, 385, 32, 347;
    0, 0, 51, 199, 281, 456, 603, 442, 45;
    0, 0, 0, 15, 524, 553, 666, 881, 401;
    0, 0, 0, 0, 799, 587, 421, 934, 39;
    0, 0, 0, 0, 0, 178, 750, 411, 713;
    0, 0, 0, 0, 0, 0, 272, 261, 249;
    0, 0, 0, 0, 0, 0, 0, 564, 42;
    0, 0, 0, 0, 0, 0, 0, 0, 404]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt11 : residualMinor (11 : F) 0 = firstValue 11 := by
  apply value_of_factors firstLower11 firstUpper11
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower11 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    984, 1, 0, 0, 0, 0, 0, 0, 0;
    133, 540, 1, 0, 0, 0, 0, 0, 0;
    211, 87, 907, 1, 0, 0, 0, 0, 0;
    523, 280, 631, 815, 1, 0, 0, 0, 0;
    123, 686, 584, 399, 453, 1, 0, 0, 0;
    402, 298, 709, 153, 360, 987, 1, 0, 0;
    22, 987, 638, 932, 817, 954, 366, 1, 0;
    965, 279, 900, 297, 677, 619, 547, 775, 1]

private def secondUpper11 : Matrix (Fin 9) (Fin 9) F :=
  !![509, 156, 569, 762, 453, 887, 304, 419, 456;
    0, 676, 817, 874, 793, 418, 372, 601, 514;
    0, 0, 246, 533, 320, 439, 234, 27, 487;
    0, 0, 0, 658, 778, 311, 648, 906, 501;
    0, 0, 0, 0, 152, 962, 950, 124, 739;
    0, 0, 0, 0, 0, 716, 194, 475, 50;
    0, 0, 0, 0, 0, 0, 552, 5, 632;
    0, 0, 0, 0, 0, 0, 0, 431, 442;
    0, 0, 0, 0, 0, 0, 0, 0, 420]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt11 : residualMinor (11 : F) 1 = secondValue 11 := by
  apply value_of_factors secondLower11 secondUpper11
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower12 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    925, 1, 0, 0, 0, 0, 0, 0, 0;
    392, 77, 1, 0, 0, 0, 0, 0, 0;
    951, 177, 42, 1, 0, 0, 0, 0, 0;
    697, 413, 254, 14, 1, 0, 0, 0, 0;
    41, 869, 735, 969, 923, 1, 0, 0, 0;
    388, 116, 957, 23, 426, 646, 1, 0, 0;
    564, 817, 585, 597, 900, 839, 652, 1, 0;
    835, 65, 640, 806, 682, 169, 183, 652, 1]

private def firstUpper12 : Matrix (Fin 9) (Fin 9) F :=
  !![894, 411, 806, 799, 973, 191, 873, 410, 26;
    0, 636, 796, 819, 405, 266, 377, 737, 578;
    0, 0, 976, 309, 315, 336, 925, 481, 851;
    0, 0, 0, 616, 831, 322, 691, 577, 446;
    0, 0, 0, 0, 883, 885, 509, 214, 27;
    0, 0, 0, 0, 0, 456, 371, 710, 222;
    0, 0, 0, 0, 0, 0, 70, 806, 922;
    0, 0, 0, 0, 0, 0, 0, 91, 422;
    0, 0, 0, 0, 0, 0, 0, 0, 917]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt12 : residualMinor (12 : F) 0 = firstValue 12 := by
  apply value_of_factors firstLower12 firstUpper12
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower12 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    990, 1, 0, 0, 0, 0, 0, 0, 0;
    363, 928, 1, 0, 0, 0, 0, 0, 0;
    366, 497, 501, 1, 0, 0, 0, 0, 0;
    333, 975, 819, 539, 1, 0, 0, 0, 0;
    955, 892, 155, 478, 369, 1, 0, 0, 0;
    225, 237, 97, 622, 742, 423, 1, 0, 0;
    153, 109, 1002, 196, 15, 618, 683, 1, 0;
    632, 719, 666, 460, 969, 858, 926, 184, 1]

private def secondUpper12 : Matrix (Fin 9) (Fin 9) F :=
  !![836, 86, 709, 813, 788, 421, 619, 269, 85;
    0, 34, 40, 609, 239, 293, 355, 669, 9;
    0, 0, 995, 629, 935, 906, 662, 944, 198;
    0, 0, 0, 19, 237, 98, 42, 487, 187;
    0, 0, 0, 0, 59, 938, 210, 568, 633;
    0, 0, 0, 0, 0, 741, 472, 904, 97;
    0, 0, 0, 0, 0, 0, 371, 714, 668;
    0, 0, 0, 0, 0, 0, 0, 831, 908;
    0, 0, 0, 0, 0, 0, 0, 0, 439]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt12 : residualMinor (12 : F) 1 = secondValue 12 := by
  apply value_of_factors secondLower12 secondUpper12
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower13 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    138, 1, 0, 0, 0, 0, 0, 0, 0;
    946, 642, 1, 0, 0, 0, 0, 0, 0;
    290, 563, 723, 1, 0, 0, 0, 0, 0;
    37, 262, 658, 893, 1, 0, 0, 0, 0;
    611, 222, 686, 432, 613, 1, 0, 0, 0;
    104, 913, 704, 108, 954, 993, 1, 0, 0;
    320, 578, 729, 591, 152, 855, 780, 1, 0;
    621, 555, 333, 594, 302, 108, 95, 43, 1]

private def firstUpper13 : Matrix (Fin 9) (Fin 9) F :=
  !![460, 67, 4, 340, 68, 294, 133, 426, 708;
    0, 258, 938, 194, 795, 703, 843, 475, 984;
    0, 0, 59, 997, 14, 662, 927, 807, 325;
    0, 0, 0, 996, 51, 761, 300, 735, 229;
    0, 0, 0, 0, 747, 756, 643, 611, 347;
    0, 0, 0, 0, 0, 410, 391, 971, 423;
    0, 0, 0, 0, 0, 0, 858, 839, 328;
    0, 0, 0, 0, 0, 0, 0, 357, 893;
    0, 0, 0, 0, 0, 0, 0, 0, 357]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt13 : residualMinor (13 : F) 0 = firstValue 13 := by
  apply value_of_factors firstLower13 firstUpper13
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower13 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    854, 1, 0, 0, 0, 0, 0, 0, 0;
    754, 22, 1, 0, 0, 0, 0, 0, 0;
    882, 495, 951, 1, 0, 0, 0, 0, 0;
    51, 1006, 356, 670, 1, 0, 0, 0, 0;
    528, 479, 295, 536, 2, 1, 0, 0, 0;
    829, 609, 623, 990, 80, 678, 1, 0, 0;
    809, 471, 259, 891, 279, 118, 172, 1, 0;
    929, 741, 329, 895, 162, 874, 248, 644, 1]

private def secondUpper13 : Matrix (Fin 9) (Fin 9) F :=
  !![280, 203, 922, 1, 313, 96, 524, 349, 258;
    0, 609, 113, 855, 172, 660, 526, 350, 445;
    0, 0, 184, 814, 967, 475, 961, 1, 716;
    0, 0, 0, 831, 828, 475, 292, 750, 975;
    0, 0, 0, 0, 636, 406, 570, 370, 673;
    0, 0, 0, 0, 0, 749, 622, 774, 603;
    0, 0, 0, 0, 0, 0, 1000, 672, 493;
    0, 0, 0, 0, 0, 0, 0, 427, 317;
    0, 0, 0, 0, 0, 0, 0, 0, 977]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt13 : residualMinor (13 : F) 1 = secondValue 13 := by
  apply value_of_factors secondLower13 secondUpper13
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower14 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    763, 1, 0, 0, 0, 0, 0, 0, 0;
    427, 246, 1, 0, 0, 0, 0, 0, 0;
    612, 174, 548, 1, 0, 0, 0, 0, 0;
    813, 435, 770, 866, 1, 0, 0, 0, 0;
    3, 547, 818, 266, 252, 1, 0, 0, 0;
    772, 677, 587, 519, 177, 71, 1, 0, 0;
    695, 457, 2, 391, 802, 637, 959, 1, 0;
    162, 517, 521, 818, 845, 956, 503, 277, 1]

private def firstUpper14 : Matrix (Fin 9) (Fin 9) F :=
  !![770, 321, 395, 582, 438, 226, 822, 483, 689;
    0, 677, 132, 520, 57, 233, 429, 790, 36;
    0, 0, 911, 760, 284, 215, 850, 384, 447;
    0, 0, 0, 583, 276, 938, 322, 823, 895;
    0, 0, 0, 0, 13, 515, 638, 984, 181;
    0, 0, 0, 0, 0, 471, 813, 414, 865;
    0, 0, 0, 0, 0, 0, 350, 802, 345;
    0, 0, 0, 0, 0, 0, 0, 335, 736;
    0, 0, 0, 0, 0, 0, 0, 0, 532]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt14 : residualMinor (14 : F) 0 = firstValue 14 := by
  apply value_of_factors firstLower14 firstUpper14
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower14 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    912, 1, 0, 0, 0, 0, 0, 0, 0;
    783, 241, 1, 0, 0, 0, 0, 0, 0;
    426, 151, 965, 1, 0, 0, 0, 0, 0;
    891, 358, 970, 115, 1, 0, 0, 0, 0;
    66, 27, 708, 193, 1003, 1, 0, 0, 0;
    798, 128, 853, 855, 847, 629, 1, 0, 0;
    200, 574, 808, 363, 909, 865, 382, 1, 0;
    834, 278, 248, 732, 432, 246, 297, 498, 1]

private def secondUpper14 : Matrix (Fin 9) (Fin 9) F :=
  !![987, 608, 976, 555, 216, 633, 544, 155, 612;
    0, 867, 661, 984, 35, 993, 317, 934, 896;
    0, 0, 983, 113, 562, 267, 434, 20, 875;
    0, 0, 0, 374, 87, 749, 333, 221, 458;
    0, 0, 0, 0, 774, 862, 910, 466, 426;
    0, 0, 0, 0, 0, 192, 268, 491, 912;
    0, 0, 0, 0, 0, 0, 882, 363, 55;
    0, 0, 0, 0, 0, 0, 0, 521, 256;
    0, 0, 0, 0, 0, 0, 0, 0, 845]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt14 : residualMinor (14 : F) 1 = secondValue 14 := by
  apply value_of_factors secondLower14 secondUpper14
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower15 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    314, 1, 0, 0, 0, 0, 0, 0, 0;
    850, 164, 1, 0, 0, 0, 0, 0, 0;
    735, 351, 480, 1, 0, 0, 0, 0, 0;
    932, 676, 171, 407, 1, 0, 0, 0, 0;
    414, 198, 356, 300, 791, 1, 0, 0, 0;
    102, 1006, 682, 494, 982, 674, 1, 0, 0;
    726, 1, 144, 825, 840, 428, 101, 1, 0;
    905, 457, 78, 183, 363, 400, 63, 117, 1]

private def firstUpper15 : Matrix (Fin 9) (Fin 9) F :=
  !![354, 924, 117, 388, 321, 461, 1, 445, 151;
    0, 45, 132, 925, 428, 106, 43, 269, 420;
    0, 0, 79, 800, 154, 646, 520, 494, 165;
    0, 0, 0, 142, 920, 67, 705, 484, 459;
    0, 0, 0, 0, 379, 791, 319, 33, 460;
    0, 0, 0, 0, 0, 933, 970, 624, 251;
    0, 0, 0, 0, 0, 0, 1005, 269, 851;
    0, 0, 0, 0, 0, 0, 0, 884, 5;
    0, 0, 0, 0, 0, 0, 0, 0, 550]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt15 : residualMinor (15 : F) 0 = firstValue 15 := by
  apply value_of_factors firstLower15 firstUpper15
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower15 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    899, 1, 0, 0, 0, 0, 0, 0, 0;
    222, 417, 1, 0, 0, 0, 0, 0, 0;
    294, 946, 676, 1, 0, 0, 0, 0, 0;
    25, 210, 463, 922, 1, 0, 0, 0, 0;
    978, 800, 416, 915, 783, 1, 0, 0, 0;
    189, 432, 232, 592, 660, 379, 1, 0, 0;
    772, 43, 652, 473, 653, 783, 723, 1, 0;
    547, 859, 528, 74, 240, 495, 895, 319, 1]

private def secondUpper15 : Matrix (Fin 9) (Fin 9) F :=
  !![890, 650, 996, 787, 76, 764, 246, 746, 384;
    0, 459, 125, 464, 610, 866, 174, 79, 273;
    0, 0, 299, 81, 315, 230, 314, 307, 324;
    0, 0, 0, 525, 800, 437, 579, 104, 136;
    0, 0, 0, 0, 424, 100, 81, 419, 151;
    0, 0, 0, 0, 0, 967, 196, 314, 183;
    0, 0, 0, 0, 0, 0, 940, 75, 859;
    0, 0, 0, 0, 0, 0, 0, 817, 721;
    0, 0, 0, 0, 0, 0, 0, 0, 225]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt15 : residualMinor (15 : F) 1 = secondValue 15 := by
  apply value_of_factors secondLower15 secondUpper15
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 8 through 15. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((8 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt8, secondAt8⟩
  · exact ⟨firstAt9, secondAt9⟩
  · exact ⟨firstAt10, secondAt10⟩
  · exact ⟨firstAt11, secondAt11⟩
  · exact ⟨firstAt12, secondAt12⟩
  · exact ⟨firstAt13, secondAt13⟩
  · exact ⟨firstAt14, secondAt14⟩
  · exact ⟨firstAt15, secondAt15⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch8
