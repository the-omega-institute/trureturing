/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch32
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch32
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch32

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower32 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    73, 1, 0, 0, 0, 0, 0, 0, 0;
    774, 256, 1, 0, 0, 0, 0, 0, 0;
    148, 200, 284, 1, 0, 0, 0, 0, 0;
    105, 816, 96, 96, 1, 0, 0, 0, 0;
    732, 101, 832, 376, 497, 1, 0, 0, 0;
    694, 35, 378, 508, 425, 383, 1, 0, 0;
    624, 614, 590, 358, 799, 627, 487, 1, 0;
    391, 57, 785, 6, 739, 780, 809, 760, 1]

private def firstUpper32 : Matrix (Fin 9) (Fin 9) F :=
  !![104, 158, 592, 326, 54, 500, 83, 144, 543;
    0, 735, 333, 721, 555, 54, 999, 120, 516;
    0, 0, 686, 773, 301, 603, 794, 585, 996;
    0, 0, 0, 97, 655, 122, 743, 900, 808;
    0, 0, 0, 0, 708, 235, 223, 542, 945;
    0, 0, 0, 0, 0, 606, 517, 460, 684;
    0, 0, 0, 0, 0, 0, 24, 804, 208;
    0, 0, 0, 0, 0, 0, 0, 465, 605;
    0, 0, 0, 0, 0, 0, 0, 0, 140]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt32 : residualMinor (32 : F) 0 = firstValue 32 := by
  apply value_of_factors firstLower32 firstUpper32
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower32 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    302, 1, 0, 0, 0, 0, 0, 0, 0;
    761, 129, 1, 0, 0, 0, 0, 0, 0;
    120, 589, 363, 1, 0, 0, 0, 0, 0;
    315, 60, 979, 625, 1, 0, 0, 0, 0;
    447, 569, 607, 535, 476, 1, 0, 0, 0;
    552, 499, 599, 119, 85, 85, 1, 0, 0;
    554, 877, 317, 362, 370, 463, 234, 1, 0;
    353, 51, 333, 556, 67, 1004, 176, 585, 1]

private def secondUpper32 : Matrix (Fin 9) (Fin 9) F :=
  !![173, 453, 293, 521, 314, 115, 149, 860, 735;
    0, 579, 468, 365, 479, 815, 402, 135, 814;
    0, 0, 475, 161, 476, 923, 147, 611, 23;
    0, 0, 0, 454, 97, 402, 143, 563, 213;
    0, 0, 0, 0, 682, 992, 382, 783, 267;
    0, 0, 0, 0, 0, 240, 996, 76, 738;
    0, 0, 0, 0, 0, 0, 939, 454, 95;
    0, 0, 0, 0, 0, 0, 0, 271, 954;
    0, 0, 0, 0, 0, 0, 0, 0, 760]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt32 : residualMinor (32 : F) 1 = secondValue 32 := by
  apply value_of_factors secondLower32 secondUpper32
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower33 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    191, 1, 0, 0, 0, 0, 0, 0, 0;
    276, 910, 1, 0, 0, 0, 0, 0, 0;
    80, 64, 574, 1, 0, 0, 0, 0, 0;
    898, 345, 713, 439, 1, 0, 0, 0, 0;
    382, 138, 18, 482, 543, 1, 0, 0, 0;
    589, 117, 4, 527, 658, 711, 1, 0, 0;
    824, 1000, 772, 869, 1008, 634, 980, 1, 0;
    233, 967, 37, 757, 163, 891, 458, 943, 1]

private def firstUpper33 : Matrix (Fin 9) (Fin 9) F :=
  !![211, 316, 869, 528, 536, 402, 440, 770, 970;
    0, 533, 1000, 210, 650, 628, 67, 757, 868;
    0, 0, 281, 432, 787, 268, 513, 303, 904;
    0, 0, 0, 490, 384, 13, 428, 951, 83;
    0, 0, 0, 0, 695, 139, 343, 54, 31;
    0, 0, 0, 0, 0, 29, 336, 610, 390;
    0, 0, 0, 0, 0, 0, 988, 416, 350;
    0, 0, 0, 0, 0, 0, 0, 468, 89;
    0, 0, 0, 0, 0, 0, 0, 0, 239]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt33 : residualMinor (33 : F) 0 = firstValue 33 := by
  apply value_of_factors firstLower33 firstUpper33
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower33 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    608, 1, 0, 0, 0, 0, 0, 0, 0;
    416, 771, 1, 0, 0, 0, 0, 0, 0;
    377, 305, 27, 1, 0, 0, 0, 0, 0;
    71, 632, 546, 451, 1, 0, 0, 0, 0;
    385, 476, 495, 93, 714, 1, 0, 0, 0;
    890, 634, 649, 983, 26, 501, 1, 0, 0;
    114, 783, 166, 752, 820, 146, 235, 1, 0;
    671, 872, 487, 195, 331, 228, 623, 693, 1]

private def secondUpper33 : Matrix (Fin 9) (Fin 9) F :=
  !![973, 198, 657, 8, 972, 955, 103, 252, 353;
    0, 36, 602, 339, 406, 261, 294, 665, 775;
    0, 0, 999, 924, 647, 442, 175, 617, 332;
    0, 0, 0, 240, 607, 639, 361, 703, 272;
    0, 0, 0, 0, 46, 200, 113, 699, 526;
    0, 0, 0, 0, 0, 125, 189, 426, 338;
    0, 0, 0, 0, 0, 0, 19, 233, 953;
    0, 0, 0, 0, 0, 0, 0, 750, 640;
    0, 0, 0, 0, 0, 0, 0, 0, 726]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt33 : residualMinor (33 : F) 1 = secondValue 33 := by
  apply value_of_factors secondLower33 secondUpper33
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower34 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    994, 1, 0, 0, 0, 0, 0, 0, 0;
    812, 258, 1, 0, 0, 0, 0, 0, 0;
    557, 758, 915, 1, 0, 0, 0, 0, 0;
    319, 882, 120, 562, 1, 0, 0, 0, 0;
    95, 125, 495, 428, 50, 1, 0, 0, 0;
    150, 114, 670, 593, 854, 339, 1, 0, 0;
    903, 836, 904, 771, 373, 543, 799, 1, 0;
    787, 797, 589, 803, 238, 341, 313, 985, 1]

private def firstUpper34 : Matrix (Fin 9) (Fin 9) F :=
  !![92, 582, 392, 171, 842, 460, 217, 102, 990;
    0, 893, 968, 662, 695, 887, 759, 378, 155;
    0, 0, 870, 786, 892, 509, 361, 31, 806;
    0, 0, 0, 129, 507, 133, 775, 477, 927;
    0, 0, 0, 0, 632, 359, 730, 602, 17;
    0, 0, 0, 0, 0, 251, 612, 383, 104;
    0, 0, 0, 0, 0, 0, 882, 555, 1005;
    0, 0, 0, 0, 0, 0, 0, 2, 889;
    0, 0, 0, 0, 0, 0, 0, 0, 237]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt34 : residualMinor (34 : F) 0 = firstValue 34 := by
  apply value_of_factors firstLower34 firstUpper34
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower34 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    989, 1, 0, 0, 0, 0, 0, 0, 0;
    971, 238, 1, 0, 0, 0, 0, 0, 0;
    249, 365, 34, 1, 0, 0, 0, 0, 0;
    440, 396, 668, 384, 1, 0, 0, 0, 0;
    788, 157, 567, 527, 592, 1, 0, 0, 0;
    84, 677, 630, 810, 559, 154, 1, 0, 0;
    130, 300, 984, 455, 782, 466, 36, 1, 0;
    883, 887, 395, 178, 980, 354, 678, 799, 1]

private def secondUpper34 : Matrix (Fin 9) (Fin 9) F :=
  !![257, 702, 146, 790, 960, 565, 818, 917, 516;
    0, 149, 26, 780, 202, 242, 747, 35, 670;
    0, 0, 211, 437, 714, 700, 678, 50, 542;
    0, 0, 0, 786, 287, 440, 185, 220, 821;
    0, 0, 0, 0, 1004, 520, 243, 192, 442;
    0, 0, 0, 0, 0, 191, 828, 945, 44;
    0, 0, 0, 0, 0, 0, 406, 291, 445;
    0, 0, 0, 0, 0, 0, 0, 739, 617;
    0, 0, 0, 0, 0, 0, 0, 0, 963]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt34 : residualMinor (34 : F) 1 = secondValue 34 := by
  apply value_of_factors secondLower34 secondUpper34
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower35 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    331, 1, 0, 0, 0, 0, 0, 0, 0;
    947, 983, 1, 0, 0, 0, 0, 0, 0;
    110, 276, 234, 1, 0, 0, 0, 0, 0;
    175, 734, 778, 488, 1, 0, 0, 0, 0;
    828, 277, 779, 448, 274, 1, 0, 0, 0;
    898, 316, 824, 921, 636, 709, 1, 0, 0;
    223, 161, 461, 683, 785, 1008, 163, 1, 0;
    183, 323, 795, 967, 741, 880, 838, 230, 1]

private def firstUpper35 : Matrix (Fin 9) (Fin 9) F :=
  !![354, 310, 266, 604, 812, 671, 695, 761, 230;
    0, 699, 330, 128, 676, 117, 11, 962, 422;
    0, 0, 950, 324, 447, 86, 27, 833, 708;
    0, 0, 0, 451, 166, 533, 989, 24, 296;
    0, 0, 0, 0, 3, 702, 270, 661, 262;
    0, 0, 0, 0, 0, 690, 583, 163, 859;
    0, 0, 0, 0, 0, 0, 165, 551, 261;
    0, 0, 0, 0, 0, 0, 0, 734, 343;
    0, 0, 0, 0, 0, 0, 0, 0, 641]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt35 : residualMinor (35 : F) 0 = firstValue 35 := by
  apply value_of_factors firstLower35 firstUpper35
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower35 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    979, 1, 0, 0, 0, 0, 0, 0, 0;
    259, 82, 1, 0, 0, 0, 0, 0, 0;
    109, 778, 315, 1, 0, 0, 0, 0, 0;
    612, 426, 156, 74, 1, 0, 0, 0, 0;
    322, 185, 376, 805, 145, 1, 0, 0, 0;
    715, 901, 251, 553, 453, 667, 1, 0, 0;
    158, 667, 517, 437, 727, 760, 519, 1, 0;
    410, 306, 663, 131, 422, 912, 822, 359, 1]

private def secondUpper35 : Matrix (Fin 9) (Fin 9) F :=
  !![391, 540, 511, 46, 63, 673, 414, 52, 195;
    0, 447, 788, 641, 926, 248, 316, 145, 673;
    0, 0, 893, 8, 709, 941, 88, 145, 955;
    0, 0, 0, 737, 115, 940, 169, 631, 872;
    0, 0, 0, 0, 325, 955, 436, 906, 188;
    0, 0, 0, 0, 0, 25, 880, 185, 416;
    0, 0, 0, 0, 0, 0, 265, 189, 209;
    0, 0, 0, 0, 0, 0, 0, 434, 786;
    0, 0, 0, 0, 0, 0, 0, 0, 880]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt35 : residualMinor (35 : F) 1 = secondValue 35 := by
  apply value_of_factors secondLower35 secondUpper35
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower36 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    692, 1, 0, 0, 0, 0, 0, 0, 0;
    472, 987, 1, 0, 0, 0, 0, 0, 0;
    204, 654, 996, 1, 0, 0, 0, 0, 0;
    433, 488, 568, 351, 1, 0, 0, 0, 0;
    348, 591, 787, 594, 842, 1, 0, 0, 0;
    432, 882, 981, 968, 544, 697, 1, 0, 0;
    92, 324, 26, 447, 356, 452, 650, 1, 0;
    526, 228, 570, 812, 99, 46, 1005, 432, 1]

private def firstUpper36 : Matrix (Fin 9) (Fin 9) F :=
  !![581, 956, 580, 475, 960, 929, 107, 160, 652;
    0, 520, 779, 577, 302, 548, 209, 134, 19;
    0, 0, 990, 358, 95, 772, 718, 479, 381;
    0, 0, 0, 937, 476, 311, 203, 199, 177;
    0, 0, 0, 0, 756, 202, 299, 446, 365;
    0, 0, 0, 0, 0, 863, 456, 672, 689;
    0, 0, 0, 0, 0, 0, 817, 551, 592;
    0, 0, 0, 0, 0, 0, 0, 370, 379;
    0, 0, 0, 0, 0, 0, 0, 0, 760]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt36 : residualMinor (36 : F) 0 = firstValue 36 := by
  apply value_of_factors firstLower36 firstUpper36
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower36 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    224, 1, 0, 0, 0, 0, 0, 0, 0;
    698, 301, 1, 0, 0, 0, 0, 0, 0;
    165, 412, 645, 1, 0, 0, 0, 0, 0;
    687, 19, 184, 995, 1, 0, 0, 0, 0;
    975, 586, 538, 693, 30, 1, 0, 0, 0;
    795, 59, 896, 226, 147, 786, 1, 0, 0;
    29, 385, 377, 716, 585, 518, 1008, 1, 0;
    147, 299, 235, 687, 825, 864, 928, 954, 1]

private def secondUpper36 : Matrix (Fin 9) (Fin 9) F :=
  !![772, 751, 70, 227, 811, 760, 275, 893, 621;
    0, 447, 12, 954, 656, 964, 545, 623, 318;
    0, 0, 313, 352, 872, 70, 392, 802, 511;
    0, 0, 0, 672, 183, 735, 967, 137, 353;
    0, 0, 0, 0, 837, 502, 535, 689, 305;
    0, 0, 0, 0, 0, 730, 492, 347, 912;
    0, 0, 0, 0, 0, 0, 911, 890, 729;
    0, 0, 0, 0, 0, 0, 0, 858, 34;
    0, 0, 0, 0, 0, 0, 0, 0, 753]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt36 : residualMinor (36 : F) 1 = secondValue 36 := by
  apply value_of_factors secondLower36 secondUpper36
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower37 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    259, 1, 0, 0, 0, 0, 0, 0, 0;
    920, 727, 1, 0, 0, 0, 0, 0, 0;
    6, 77, 188, 1, 0, 0, 0, 0, 0;
    133, 884, 26, 590, 1, 0, 0, 0, 0;
    500, 21, 397, 24, 688, 1, 0, 0, 0;
    844, 698, 710, 192, 708, 295, 1, 0, 0;
    915, 431, 918, 914, 11, 389, 99, 1, 0;
    891, 374, 572, 982, 237, 815, 274, 773, 1]

private def firstUpper37 : Matrix (Fin 9) (Fin 9) F :=
  !![241, 313, 820, 28, 380, 762, 291, 711, 942;
    0, 145, 386, 742, 114, 246, 929, 548, 243;
    0, 0, 873, 633, 828, 569, 826, 696, 434;
    0, 0, 0, 794, 630, 62, 940, 848, 961;
    0, 0, 0, 0, 416, 187, 694, 621, 213;
    0, 0, 0, 0, 0, 149, 450, 567, 226;
    0, 0, 0, 0, 0, 0, 999, 969, 989;
    0, 0, 0, 0, 0, 0, 0, 47, 771;
    0, 0, 0, 0, 0, 0, 0, 0, 343]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt37 : residualMinor (37 : F) 0 = firstValue 37 := by
  apply value_of_factors firstLower37 firstUpper37
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower37 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    911, 1, 0, 0, 0, 0, 0, 0, 0;
    67, 641, 1, 0, 0, 0, 0, 0, 0;
    886, 471, 703, 1, 0, 0, 0, 0, 0;
    307, 568, 609, 305, 1, 0, 0, 0, 0;
    159, 647, 214, 117, 645, 1, 0, 0, 0;
    794, 375, 654, 936, 133, 847, 1, 0, 0;
    455, 666, 63, 667, 1007, 570, 533, 1, 0;
    812, 955, 28, 519, 969, 726, 463, 566, 1]

private def secondUpper37 : Matrix (Fin 9) (Fin 9) F :=
  !![411, 183, 673, 69, 111, 402, 434, 845, 77;
    0, 264, 236, 630, 440, 894, 777, 122, 526;
    0, 0, 40, 979, 551, 970, 77, 205, 155;
    0, 0, 0, 757, 102, 245, 15, 805, 827;
    0, 0, 0, 0, 239, 981, 440, 396, 325;
    0, 0, 0, 0, 0, 893, 593, 403, 1000;
    0, 0, 0, 0, 0, 0, 792, 4, 836;
    0, 0, 0, 0, 0, 0, 0, 213, 511;
    0, 0, 0, 0, 0, 0, 0, 0, 984]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt37 : residualMinor (37 : F) 1 = secondValue 37 := by
  apply value_of_factors secondLower37 secondUpper37
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower38 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    389, 1, 0, 0, 0, 0, 0, 0, 0;
    809, 990, 1, 0, 0, 0, 0, 0, 0;
    918, 443, 69, 1, 0, 0, 0, 0, 0;
    471, 879, 186, 616, 1, 0, 0, 0, 0;
    119, 672, 358, 355, 289, 1, 0, 0, 0;
    995, 206, 64, 351, 658, 574, 1, 0, 0;
    478, 596, 156, 961, 78, 755, 574, 1, 0;
    997, 279, 124, 1006, 676, 987, 494, 313, 1]

private def firstUpper38 : Matrix (Fin 9) (Fin 9) F :=
  !![597, 591, 725, 798, 45, 191, 366, 631, 946;
    0, 36, 952, 585, 768, 663, 982, 826, 859;
    0, 0, 337, 138, 344, 161, 880, 476, 165;
    0, 0, 0, 98, 369, 782, 953, 413, 974;
    0, 0, 0, 0, 460, 370, 392, 152, 739;
    0, 0, 0, 0, 0, 222, 906, 481, 597;
    0, 0, 0, 0, 0, 0, 168, 447, 522;
    0, 0, 0, 0, 0, 0, 0, 825, 650;
    0, 0, 0, 0, 0, 0, 0, 0, 608]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt38 : residualMinor (38 : F) 0 = firstValue 38 := by
  apply value_of_factors firstLower38 firstUpper38
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower38 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    994, 1, 0, 0, 0, 0, 0, 0, 0;
    611, 173, 1, 0, 0, 0, 0, 0, 0;
    773, 757, 960, 1, 0, 0, 0, 0, 0;
    604, 926, 392, 19, 1, 0, 0, 0, 0;
    319, 636, 635, 354, 680, 1, 0, 0, 0;
    884, 884, 587, 348, 967, 827, 1, 0, 0;
    60, 299, 307, 583, 616, 923, 113, 1, 0;
    514, 522, 147, 742, 924, 731, 66, 34, 1]

private def secondUpper38 : Matrix (Fin 9) (Fin 9) F :=
  !![466, 317, 951, 847, 525, 76, 377, 593, 471;
    0, 602, 596, 832, 923, 427, 688, 912, 570;
    0, 0, 640, 395, 798, 587, 584, 387, 536;
    0, 0, 0, 497, 91, 580, 634, 982, 632;
    0, 0, 0, 0, 118, 863, 848, 368, 506;
    0, 0, 0, 0, 0, 858, 573, 325, 901;
    0, 0, 0, 0, 0, 0, 132, 505, 353;
    0, 0, 0, 0, 0, 0, 0, 367, 347;
    0, 0, 0, 0, 0, 0, 0, 0, 976]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt38 : residualMinor (38 : F) 1 = secondValue 38 := by
  apply value_of_factors secondLower38 secondUpper38
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower39 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    869, 1, 0, 0, 0, 0, 0, 0, 0;
    855, 299, 1, 0, 0, 0, 0, 0, 0;
    681, 977, 409, 1, 0, 0, 0, 0, 0;
    142, 811, 679, 679, 1, 0, 0, 0, 0;
    154, 896, 321, 223, 933, 1, 0, 0, 0;
    692, 224, 562, 983, 714, 934, 1, 0, 0;
    238, 740, 483, 373, 786, 1001, 111, 1, 0;
    954, 980, 453, 830, 725, 195, 799, 62, 1]

private def firstUpper39 : Matrix (Fin 9) (Fin 9) F :=
  !![354, 104, 836, 751, 209, 647, 81, 855, 407;
    0, 74, 50, 883, 34, 212, 148, 440, 818;
    0, 0, 24, 964, 51, 281, 184, 621, 591;
    0, 0, 0, 704, 799, 151, 797, 382, 565;
    0, 0, 0, 0, 314, 439, 67, 754, 623;
    0, 0, 0, 0, 0, 291, 60, 260, 244;
    0, 0, 0, 0, 0, 0, 714, 895, 26;
    0, 0, 0, 0, 0, 0, 0, 155, 465;
    0, 0, 0, 0, 0, 0, 0, 0, 824]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt39 : residualMinor (39 : F) 0 = firstValue 39 := by
  apply value_of_factors firstLower39 firstUpper39
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower39 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    325, 1, 0, 0, 0, 0, 0, 0, 0;
    298, 798, 1, 0, 0, 0, 0, 0, 0;
    593, 806, 108, 1, 0, 0, 0, 0, 0;
    376, 24, 912, 885, 1, 0, 0, 0, 0;
    767, 330, 537, 400, 611, 1, 0, 0, 0;
    55, 462, 76, 746, 329, 486, 1, 0, 0;
    476, 855, 875, 139, 105, 398, 548, 1, 0;
    654, 217, 96, 551, 191, 566, 580, 1007, 1]

private def secondUpper39 : Matrix (Fin 9) (Fin 9) F :=
  !![651, 954, 192, 83, 777, 711, 82, 480, 366;
    0, 362, 212, 947, 769, 428, 500, 197, 454;
    0, 0, 880, 521, 563, 874, 18, 947, 718;
    0, 0, 0, 305, 250, 710, 833, 382, 263;
    0, 0, 0, 0, 65, 751, 234, 124, 462;
    0, 0, 0, 0, 0, 160, 117, 846, 869;
    0, 0, 0, 0, 0, 0, 728, 178, 532;
    0, 0, 0, 0, 0, 0, 0, 249, 358;
    0, 0, 0, 0, 0, 0, 0, 0, 368]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt39 : residualMinor (39 : F) 1 = secondValue 39 := by
  apply value_of_factors secondLower39 secondUpper39
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 32 through 39. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((32 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt32, secondAt32⟩
  · exact ⟨firstAt33, secondAt33⟩
  · exact ⟨firstAt34, secondAt34⟩
  · exact ⟨firstAt35, secondAt35⟩
  · exact ⟨firstAt36, secondAt36⟩
  · exact ⟨firstAt37, secondAt37⟩
  · exact ⟨firstAt38, secondAt38⟩
  · exact ⟨firstAt39, secondAt39⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch32
