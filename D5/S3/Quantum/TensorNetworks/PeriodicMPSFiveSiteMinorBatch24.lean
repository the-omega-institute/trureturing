/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch24
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch24
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch24

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower24 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    26, 1, 0, 0, 0, 0, 0, 0, 0;
    854, 817, 1, 0, 0, 0, 0, 0, 0;
    77, 178, 462, 1, 0, 0, 0, 0, 0;
    384, 972, 603, 16, 1, 0, 0, 0, 0;
    176, 718, 918, 597, 275, 1, 0, 0, 0;
    232, 770, 410, 821, 488, 931, 1, 0, 0;
    14, 987, 367, 817, 429, 961, 26, 1, 0;
    322, 504, 696, 606, 131, 733, 397, 474, 1]

private def firstUpper24 : Matrix (Fin 9) (Fin 9) F :=
  !![459, 620, 386, 760, 37, 946, 513, 886, 205;
    0, 98, 348, 660, 124, 385, 300, 417, 898;
    0, 0, 502, 403, 360, 383, 593, 879, 237;
    0, 0, 0, 916, 527, 876, 324, 268, 833;
    0, 0, 0, 0, 74, 995, 740, 930, 151;
    0, 0, 0, 0, 0, 74, 633, 332, 687;
    0, 0, 0, 0, 0, 0, 722, 542, 519;
    0, 0, 0, 0, 0, 0, 0, 543, 338;
    0, 0, 0, 0, 0, 0, 0, 0, 442]

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
    865, 1, 0, 0, 0, 0, 0, 0, 0;
    43, 693, 1, 0, 0, 0, 0, 0, 0;
    558, 274, 319, 1, 0, 0, 0, 0, 0;
    715, 499, 218, 308, 1, 0, 0, 0, 0;
    807, 711, 479, 205, 154, 1, 0, 0, 0;
    512, 304, 849, 749, 746, 752, 1, 0, 0;
    997, 377, 971, 95, 297, 876, 1006, 1, 0;
    533, 298, 482, 737, 743, 697, 867, 973, 1]

private def secondUpper24 : Matrix (Fin 9) (Fin 9) F :=
  !![910, 121, 370, 273, 720, 374, 950, 135, 460;
    0, 345, 97, 201, 839, 135, 97, 515, 829;
    0, 0, 597, 379, 154, 139, 594, 960, 897;
    0, 0, 0, 487, 361, 919, 411, 909, 307;
    0, 0, 0, 0, 509, 327, 541, 135, 627;
    0, 0, 0, 0, 0, 134, 271, 478, 127;
    0, 0, 0, 0, 0, 0, 20, 588, 908;
    0, 0, 0, 0, 0, 0, 0, 819, 677;
    0, 0, 0, 0, 0, 0, 0, 0, 805]

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
    131, 1, 0, 0, 0, 0, 0, 0, 0;
    3, 979, 1, 0, 0, 0, 0, 0, 0;
    749, 293, 799, 1, 0, 0, 0, 0, 0;
    139, 856, 519, 218, 1, 0, 0, 0, 0;
    974, 214, 876, 845, 621, 1, 0, 0, 0;
    178, 854, 24, 791, 958, 797, 1, 0, 0;
    454, 52, 157, 826, 532, 208, 78, 1, 0;
    220, 57, 668, 542, 824, 42, 358, 791, 1]

private def firstUpper25 : Matrix (Fin 9) (Fin 9) F :=
  !![258, 379, 78, 118, 342, 982, 706, 507, 487;
    0, 717, 640, 679, 968, 879, 928, 864, 74;
    0, 0, 80, 371, 425, 731, 216, 122, 702;
    0, 0, 0, 328, 838, 182, 775, 164, 372;
    0, 0, 0, 0, 383, 697, 974, 760, 320;
    0, 0, 0, 0, 0, 59, 887, 701, 237;
    0, 0, 0, 0, 0, 0, 152, 378, 163;
    0, 0, 0, 0, 0, 0, 0, 267, 503;
    0, 0, 0, 0, 0, 0, 0, 0, 507]

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
    409, 1, 0, 0, 0, 0, 0, 0, 0;
    668, 397, 1, 0, 0, 0, 0, 0, 0;
    793, 518, 964, 1, 0, 0, 0, 0, 0;
    419, 247, 73, 544, 1, 0, 0, 0, 0;
    451, 708, 491, 143, 463, 1, 0, 0, 0;
    833, 913, 782, 855, 471, 456, 1, 0, 0;
    686, 170, 976, 812, 735, 234, 223, 1, 0;
    25, 216, 585, 653, 340, 748, 804, 379, 1]

private def secondUpper25 : Matrix (Fin 9) (Fin 9) F :=
  !![162, 941, 889, 268, 413, 545, 827, 55, 368;
    0, 485, 407, 362, 960, 453, 358, 390, 133;
    0, 0, 595, 677, 518, 464, 358, 79, 991;
    0, 0, 0, 603, 14, 50, 589, 101, 967;
    0, 0, 0, 0, 847, 275, 540, 294, 220;
    0, 0, 0, 0, 0, 937, 910, 466, 944;
    0, 0, 0, 0, 0, 0, 667, 915, 127;
    0, 0, 0, 0, 0, 0, 0, 343, 740;
    0, 0, 0, 0, 0, 0, 0, 0, 729]

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
    410, 1, 0, 0, 0, 0, 0, 0, 0;
    565, 792, 1, 0, 0, 0, 0, 0, 0;
    344, 395, 138, 1, 0, 0, 0, 0, 0;
    625, 638, 852, 321, 1, 0, 0, 0, 0;
    506, 640, 310, 828, 224, 1, 0, 0, 0;
    76, 632, 897, 642, 928, 992, 1, 0, 0;
    48, 746, 657, 905, 469, 618, 744, 1, 0;
    311, 105, 387, 577, 735, 853, 278, 345, 1]

private def firstUpper26 : Matrix (Fin 9) (Fin 9) F :=
  !![112, 480, 308, 922, 415, 669, 15, 719, 919;
    0, 342, 231, 783, 93, 750, 317, 119, 388;
    0, 0, 441, 634, 699, 883, 988, 102, 882;
    0, 0, 0, 737, 676, 82, 192, 407, 806;
    0, 0, 0, 0, 337, 482, 884, 930, 655;
    0, 0, 0, 0, 0, 684, 577, 873, 32;
    0, 0, 0, 0, 0, 0, 797, 984, 289;
    0, 0, 0, 0, 0, 0, 0, 203, 863;
    0, 0, 0, 0, 0, 0, 0, 0, 116]

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
    600, 1, 0, 0, 0, 0, 0, 0, 0;
    540, 872, 1, 0, 0, 0, 0, 0, 0;
    421, 13, 613, 1, 0, 0, 0, 0, 0;
    752, 596, 811, 908, 1, 0, 0, 0, 0;
    781, 331, 324, 563, 125, 1, 0, 0, 0;
    580, 326, 837, 293, 575, 179, 1, 0, 0;
    570, 389, 782, 995, 35, 494, 649, 1, 0;
    73, 224, 331, 600, 280, 567, 809, 837, 1]

private def secondUpper26 : Matrix (Fin 9) (Fin 9) F :=
  !![778, 391, 554, 480, 906, 307, 328, 453, 201;
    0, 884, 956, 1002, 982, 30, 368, 911, 292;
    0, 0, 542, 684, 538, 971, 635, 379, 109;
    0, 0, 0, 573, 643, 146, 151, 66, 796;
    0, 0, 0, 0, 149, 434, 863, 396, 203;
    0, 0, 0, 0, 0, 985, 851, 636, 141;
    0, 0, 0, 0, 0, 0, 477, 155, 203;
    0, 0, 0, 0, 0, 0, 0, 647, 625;
    0, 0, 0, 0, 0, 0, 0, 0, 596]

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
    423, 1, 0, 0, 0, 0, 0, 0, 0;
    461, 816, 1, 0, 0, 0, 0, 0, 0;
    283, 835, 577, 1, 0, 0, 0, 0, 0;
    952, 56, 123, 887, 1, 0, 0, 0, 0;
    204, 544, 204, 97, 410, 1, 0, 0, 0;
    696, 303, 262, 465, 240, 456, 1, 0, 0;
    754, 136, 959, 135, 479, 650, 35, 1, 0;
    177, 324, 695, 156, 541, 496, 586, 486, 1]

private def firstUpper27 : Matrix (Fin 9) (Fin 9) F :=
  !![943, 189, 678, 313, 148, 606, 827, 548, 495;
    0, 542, 451, 850, 996, 461, 560, 152, 68;
    0, 0, 45, 812, 47, 899, 433, 400, 238;
    0, 0, 0, 287, 502, 478, 498, 946, 876;
    0, 0, 0, 0, 952, 991, 710, 945, 898;
    0, 0, 0, 0, 0, 600, 975, 919, 984;
    0, 0, 0, 0, 0, 0, 273, 254, 361;
    0, 0, 0, 0, 0, 0, 0, 213, 269;
    0, 0, 0, 0, 0, 0, 0, 0, 892]

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
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    366, 728, 1, 0, 0, 0, 0, 0, 0;
    579, 509, 753, 1, 0, 0, 0, 0, 0;
    341, 998, 543, 953, 1, 0, 0, 0, 0;
    350, 913, 318, 427, 946, 1, 0, 0, 0;
    237, 644, 50, 437, 358, 168, 1, 0, 0;
    993, 353, 563, 280, 111, 927, 504, 1, 0;
    266, 757, 472, 455, 105, 8, 631, 199, 1]

private def secondUpper27 : Matrix (Fin 9) (Fin 9) F :=
  !![406, 624, 301, 536, 817, 666, 168, 336, 981;
    0, 778, 689, 61, 33, 513, 258, 895, 590;
    0, 0, 249, 793, 997, 879, 72, 70, 864;
    0, 0, 0, 693, 617, 95, 203, 633, 732;
    0, 0, 0, 0, 850, 882, 192, 462, 352;
    0, 0, 0, 0, 0, 694, 681, 982, 700;
    0, 0, 0, 0, 0, 0, 221, 635, 755;
    0, 0, 0, 0, 0, 0, 0, 700, 428;
    0, 0, 0, 0, 0, 0, 0, 0, 75]

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
    341, 1, 0, 0, 0, 0, 0, 0, 0;
    533, 313, 1, 0, 0, 0, 0, 0, 0;
    202, 708, 248, 1, 0, 0, 0, 0, 0;
    350, 584, 747, 506, 1, 0, 0, 0, 0;
    446, 144, 968, 869, 644, 1, 0, 0, 0;
    115, 727, 853, 668, 891, 371, 1, 0, 0;
    205, 575, 988, 286, 348, 479, 944, 1, 0;
    896, 532, 953, 902, 599, 603, 529, 201, 1]

private def firstUpper28 : Matrix (Fin 9) (Fin 9) F :=
  !![337, 421, 552, 776, 1004, 767, 966, 495, 245;
    0, 143, 950, 592, 355, 885, 398, 245, 168;
    0, 0, 499, 494, 579, 512, 529, 869, 487;
    0, 0, 0, 782, 741, 70, 40, 887, 814;
    0, 0, 0, 0, 383, 150, 919, 254, 240;
    0, 0, 0, 0, 0, 4, 110, 54, 750;
    0, 0, 0, 0, 0, 0, 685, 955, 405;
    0, 0, 0, 0, 0, 0, 0, 828, 840;
    0, 0, 0, 0, 0, 0, 0, 0, 177]

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
    427, 1, 0, 0, 0, 0, 0, 0, 0;
    636, 486, 1, 0, 0, 0, 0, 0, 0;
    746, 627, 809, 1, 0, 0, 0, 0, 0;
    693, 475, 266, 952, 1, 0, 0, 0, 0;
    457, 987, 172, 768, 107, 1, 0, 0, 0;
    720, 625, 790, 10, 339, 903, 1, 0, 0;
    277, 311, 451, 613, 723, 549, 405, 1, 0;
    325, 681, 604, 833, 496, 470, 684, 859, 1]

private def secondUpper28 : Matrix (Fin 9) (Fin 9) F :=
  !![1002, 60, 756, 948, 827, 414, 571, 990, 736;
    0, 31, 567, 663, 689, 898, 222, 578, 502;
    0, 0, 154, 159, 917, 722, 430, 926, 304;
    0, 0, 0, 574, 321, 459, 845, 910, 595;
    0, 0, 0, 0, 409, 94, 751, 170, 870;
    0, 0, 0, 0, 0, 218, 528, 238, 93;
    0, 0, 0, 0, 0, 0, 352, 303, 92;
    0, 0, 0, 0, 0, 0, 0, 439, 601;
    0, 0, 0, 0, 0, 0, 0, 0, 247]

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
    891, 1, 0, 0, 0, 0, 0, 0, 0;
    419, 114, 1, 0, 0, 0, 0, 0, 0;
    470, 271, 124, 1, 0, 0, 0, 0, 0;
    227, 917, 934, 963, 1, 0, 0, 0, 0;
    255, 422, 699, 288, 181, 1, 0, 0, 0;
    341, 675, 1007, 735, 851, 298, 1, 0, 0;
    615, 241, 767, 755, 142, 953, 647, 1, 0;
    454, 503, 828, 758, 994, 904, 514, 180, 1]

private def firstUpper29 : Matrix (Fin 9) (Fin 9) F :=
  !![494, 27, 647, 82, 459, 223, 268, 173, 524;
    0, 560, 848, 10, 959, 724, 995, 837, 261;
    0, 0, 6, 73, 783, 761, 778, 868, 948;
    0, 0, 0, 408, 951, 123, 645, 185, 665;
    0, 0, 0, 0, 202, 440, 377, 996, 373;
    0, 0, 0, 0, 0, 520, 803, 596, 932;
    0, 0, 0, 0, 0, 0, 214, 864, 844;
    0, 0, 0, 0, 0, 0, 0, 860, 263;
    0, 0, 0, 0, 0, 0, 0, 0, 954]

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
    60, 1, 0, 0, 0, 0, 0, 0, 0;
    288, 476, 1, 0, 0, 0, 0, 0, 0;
    999, 384, 656, 1, 0, 0, 0, 0, 0;
    724, 774, 196, 896, 1, 0, 0, 0, 0;
    341, 778, 323, 342, 843, 1, 0, 0, 0;
    450, 479, 918, 897, 2, 414, 1, 0, 0;
    546, 736, 798, 383, 906, 535, 307, 1, 0;
    429, 321, 52, 743, 855, 396, 4, 855, 1]

private def secondUpper29 : Matrix (Fin 9) (Fin 9) F :=
  !![680, 388, 19, 692, 489, 827, 744, 396, 858;
    0, 328, 46, 273, 195, 465, 406, 50, 966;
    0, 0, 370, 955, 166, 747, 592, 655, 415;
    0, 0, 0, 330, 257, 546, 302, 295, 406;
    0, 0, 0, 0, 545, 356, 243, 947, 872;
    0, 0, 0, 0, 0, 249, 996, 924, 162;
    0, 0, 0, 0, 0, 0, 62, 838, 979;
    0, 0, 0, 0, 0, 0, 0, 587, 174;
    0, 0, 0, 0, 0, 0, 0, 0, 396]

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
    576, 1, 0, 0, 0, 0, 0, 0, 0;
    602, 635, 1, 0, 0, 0, 0, 0, 0;
    74, 104, 468, 1, 0, 0, 0, 0, 0;
    284, 954, 105, 991, 1, 0, 0, 0, 0;
    353, 78, 322, 27, 237, 1, 0, 0, 0;
    206, 471, 775, 154, 38, 57, 1, 0, 0;
    39, 41, 987, 140, 305, 0, 167, 1, 0;
    443, 313, 529, 55, 388, 991, 780, 682, 1]

private def firstUpper30 : Matrix (Fin 9) (Fin 9) F :=
  !![455, 424, 945, 82, 231, 731, 177, 981, 220;
    0, 985, 343, 620, 517, 412, 887, 838, 84;
    0, 0, 311, 342, 851, 122, 874, 788, 776;
    0, 0, 0, 606, 672, 149, 116, 786, 694;
    0, 0, 0, 0, 1000, 219, 268, 8, 880;
    0, 0, 0, 0, 0, 66, 93, 599, 268;
    0, 0, 0, 0, 0, 0, 62, 685, 672;
    0, 0, 0, 0, 0, 0, 0, 461, 112;
    0, 0, 0, 0, 0, 0, 0, 0, 166]

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
    129, 1, 0, 0, 0, 0, 0, 0, 0;
    67, 36, 1, 0, 0, 0, 0, 0, 0;
    300, 163, 189, 1, 0, 0, 0, 0, 0;
    946, 102, 632, 714, 1, 0, 0, 0, 0;
    434, 202, 131, 778, 850, 1, 0, 0, 0;
    375, 566, 992, 257, 851, 548, 1, 0, 0;
    162, 206, 546, 489, 992, 861, 397, 1, 0;
    803, 631, 404, 138, 291, 144, 908, 31, 1]

private def secondUpper30 : Matrix (Fin 9) (Fin 9) F :=
  !![167, 675, 946, 832, 14, 305, 752, 826, 898;
    0, 730, 867, 55, 597, 721, 786, 245, 872;
    0, 0, 238, 244, 809, 572, 719, 877, 152;
    0, 0, 0, 186, 473, 514, 669, 153, 73;
    0, 0, 0, 0, 489, 711, 357, 653, 649;
    0, 0, 0, 0, 0, 945, 819, 701, 61;
    0, 0, 0, 0, 0, 0, 25, 418, 607;
    0, 0, 0, 0, 0, 0, 0, 97, 852;
    0, 0, 0, 0, 0, 0, 0, 0, 160]

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
    656, 1, 0, 0, 0, 0, 0, 0, 0;
    827, 422, 1, 0, 0, 0, 0, 0, 0;
    706, 202, 787, 1, 0, 0, 0, 0, 0;
    187, 734, 546, 674, 1, 0, 0, 0, 0;
    858, 357, 158, 727, 234, 1, 0, 0, 0;
    548, 512, 527, 907, 299, 914, 1, 0, 0;
    40, 708, 723, 421, 643, 82, 431, 1, 0;
    20, 942, 961, 879, 22, 459, 238, 602, 1]

private def firstUpper31 : Matrix (Fin 9) (Fin 9) F :=
  !![150, 819, 125, 404, 369, 915, 171, 947, 723;
    0, 194, 419, 734, 916, 121, 693, 559, 933;
    0, 0, 534, 58, 859, 125, 540, 798, 949;
    0, 0, 0, 612, 476, 417, 510, 35, 680;
    0, 0, 0, 0, 650, 109, 183, 779, 985;
    0, 0, 0, 0, 0, 769, 127, 754, 677;
    0, 0, 0, 0, 0, 0, 450, 908, 859;
    0, 0, 0, 0, 0, 0, 0, 37, 221;
    0, 0, 0, 0, 0, 0, 0, 0, 528]

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
    49, 1, 0, 0, 0, 0, 0, 0, 0;
    120, 852, 1, 0, 0, 0, 0, 0, 0;
    775, 565, 307, 1, 0, 0, 0, 0, 0;
    434, 967, 430, 335, 1, 0, 0, 0, 0;
    995, 736, 385, 905, 137, 1, 0, 0, 0;
    359, 635, 959, 679, 604, 740, 1, 0, 0;
    413, 530, 273, 492, 523, 255, 734, 1, 0;
    177, 913, 427, 166, 16, 867, 1000, 702, 1]

private def secondUpper31 : Matrix (Fin 9) (Fin 9) F :=
  !![164, 387, 922, 848, 253, 284, 743, 510, 628;
    0, 878, 917, 208, 531, 216, 787, 482, 489;
    0, 0, 257, 689, 939, 524, 626, 114, 144;
    0, 0, 0, 25, 686, 849, 238, 683, 557;
    0, 0, 0, 0, 528, 552, 260, 484, 388;
    0, 0, 0, 0, 0, 958, 811, 321, 378;
    0, 0, 0, 0, 0, 0, 520, 74, 663;
    0, 0, 0, 0, 0, 0, 0, 150, 527;
    0, 0, 0, 0, 0, 0, 0, 0, 155]

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch24
