/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch16
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch16
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch16

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower16 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    58, 1, 0, 0, 0, 0, 0, 0, 0;
    573, 976, 1, 0, 0, 0, 0, 0, 0;
    248, 406, 439, 1, 0, 0, 0, 0, 0;
    100, 829, 348, 286, 1, 0, 0, 0, 0;
    705, 255, 207, 864, 911, 1, 0, 0, 0;
    968, 808, 0, 414, 20, 1006, 1, 0, 0;
    937, 810, 964, 952, 413, 347, 736, 1, 0;
    682, 385, 904, 789, 937, 205, 784, 923, 1]

private def firstUpper16 : Matrix (Fin 9) (Fin 9) F :=
  !![110, 221, 485, 840, 973, 690, 679, 31, 909;
    0, 212, 515, 393, 720, 852, 985, 510, 184;
    0, 0, 440, 643, 988, 86, 555, 213, 150;
    0, 0, 0, 396, 885, 948, 820, 855, 804;
    0, 0, 0, 0, 9, 469, 737, 72, 865;
    0, 0, 0, 0, 0, 116, 187, 719, 469;
    0, 0, 0, 0, 0, 0, 262, 438, 384;
    0, 0, 0, 0, 0, 0, 0, 541, 601;
    0, 0, 0, 0, 0, 0, 0, 0, 84]

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
    673, 1, 0, 0, 0, 0, 0, 0, 0;
    472, 426, 1, 0, 0, 0, 0, 0, 0;
    940, 52, 705, 1, 0, 0, 0, 0, 0;
    727, 360, 515, 780, 1, 0, 0, 0, 0;
    305, 675, 374, 249, 17, 1, 0, 0, 0;
    878, 120, 971, 196, 334, 510, 1, 0, 0;
    764, 46, 182, 84, 103, 889, 730, 1, 0;
    471, 502, 284, 857, 761, 781, 142, 332, 1]

private def secondUpper16 : Matrix (Fin 9) (Fin 9) F :=
  !![458, 961, 91, 359, 66, 607, 7, 828, 453;
    0, 938, 699, 225, 628, 646, 341, 14, 287;
    0, 0, 335, 887, 980, 377, 693, 903, 264;
    0, 0, 0, 954, 16, 585, 217, 320, 248;
    0, 0, 0, 0, 426, 743, 990, 123, 500;
    0, 0, 0, 0, 0, 138, 651, 700, 912;
    0, 0, 0, 0, 0, 0, 500, 840, 399;
    0, 0, 0, 0, 0, 0, 0, 27, 184;
    0, 0, 0, 0, 0, 0, 0, 0, 585]

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
    12, 1, 0, 0, 0, 0, 0, 0, 0;
    967, 756, 1, 0, 0, 0, 0, 0, 0;
    1008, 147, 732, 1, 0, 0, 0, 0, 0;
    149, 371, 327, 191, 1, 0, 0, 0, 0;
    678, 353, 628, 487, 782, 1, 0, 0, 0;
    348, 48, 388, 631, 179, 965, 1, 0, 0;
    706, 174, 655, 503, 592, 753, 823, 1, 0;
    848, 125, 333, 62, 759, 547, 999, 876, 1]

private def firstUpper17 : Matrix (Fin 9) (Fin 9) F :=
  !![385, 606, 819, 122, 307, 534, 343, 643, 152;
    0, 372, 280, 46, 594, 265, 834, 469, 668;
    0, 0, 244, 952, 858, 675, 767, 548, 55;
    0, 0, 0, 583, 802, 269, 372, 330, 381;
    0, 0, 0, 0, 919, 220, 700, 249, 69;
    0, 0, 0, 0, 0, 171, 330, 107, 479;
    0, 0, 0, 0, 0, 0, 132, 827, 697;
    0, 0, 0, 0, 0, 0, 0, 664, 194;
    0, 0, 0, 0, 0, 0, 0, 0, 509]

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
    1007, 1, 0, 0, 0, 0, 0, 0, 0;
    96, 814, 1, 0, 0, 0, 0, 0, 0;
    746, 286, 597, 1, 0, 0, 0, 0, 0;
    595, 25, 15, 704, 1, 0, 0, 0, 0;
    523, 705, 756, 434, 59, 1, 0, 0, 0;
    497, 421, 280, 463, 354, 377, 1, 0, 0;
    840, 821, 671, 811, 586, 738, 545, 1, 0;
    984, 120, 409, 332, 99, 425, 4, 607, 1]

private def secondUpper17 : Matrix (Fin 9) (Fin 9) F :=
  !![666, 114, 21, 706, 873, 258, 84, 481, 85;
    0, 809, 60, 904, 979, 126, 73, 66, 644;
    0, 0, 545, 875, 274, 805, 483, 172, 609;
    0, 0, 0, 883, 423, 276, 397, 479, 739;
    0, 0, 0, 0, 268, 392, 475, 675, 332;
    0, 0, 0, 0, 0, 610, 55, 783, 311;
    0, 0, 0, 0, 0, 0, 239, 139, 306;
    0, 0, 0, 0, 0, 0, 0, 870, 534;
    0, 0, 0, 0, 0, 0, 0, 0, 136]

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
    449, 1, 0, 0, 0, 0, 0, 0, 0;
    500, 160, 1, 0, 0, 0, 0, 0, 0;
    993, 263, 844, 1, 0, 0, 0, 0, 0;
    726, 299, 63, 503, 1, 0, 0, 0, 0;
    541, 610, 1002, 273, 511, 1, 0, 0, 0;
    42, 432, 173, 764, 273, 279, 1, 0, 0;
    168, 618, 323, 405, 588, 545, 38, 1, 0;
    624, 387, 620, 154, 561, 333, 740, 572, 1]

private def firstUpper18 : Matrix (Fin 9) (Fin 9) F :=
  !![945, 538, 706, 79, 259, 602, 229, 560, 234;
    0, 322, 169, 589, 890, 990, 579, 216, 534;
    0, 0, 413, 998, 396, 823, 96, 632, 723;
    0, 0, 0, 247, 86, 777, 943, 382, 342;
    0, 0, 0, 0, 32, 166, 469, 509, 284;
    0, 0, 0, 0, 0, 664, 280, 236, 82;
    0, 0, 0, 0, 0, 0, 877, 210, 435;
    0, 0, 0, 0, 0, 0, 0, 509, 241;
    0, 0, 0, 0, 0, 0, 0, 0, 702]

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
    293, 1, 0, 0, 0, 0, 0, 0, 0;
    18, 21, 1, 0, 0, 0, 0, 0, 0;
    434, 424, 659, 1, 0, 0, 0, 0, 0;
    391, 407, 764, 623, 1, 0, 0, 0, 0;
    880, 298, 295, 115, 408, 1, 0, 0, 0;
    915, 554, 885, 445, 920, 632, 1, 0, 0;
    681, 500, 433, 796, 33, 696, 395, 1, 0;
    983, 877, 870, 647, 950, 537, 632, 891, 1]

private def secondUpper18 : Matrix (Fin 9) (Fin 9) F :=
  !![43, 269, 577, 590, 685, 583, 500, 804, 29;
    0, 618, 788, 414, 223, 578, 287, 949, 239;
    0, 0, 369, 398, 6, 694, 499, 289, 867;
    0, 0, 0, 633, 946, 777, 957, 88, 428;
    0, 0, 0, 0, 687, 113, 659, 827, 139;
    0, 0, 0, 0, 0, 213, 829, 411, 381;
    0, 0, 0, 0, 0, 0, 236, 646, 119;
    0, 0, 0, 0, 0, 0, 0, 902, 509;
    0, 0, 0, 0, 0, 0, 0, 0, 657]

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
    241, 1, 0, 0, 0, 0, 0, 0, 0;
    244, 785, 1, 0, 0, 0, 0, 0, 0;
    812, 637, 157, 1, 0, 0, 0, 0, 0;
    984, 566, 36, 637, 1, 0, 0, 0, 0;
    536, 297, 222, 887, 712, 1, 0, 0, 0;
    77, 424, 92, 705, 159, 340, 1, 0, 0;
    494, 131, 826, 893, 152, 967, 268, 1, 0;
    845, 880, 238, 877, 9, 864, 756, 89, 1]

private def firstUpper19 : Matrix (Fin 9) (Fin 9) F :=
  !![648, 411, 648, 259, 183, 245, 477, 864, 301;
    0, 935, 714, 466, 46, 829, 954, 361, 650;
    0, 0, 593, 559, 224, 56, 113, 574, 337;
    0, 0, 0, 384, 862, 812, 332, 57, 729;
    0, 0, 0, 0, 877, 866, 809, 757, 217;
    0, 0, 0, 0, 0, 737, 932, 920, 452;
    0, 0, 0, 0, 0, 0, 252, 587, 70;
    0, 0, 0, 0, 0, 0, 0, 637, 764;
    0, 0, 0, 0, 0, 0, 0, 0, 295]

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
    908, 1, 0, 0, 0, 0, 0, 0, 0;
    341, 303, 1, 0, 0, 0, 0, 0, 0;
    610, 734, 299, 1, 0, 0, 0, 0, 0;
    871, 710, 119, 253, 1, 0, 0, 0, 0;
    337, 530, 436, 359, 127, 1, 0, 0, 0;
    814, 668, 104, 40, 373, 992, 1, 0, 0;
    726, 507, 47, 813, 702, 71, 954, 1, 0;
    443, 95, 18, 954, 914, 370, 131, 66, 1]

private def secondUpper19 : Matrix (Fin 9) (Fin 9) F :=
  !![907, 219, 680, 64, 595, 806, 72, 584, 778;
    0, 16, 555, 737, 317, 20, 85, 184, 419;
    0, 0, 306, 792, 993, 870, 821, 746, 66;
    0, 0, 0, 471, 450, 417, 411, 614, 41;
    0, 0, 0, 0, 701, 445, 921, 778, 137;
    0, 0, 0, 0, 0, 110, 101, 282, 518;
    0, 0, 0, 0, 0, 0, 313, 645, 393;
    0, 0, 0, 0, 0, 0, 0, 404, 273;
    0, 0, 0, 0, 0, 0, 0, 0, 303]

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
    916, 1, 0, 0, 0, 0, 0, 0, 0;
    790, 948, 1, 0, 0, 0, 0, 0, 0;
    597, 327, 639, 1, 0, 0, 0, 0, 0;
    297, 367, 830, 197, 1, 0, 0, 0, 0;
    214, 29, 739, 750, 897, 1, 0, 0, 0;
    878, 465, 627, 402, 401, 59, 1, 0, 0;
    316, 814, 948, 102, 505, 337, 630, 1, 0;
    178, 971, 744, 893, 734, 995, 180, 600, 1]

private def firstUpper20 : Matrix (Fin 9) (Fin 9) F :=
  !![628, 683, 732, 184, 60, 396, 894, 512, 176;
    0, 177, 532, 613, 475, 475, 665, 852, 528;
    0, 0, 231, 444, 971, 353, 378, 659, 27;
    0, 0, 0, 75, 847, 809, 234, 694, 515;
    0, 0, 0, 0, 773, 703, 511, 710, 757;
    0, 0, 0, 0, 0, 961, 440, 476, 678;
    0, 0, 0, 0, 0, 0, 947, 825, 984;
    0, 0, 0, 0, 0, 0, 0, 67, 571;
    0, 0, 0, 0, 0, 0, 0, 0, 52]

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
    335, 1, 0, 0, 0, 0, 0, 0, 0;
    177, 52, 1, 0, 0, 0, 0, 0, 0;
    600, 900, 98, 1, 0, 0, 0, 0, 0;
    105, 71, 720, 941, 1, 0, 0, 0, 0;
    41, 222, 764, 455, 952, 1, 0, 0, 0;
    919, 185, 421, 820, 21, 327, 1, 0, 0;
    174, 215, 227, 165, 887, 533, 144, 1, 0;
    22, 726, 468, 625, 483, 305, 326, 635, 1]

private def secondUpper20 : Matrix (Fin 9) (Fin 9) F :=
  !![242, 163, 780, 1004, 692, 980, 944, 577, 389;
    0, 106, 90, 311, 190, 605, 847, 83, 150;
    0, 0, 728, 296, 40, 596, 891, 526, 945;
    0, 0, 0, 617, 361, 317, 711, 863, 971;
    0, 0, 0, 0, 720, 883, 449, 837, 440;
    0, 0, 0, 0, 0, 156, 605, 391, 373;
    0, 0, 0, 0, 0, 0, 175, 297, 657;
    0, 0, 0, 0, 0, 0, 0, 144, 763;
    0, 0, 0, 0, 0, 0, 0, 0, 261]

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
    654, 1, 0, 0, 0, 0, 0, 0, 0;
    801, 301, 1, 0, 0, 0, 0, 0, 0;
    874, 960, 75, 1, 0, 0, 0, 0, 0;
    104, 362, 756, 540, 1, 0, 0, 0, 0;
    504, 517, 475, 439, 707, 1, 0, 0, 0;
    8, 624, 177, 162, 65, 507, 1, 0, 0;
    695, 1004, 254, 45, 173, 322, 670, 1, 0;
    285, 606, 970, 883, 762, 251, 78, 286, 1]

private def firstUpper21 : Matrix (Fin 9) (Fin 9) F :=
  !![992, 262, 495, 682, 895, 668, 94, 144, 365;
    0, 439, 419, 461, 931, 532, 239, 906, 428;
    0, 0, 550, 699, 767, 406, 108, 275, 484;
    0, 0, 0, 750, 38, 312, 515, 719, 102;
    0, 0, 0, 0, 961, 577, 650, 986, 618;
    0, 0, 0, 0, 0, 814, 744, 102, 84;
    0, 0, 0, 0, 0, 0, 352, 105, 416;
    0, 0, 0, 0, 0, 0, 0, 45, 946;
    0, 0, 0, 0, 0, 0, 0, 0, 410]

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
    961, 1, 0, 0, 0, 0, 0, 0, 0;
    780, 392, 1, 0, 0, 0, 0, 0, 0;
    69, 835, 49, 1, 0, 0, 0, 0, 0;
    176, 267, 294, 338, 1, 0, 0, 0, 0;
    308, 625, 403, 630, 640, 1, 0, 0, 0;
    59, 392, 238, 908, 223, 740, 1, 0, 0;
    306, 35, 873, 120, 218, 399, 704, 1, 0;
    385, 454, 886, 35, 524, 120, 833, 221, 1]

private def secondUpper21 : Matrix (Fin 9) (Fin 9) F :=
  !![643, 335, 457, 781, 976, 152, 103, 442, 903;
    0, 193, 1007, 666, 466, 740, 65, 263, 971;
    0, 0, 1003, 137, 464, 410, 152, 0, 627;
    0, 0, 0, 861, 176, 588, 140, 17, 710;
    0, 0, 0, 0, 527, 705, 267, 324, 29;
    0, 0, 0, 0, 0, 406, 334, 472, 731;
    0, 0, 0, 0, 0, 0, 169, 914, 917;
    0, 0, 0, 0, 0, 0, 0, 816, 12;
    0, 0, 0, 0, 0, 0, 0, 0, 707]

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
    975, 1, 0, 0, 0, 0, 0, 0, 0;
    827, 559, 1, 0, 0, 0, 0, 0, 0;
    47, 577, 191, 1, 0, 0, 0, 0, 0;
    607, 489, 615, 699, 1, 0, 0, 0, 0;
    975, 502, 497, 341, 822, 1, 0, 0, 0;
    596, 26, 334, 255, 531, 231, 1, 0, 0;
    187, 459, 245, 518, 227, 255, 768, 1, 0;
    999, 165, 315, 836, 185, 466, 275, 824, 1]

private def firstUpper22 : Matrix (Fin 9) (Fin 9) F :=
  !![328, 752, 42, 758, 616, 270, 310, 752, 1001;
    0, 647, 903, 972, 34, 248, 846, 318, 978;
    0, 0, 806, 418, 104, 767, 926, 424, 705;
    0, 0, 0, 338, 10, 545, 79, 22, 801;
    0, 0, 0, 0, 336, 429, 914, 57, 561;
    0, 0, 0, 0, 0, 865, 107, 958, 957;
    0, 0, 0, 0, 0, 0, 190, 989, 601;
    0, 0, 0, 0, 0, 0, 0, 895, 911;
    0, 0, 0, 0, 0, 0, 0, 0, 269]

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
    417, 1, 0, 0, 0, 0, 0, 0, 0;
    576, 862, 1, 0, 0, 0, 0, 0, 0;
    463, 992, 870, 1, 0, 0, 0, 0, 0;
    863, 324, 97, 307, 1, 0, 0, 0, 0;
    749, 882, 422, 670, 62, 1, 0, 0, 0;
    44, 999, 742, 832, 891, 419, 1, 0, 0;
    516, 159, 823, 244, 179, 550, 41, 1, 0;
    101, 817, 602, 783, 812, 541, 822, 673, 1]

private def secondUpper22 : Matrix (Fin 9) (Fin 9) F :=
  !![939, 56, 904, 793, 614, 11, 571, 53, 590;
    0, 159, 882, 696, 527, 607, 413, 72, 407;
    0, 0, 944, 904, 97, 613, 912, 189, 458;
    0, 0, 0, 997, 332, 760, 177, 92, 369;
    0, 0, 0, 0, 993, 612, 15, 632, 716;
    0, 0, 0, 0, 0, 219, 222, 292, 479;
    0, 0, 0, 0, 0, 0, 235, 818, 260;
    0, 0, 0, 0, 0, 0, 0, 498, 897;
    0, 0, 0, 0, 0, 0, 0, 0, 287]

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
    128, 1, 0, 0, 0, 0, 0, 0, 0;
    256, 850, 1, 0, 0, 0, 0, 0, 0;
    819, 12, 763, 1, 0, 0, 0, 0, 0;
    485, 265, 569, 607, 1, 0, 0, 0, 0;
    796, 344, 341, 885, 906, 1, 0, 0, 0;
    770, 275, 723, 19, 474, 18, 1, 0, 0;
    950, 849, 392, 522, 348, 380, 251, 1, 0;
    895, 853, 638, 945, 992, 452, 999, 797, 1]

private def firstUpper23 : Matrix (Fin 9) (Fin 9) F :=
  !![893, 49, 938, 843, 1000, 698, 965, 979, 791;
    0, 472, 55, 117, 772, 144, 788, 559, 42;
    0, 0, 485, 372, 213, 347, 306, 136, 194;
    0, 0, 0, 206, 983, 703, 895, 1004, 341;
    0, 0, 0, 0, 836, 305, 29, 217, 84;
    0, 0, 0, 0, 0, 828, 573, 509, 678;
    0, 0, 0, 0, 0, 0, 692, 265, 207;
    0, 0, 0, 0, 0, 0, 0, 253, 376;
    0, 0, 0, 0, 0, 0, 0, 0, 141]

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
    428, 1, 0, 0, 0, 0, 0, 0, 0;
    634, 208, 1, 0, 0, 0, 0, 0, 0;
    202, 572, 1006, 1, 0, 0, 0, 0, 0;
    307, 11, 342, 390, 1, 0, 0, 0, 0;
    630, 170, 534, 848, 853, 1, 0, 0, 0;
    991, 253, 283, 715, 361, 595, 1, 0, 0;
    3, 562, 230, 130, 284, 561, 972, 1, 0;
    822, 763, 542, 350, 407, 68, 709, 179, 1]

private def secondUpper23 : Matrix (Fin 9) (Fin 9) F :=
  !![961, 622, 307, 1002, 562, 612, 134, 583, 829;
    0, 850, 831, 27, 235, 91, 362, 454, 746;
    0, 0, 597, 653, 707, 444, 144, 525, 587;
    0, 0, 0, 197, 292, 588, 327, 614, 469;
    0, 0, 0, 0, 680, 263, 906, 694, 264;
    0, 0, 0, 0, 0, 364, 363, 766, 790;
    0, 0, 0, 0, 0, 0, 146, 318, 724;
    0, 0, 0, 0, 0, 0, 0, 116, 854;
    0, 0, 0, 0, 0, 0, 0, 0, 118]

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch16
