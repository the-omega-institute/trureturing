/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch8
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch8
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch8

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower8 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    696, 1, 0, 0, 0, 0, 0, 0, 0;
    431, 981, 1, 0, 0, 0, 0, 0, 0;
    864, 132, 150, 1, 0, 0, 0, 0, 0;
    415, 770, 192, 966, 1, 0, 0, 0, 0;
    695, 745, 934, 190, 81, 1, 0, 0, 0;
    244, 478, 750, 698, 386, 748, 1, 0, 0;
    126, 39, 448, 725, 753, 434, 398, 1, 0;
    950, 739, 529, 70, 233, 405, 338, 967, 1]

private def firstUpper8 : Matrix (Fin 9) (Fin 9) F :=
  !![460, 927, 274, 322, 713, 318, 357, 909, 886;
    0, 851, 200, 483, 224, 644, 1002, 931, 147;
    0, 0, 74, 825, 918, 312, 873, 152, 1;
    0, 0, 0, 584, 750, 441, 496, 986, 953;
    0, 0, 0, 0, 257, 131, 558, 717, 571;
    0, 0, 0, 0, 0, 319, 737, 199, 572;
    0, 0, 0, 0, 0, 0, 124, 873, 153;
    0, 0, 0, 0, 0, 0, 0, 234, 217;
    0, 0, 0, 0, 0, 0, 0, 0, 210]

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
    659, 1, 0, 0, 0, 0, 0, 0, 0;
    3, 831, 1, 0, 0, 0, 0, 0, 0;
    92, 136, 636, 1, 0, 0, 0, 0, 0;
    42, 163, 20, 526, 1, 0, 0, 0, 0;
    342, 441, 837, 814, 425, 1, 0, 0, 0;
    549, 23, 545, 475, 39, 665, 1, 0, 0;
    315, 939, 183, 548, 34, 457, 808, 1, 0;
    251, 132, 642, 482, 764, 603, 364, 584, 1]

private def secondUpper8 : Matrix (Fin 9) (Fin 9) F :=
  !![358, 465, 633, 195, 112, 291, 671, 909, 98;
    0, 584, 782, 235, 902, 942, 4, 258, 298;
    0, 0, 642, 843, 47, 594, 267, 415, 667;
    0, 0, 0, 321, 647, 458, 37, 502, 474;
    0, 0, 0, 0, 584, 134, 878, 526, 194;
    0, 0, 0, 0, 0, 202, 431, 1000, 737;
    0, 0, 0, 0, 0, 0, 180, 273, 776;
    0, 0, 0, 0, 0, 0, 0, 677, 172;
    0, 0, 0, 0, 0, 0, 0, 0, 351]

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
    46, 1, 0, 0, 0, 0, 0, 0, 0;
    405, 169, 1, 0, 0, 0, 0, 0, 0;
    873, 9, 655, 1, 0, 0, 0, 0, 0;
    356, 380, 220, 278, 1, 0, 0, 0, 0;
    465, 955, 685, 293, 444, 1, 0, 0, 0;
    99, 290, 920, 780, 109, 908, 1, 0, 0;
    262, 685, 812, 111, 461, 189, 816, 1, 0;
    966, 447, 303, 999, 437, 305, 603, 673, 1]

private def firstUpper9 : Matrix (Fin 9) (Fin 9) F :=
  !![222, 793, 887, 184, 464, 77, 613, 229, 29;
    0, 631, 203, 243, 790, 338, 589, 586, 421;
    0, 0, 715, 862, 387, 651, 209, 617, 469;
    0, 0, 0, 598, 952, 671, 322, 402, 796;
    0, 0, 0, 0, 536, 550, 707, 26, 324;
    0, 0, 0, 0, 0, 203, 866, 152, 376;
    0, 0, 0, 0, 0, 0, 725, 6, 229;
    0, 0, 0, 0, 0, 0, 0, 830, 177;
    0, 0, 0, 0, 0, 0, 0, 0, 215]

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
    538, 1, 0, 0, 0, 0, 0, 0, 0;
    809, 662, 1, 0, 0, 0, 0, 0, 0;
    851, 702, 446, 1, 0, 0, 0, 0, 0;
    913, 540, 43, 206, 1, 0, 0, 0, 0;
    470, 59, 650, 434, 692, 1, 0, 0, 0;
    279, 549, 340, 826, 20, 943, 1, 0, 0;
    125, 430, 253, 598, 407, 48, 733, 1, 0;
    435, 439, 867, 707, 213, 50, 976, 369, 1]

private def secondUpper9 : Matrix (Fin 9) (Fin 9) F :=
  !![237, 113, 192, 469, 872, 126, 595, 410, 438;
    0, 531, 267, 563, 994, 668, 278, 412, 199;
    0, 0, 626, 1001, 638, 876, 459, 643, 883;
    0, 0, 0, 817, 652, 675, 495, 633, 928;
    0, 0, 0, 0, 131, 169, 304, 687, 765;
    0, 0, 0, 0, 0, 112, 841, 652, 18;
    0, 0, 0, 0, 0, 0, 640, 463, 810;
    0, 0, 0, 0, 0, 0, 0, 843, 847;
    0, 0, 0, 0, 0, 0, 0, 0, 299]

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
    553, 1, 0, 0, 0, 0, 0, 0, 0;
    382, 685, 1, 0, 0, 0, 0, 0, 0;
    618, 682, 161, 1, 0, 0, 0, 0, 0;
    802, 188, 554, 963, 1, 0, 0, 0, 0;
    883, 48, 244, 48, 746, 1, 0, 0, 0;
    208, 130, 857, 121, 244, 215, 1, 0, 0;
    229, 372, 49, 951, 54, 559, 791, 1, 0;
    692, 17, 957, 178, 751, 269, 389, 502, 1]

private def firstUpper10 : Matrix (Fin 9) (Fin 9) F :=
  !![289, 287, 446, 965, 741, 833, 838, 732, 220;
    0, 547, 231, 663, 89, 366, 724, 732, 435;
    0, 0, 346, 937, 700, 382, 716, 830, 199;
    0, 0, 0, 88, 359, 556, 828, 382, 485;
    0, 0, 0, 0, 923, 38, 28, 85, 868;
    0, 0, 0, 0, 0, 515, 295, 266, 199;
    0, 0, 0, 0, 0, 0, 500, 38, 377;
    0, 0, 0, 0, 0, 0, 0, 164, 554;
    0, 0, 0, 0, 0, 0, 0, 0, 86]

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
    381, 1, 0, 0, 0, 0, 0, 0, 0;
    701, 34, 1, 0, 0, 0, 0, 0, 0;
    915, 560, 449, 1, 0, 0, 0, 0, 0;
    542, 225, 494, 355, 1, 0, 0, 0, 0;
    815, 720, 994, 283, 717, 1, 0, 0, 0;
    828, 685, 192, 423, 703, 502, 1, 0, 0;
    767, 363, 403, 423, 459, 851, 6, 1, 0;
    699, 404, 180, 230, 111, 843, 102, 928, 1]

private def secondUpper10 : Matrix (Fin 9) (Fin 9) F :=
  !![985, 379, 236, 21, 891, 720, 421, 253, 925;
    0, 733, 558, 618, 770, 30, 28, 381, 731;
    0, 0, 258, 969, 692, 1000, 55, 293, 536;
    0, 0, 0, 550, 784, 528, 911, 664, 962;
    0, 0, 0, 0, 502, 929, 551, 678, 158;
    0, 0, 0, 0, 0, 476, 52, 513, 469;
    0, 0, 0, 0, 0, 0, 959, 254, 214;
    0, 0, 0, 0, 0, 0, 0, 846, 680;
    0, 0, 0, 0, 0, 0, 0, 0, 10]

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
    168, 1, 0, 0, 0, 0, 0, 0, 0;
    846, 979, 1, 0, 0, 0, 0, 0, 0;
    221, 327, 764, 1, 0, 0, 0, 0, 0;
    295, 693, 907, 105, 1, 0, 0, 0, 0;
    302, 474, 813, 896, 926, 1, 0, 0, 0;
    413, 499, 768, 236, 804, 513, 1, 0, 0;
    692, 177, 232, 838, 566, 954, 942, 1, 0;
    490, 148, 512, 283, 782, 653, 642, 124, 1]

private def firstUpper11 : Matrix (Fin 9) (Fin 9) F :=
  !![859, 6, 256, 917, 288, 148, 804, 828, 802;
    0, 602, 740, 219, 446, 883, 835, 783, 121;
    0, 0, 497, 263, 951, 666, 751, 169, 869;
    0, 0, 0, 462, 778, 341, 625, 222, 582;
    0, 0, 0, 0, 186, 818, 568, 549, 249;
    0, 0, 0, 0, 0, 895, 942, 886, 156;
    0, 0, 0, 0, 0, 0, 807, 210, 687;
    0, 0, 0, 0, 0, 0, 0, 25, 731;
    0, 0, 0, 0, 0, 0, 0, 0, 318]

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
    679, 1, 0, 0, 0, 0, 0, 0, 0;
    704, 100, 1, 0, 0, 0, 0, 0, 0;
    678, 952, 364, 1, 0, 0, 0, 0, 0;
    133, 463, 350, 876, 1, 0, 0, 0, 0;
    906, 530, 829, 868, 741, 1, 0, 0, 0;
    366, 909, 468, 929, 607, 703, 1, 0, 0;
    799, 515, 394, 390, 858, 651, 404, 1, 0;
    602, 836, 107, 943, 555, 793, 868, 782, 1]

private def secondUpper11 : Matrix (Fin 9) (Fin 9) F :=
  !![826, 584, 43, 358, 390, 712, 787, 969, 388;
    0, 602, 425, 994, 955, 385, 89, 562, 557;
    0, 0, 12, 317, 401, 569, 109, 340, 792;
    0, 0, 0, 662, 708, 258, 861, 270, 482;
    0, 0, 0, 0, 131, 827, 350, 465, 627;
    0, 0, 0, 0, 0, 822, 554, 293, 793;
    0, 0, 0, 0, 0, 0, 700, 879, 717;
    0, 0, 0, 0, 0, 0, 0, 506, 720;
    0, 0, 0, 0, 0, 0, 0, 0, 238]

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
    969, 1, 0, 0, 0, 0, 0, 0, 0;
    466, 1, 1, 0, 0, 0, 0, 0, 0;
    862, 543, 387, 1, 0, 0, 0, 0, 0;
    1003, 313, 980, 994, 1, 0, 0, 0, 0;
    148, 235, 625, 65, 450, 1, 0, 0, 0;
    512, 779, 585, 434, 513, 491, 1, 0, 0;
    504, 924, 550, 928, 960, 224, 387, 1, 0;
    439, 122, 43, 516, 786, 984, 532, 171, 1]

private def firstUpper12 : Matrix (Fin 9) (Fin 9) F :=
  !![176, 273, 960, 554, 857, 234, 31, 205, 99;
    0, 22, 341, 225, 669, 529, 833, 934, 876;
    0, 0, 41, 3, 620, 42, 773, 402, 43;
    0, 0, 0, 474, 442, 926, 979, 330, 492;
    0, 0, 0, 0, 307, 116, 204, 225, 481;
    0, 0, 0, 0, 0, 59, 186, 498, 827;
    0, 0, 0, 0, 0, 0, 509, 349, 892;
    0, 0, 0, 0, 0, 0, 0, 193, 366;
    0, 0, 0, 0, 0, 0, 0, 0, 415]

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
    828, 1, 0, 0, 0, 0, 0, 0, 0;
    465, 141, 1, 0, 0, 0, 0, 0, 0;
    868, 509, 77, 1, 0, 0, 0, 0, 0;
    148, 377, 746, 851, 1, 0, 0, 0, 0;
    591, 903, 540, 512, 340, 1, 0, 0, 0;
    703, 736, 383, 450, 279, 64, 1, 0, 0;
    680, 795, 186, 251, 230, 113, 71, 1, 0;
    471, 858, 900, 132, 170, 576, 762, 44, 1]

private def secondUpper12 : Matrix (Fin 9) (Fin 9) F :=
  !![787, 4, 377, 992, 520, 518, 737, 486, 355;
    0, 925, 917, 213, 978, 171, 811, 989, 631;
    0, 0, 871, 158, 773, 20, 938, 830, 861;
    0, 0, 0, 112, 730, 220, 517, 958, 576;
    0, 0, 0, 0, 457, 647, 987, 829, 871;
    0, 0, 0, 0, 0, 193, 192, 278, 1006;
    0, 0, 0, 0, 0, 0, 71, 21, 5;
    0, 0, 0, 0, 0, 0, 0, 365, 345;
    0, 0, 0, 0, 0, 0, 0, 0, 912]

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
    417, 1, 0, 0, 0, 0, 0, 0, 0;
    814, 940, 1, 0, 0, 0, 0, 0, 0;
    587, 147, 623, 1, 0, 0, 0, 0, 0;
    479, 78, 372, 912, 1, 0, 0, 0, 0;
    441, 196, 96, 989, 566, 1, 0, 0, 0;
    553, 749, 793, 803, 1005, 124, 1, 0, 0;
    860, 245, 914, 669, 617, 593, 694, 1, 0;
    554, 98, 190, 571, 696, 769, 302, 770, 1]

private def firstUpper13 : Matrix (Fin 9) (Fin 9) F :=
  !![429, 38, 773, 780, 111, 566, 206, 429, 85;
    0, 613, 859, 439, 779, 180, 503, 856, 539;
    0, 0, 785, 208, 831, 79, 354, 296, 101;
    0, 0, 0, 408, 156, 6, 572, 867, 716;
    0, 0, 0, 0, 692, 426, 61, 33, 798;
    0, 0, 0, 0, 0, 728, 358, 941, 65;
    0, 0, 0, 0, 0, 0, 797, 603, 200;
    0, 0, 0, 0, 0, 0, 0, 3, 566;
    0, 0, 0, 0, 0, 0, 0, 0, 769]

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
    419, 1, 0, 0, 0, 0, 0, 0, 0;
    186, 518, 1, 0, 0, 0, 0, 0, 0;
    947, 645, 995, 1, 0, 0, 0, 0, 0;
    64, 765, 552, 996, 1, 0, 0, 0, 0;
    477, 411, 248, 52, 128, 1, 0, 0, 0;
    114, 444, 402, 533, 894, 317, 1, 0, 0;
    855, 49, 438, 287, 20, 118, 497, 1, 0;
    818, 622, 499, 16, 380, 644, 215, 405, 1]

private def secondUpper13 : Matrix (Fin 9) (Fin 9) F :=
  !![841, 128, 857, 967, 278, 445, 62, 745, 594;
    0, 160, 441, 237, 205, 306, 896, 782, 1006;
    0, 0, 267, 518, 616, 260, 731, 51, 863;
    0, 0, 0, 677, 909, 634, 458, 508, 443;
    0, 0, 0, 0, 637, 285, 1001, 141, 396;
    0, 0, 0, 0, 0, 686, 120, 877, 205;
    0, 0, 0, 0, 0, 0, 201, 879, 9;
    0, 0, 0, 0, 0, 0, 0, 220, 772;
    0, 0, 0, 0, 0, 0, 0, 0, 484]

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
    802, 1, 0, 0, 0, 0, 0, 0, 0;
    272, 228, 1, 0, 0, 0, 0, 0, 0;
    234, 953, 484, 1, 0, 0, 0, 0, 0;
    797, 777, 741, 530, 1, 0, 0, 0, 0;
    402, 715, 443, 845, 7, 1, 0, 0, 0;
    225, 834, 164, 677, 651, 571, 1, 0, 0;
    133, 351, 567, 510, 308, 380, 168, 1, 0;
    690, 836, 933, 285, 539, 253, 689, 651, 1]

private def firstUpper14 : Matrix (Fin 9) (Fin 9) F :=
  !![966, 143, 492, 995, 35, 578, 316, 360, 495;
    0, 780, 856, 459, 378, 297, 660, 598, 484;
    0, 0, 815, 735, 850, 15, 633, 844, 430;
    0, 0, 0, 585, 350, 983, 110, 343, 593;
    0, 0, 0, 0, 383, 793, 73, 902, 626;
    0, 0, 0, 0, 0, 384, 34, 777, 177;
    0, 0, 0, 0, 0, 0, 31, 441, 629;
    0, 0, 0, 0, 0, 0, 0, 40, 236;
    0, 0, 0, 0, 0, 0, 0, 0, 126]

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
    434, 1, 0, 0, 0, 0, 0, 0, 0;
    260, 984, 1, 0, 0, 0, 0, 0, 0;
    387, 569, 582, 1, 0, 0, 0, 0, 0;
    575, 181, 687, 92, 1, 0, 0, 0, 0;
    734, 748, 711, 328, 693, 1, 0, 0, 0;
    712, 648, 611, 618, 927, 650, 1, 0, 0;
    478, 152, 333, 17, 223, 372, 362, 1, 0;
    314, 229, 851, 867, 308, 559, 471, 477, 1]

private def secondUpper14 : Matrix (Fin 9) (Fin 9) F :=
  !![103, 615, 862, 528, 99, 354, 293, 108, 460;
    0, 915, 143, 221, 617, 454, 805, 286, 70;
    0, 0, 290, 94, 474, 979, 399, 270, 438;
    0, 0, 0, 65, 903, 240, 925, 48, 239;
    0, 0, 0, 0, 23, 787, 188, 694, 901;
    0, 0, 0, 0, 0, 961, 284, 930, 439;
    0, 0, 0, 0, 0, 0, 480, 507, 138;
    0, 0, 0, 0, 0, 0, 0, 244, 161;
    0, 0, 0, 0, 0, 0, 0, 0, 734]

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
    656, 1, 0, 0, 0, 0, 0, 0, 0;
    700, 519, 1, 0, 0, 0, 0, 0, 0;
    909, 251, 93, 1, 0, 0, 0, 0, 0;
    204, 163, 634, 274, 1, 0, 0, 0, 0;
    607, 868, 126, 713, 639, 1, 0, 0, 0;
    987, 690, 511, 661, 231, 760, 1, 0, 0;
    722, 552, 269, 426, 949, 246, 380, 1, 0;
    215, 459, 242, 88, 724, 161, 269, 343, 1]

private def firstUpper15 : Matrix (Fin 9) (Fin 9) F :=
  !![584, 287, 40, 917, 714, 984, 944, 219, 670;
    0, 229, 147, 868, 293, 993, 108, 566, 331;
    0, 0, 16, 194, 110, 704, 631, 796, 911;
    0, 0, 0, 653, 206, 637, 825, 717, 810;
    0, 0, 0, 0, 786, 985, 82, 333, 514;
    0, 0, 0, 0, 0, 966, 289, 165, 303;
    0, 0, 0, 0, 0, 0, 652, 424, 747;
    0, 0, 0, 0, 0, 0, 0, 483, 42;
    0, 0, 0, 0, 0, 0, 0, 0, 740]

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
    397, 1, 0, 0, 0, 0, 0, 0, 0;
    72, 260, 1, 0, 0, 0, 0, 0, 0;
    773, 679, 940, 1, 0, 0, 0, 0, 0;
    591, 182, 289, 143, 1, 0, 0, 0, 0;
    595, 408, 600, 735, 551, 1, 0, 0, 0;
    34, 316, 634, 751, 772, 923, 1, 0, 0;
    396, 143, 198, 222, 72, 726, 746, 1, 0;
    730, 507, 518, 9, 169, 945, 155, 211, 1]

private def secondUpper15 : Matrix (Fin 9) (Fin 9) F :=
  !![233, 637, 588, 525, 200, 936, 820, 784, 685;
    0, 188, 805, 485, 812, 457, 213, 476, 412;
    0, 0, 996, 406, 659, 578, 690, 257, 940;
    0, 0, 0, 759, 889, 942, 936, 807, 963;
    0, 0, 0, 0, 172, 951, 911, 866, 573;
    0, 0, 0, 0, 0, 24, 510, 388, 869;
    0, 0, 0, 0, 0, 0, 288, 919, 531;
    0, 0, 0, 0, 0, 0, 0, 301, 730;
    0, 0, 0, 0, 0, 0, 0, 0, 956]

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch8
