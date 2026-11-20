/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch0
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch0
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 0 through 5. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_0 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 138, 1, 0, 0, 0, 0, 0, 0, 0, 99, 787, 1, 0, 0, 0, 0, 0, 0, 774, 613, 970, 1, 0, 0, 0, 0, 0, 804, 717, 453, 381, 1, 0, 0, 0, 0, 634, 291, 646, 433, 887, 1, 0, 0, 0, 758, 723, 883, 361, 933, 667, 1, 0, 0, 95, 922, 855, 889, 517, 587, 453, 1, 0, 764, 649, 384, 364, 232, 447, 764, 113, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_0 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[555, 69, 269, 383, 800, 974, 0, 559, 513, 0, 536, 588, 493, 327, 281, 450, 551, 810, 0, 0, 82, 744, 298, 821, 505, 422, 890, 0, 0, 0, 217, 418, 259, 131, 656, 29, 0, 0, 0, 0, 674, 696, 595, 468, 436, 0, 0, 0, 0, 0, 778, 503, 170, 919, 0, 0, 0, 0, 0, 0, 858, 105, 58, 0, 0, 0, 0, 0, 0, 0, 596, 195, 0, 0, 0, 0, 0, 0, 0, 0, 258] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_0 :
    (evaluatedRows (0 : F) 0).det = point (0 : F) 1 * quotientValue 0 0 := by
  apply det_of_factors lower0_0 upper0_0
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_0 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 775, 1, 0, 0, 0, 0, 0, 0, 0, 885, 13, 1, 0, 0, 0, 0, 0, 0, 223, 728, 28, 1, 0, 0, 0, 0, 0, 216, 657, 687, 453, 1, 0, 0, 0, 0, 592, 605, 536, 997, 875, 1, 0, 0, 0, 294, 243, 342, 547, 554, 903, 1, 0, 0, 146, 159, 193, 140, 251, 514, 385, 1, 0, 898, 1004, 376, 792, 442, 802, 488, 537, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_0 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[216, 442, 658, 59, 574, 37, 0, 0, 0, 0, 478, 981, 559, 865, 73, 450, 0, 974, 0, 0, 331, 903, 241, 162, 700, 35, 455, 0, 0, 0, 352, 590, 49, 905, 933, 884, 0, 0, 0, 0, 36, 122, 626, 900, 436, 0, 0, 0, 0, 0, 702, 100, 464, 97, 0, 0, 0, 0, 0, 0, 336, 939, 528, 0, 0, 0, 0, 0, 0, 0, 435, 944, 0, 0, 0, 0, 0, 0, 0, 0, 529] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_0 :
    (evaluatedRows (0 : F) 1).det = point (0 : F) 1 * quotientValue 1 0 := by
  apply det_of_factors lower1_0 upper1_0
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_1 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 983, 1, 0, 0, 0, 0, 0, 0, 0, 891, 658, 1, 0, 0, 0, 0, 0, 0, 239, 153, 680, 1, 0, 0, 0, 0, 0, 949, 601, 744, 993, 1, 0, 0, 0, 0, 23, 570, 723, 682, 966, 1, 0, 0, 0, 52, 981, 935, 235, 987, 16, 1, 0, 0, 414, 688, 202, 77, 709, 914, 107, 1, 0, 794, 212, 125, 83, 388, 741, 915, 178, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_1 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[205, 321, 533, 941, 765, 188, 0, 41, 468, 0, 737, 278, 51, 115, 384, 968, 57, 248, 0, 0, 31, 146, 467, 614, 276, 441, 3, 0, 0, 0, 921, 149, 271, 213, 5, 383, 0, 0, 0, 0, 504, 80, 4, 607, 943, 0, 0, 0, 0, 0, 346, 669, 377, 183, 0, 0, 0, 0, 0, 0, 553, 912, 584, 0, 0, 0, 0, 0, 0, 0, 838, 4, 0, 0, 0, 0, 0, 0, 0, 0, 429] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_1 :
    (evaluatedRows (1 : F) 0).det = point (1 : F) 1 * quotientValue 0 1 := by
  apply det_of_factors lower0_1 upper0_1
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_1 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 22, 1, 0, 0, 0, 0, 0, 0, 0, 876, 283, 1, 0, 0, 0, 0, 0, 0, 962, 198, 971, 1, 0, 0, 0, 0, 0, 206, 435, 766, 812, 1, 0, 0, 0, 0, 291, 542, 103, 953, 131, 1, 0, 0, 0, 965, 930, 652, 738, 688, 394, 1, 0, 0, 193, 812, 670, 147, 39, 813, 66, 1, 0, 570, 637, 936, 701, 138, 957, 929, 728, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_1 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[675, 737, 384, 29, 596, 854, 0, 0, 0, 0, 393, 170, 172, 410, 924, 968, 0, 188, 0, 0, 934, 945, 564, 454, 36, 821, 273, 0, 0, 0, 123, 65, 385, 405, 489, 253, 0, 0, 0, 0, 579, 874, 138, 414, 56, 0, 0, 0, 0, 0, 196, 988, 605, 709, 0, 0, 0, 0, 0, 0, 989, 287, 366, 0, 0, 0, 0, 0, 0, 0, 275, 474, 0, 0, 0, 0, 0, 0, 0, 0, 199] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_1 :
    (evaluatedRows (1 : F) 1).det = point (1 : F) 1 * quotientValue 1 1 := by
  apply det_of_factors lower1_1 upper1_1
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_2 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 147, 1, 0, 0, 0, 0, 0, 0, 0, 446, 273, 1, 0, 0, 0, 0, 0, 0, 473, 380, 30, 1, 0, 0, 0, 0, 0, 183, 341, 673, 992, 1, 0, 0, 0, 0, 886, 519, 604, 178, 852, 1, 0, 0, 0, 577, 764, 569, 129, 160, 808, 1, 0, 0, 567, 987, 188, 615, 275, 156, 818, 1, 0, 650, 204, 437, 965, 198, 741, 543, 309, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_2 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[423, 66, 99, 127, 632, 658, 0, 563, 95, 0, 496, 879, 590, 100, 43, 446, 986, 819, 0, 0, 111, 264, 206, 74, 236, 719, 419, 0, 0, 0, 399, 447, 741, 15, 246, 483, 0, 0, 0, 0, 80, 300, 172, 958, 404, 0, 0, 0, 0, 0, 703, 482, 607, 439, 0, 0, 0, 0, 0, 0, 615, 560, 986, 0, 0, 0, 0, 0, 0, 0, 236, 619, 0, 0, 0, 0, 0, 0, 0, 0, 953] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_2 :
    (evaluatedRows (2 : F) 0).det = point (2 : F) 1 * quotientValue 0 2 := by
  apply det_of_factors lower0_2 upper0_2
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_2 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 271, 1, 0, 0, 0, 0, 0, 0, 0, 26, 529, 1, 0, 0, 0, 0, 0, 0, 14, 986, 830, 1, 0, 0, 0, 0, 0, 255, 938, 641, 250, 1, 0, 0, 0, 0, 391, 229, 491, 349, 319, 1, 0, 0, 0, 192, 474, 175, 702, 577, 178, 1, 0, 0, 757, 285, 698, 140, 46, 33, 915, 1, 0, 608, 837, 751, 962, 90, 709, 808, 134, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_2 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[814, 665, 78, 330, 161, 25, 0, 0, 0, 0, 504, 348, 459, 941, 193, 446, 0, 658, 0, 0, 239, 891, 122, 734, 77, 351, 23, 0, 0, 0, 939, 361, 861, 834, 153, 1003, 0, 0, 0, 0, 955, 684, 893, 827, 937, 0, 0, 0, 0, 0, 215, 559, 697, 601, 0, 0, 0, 0, 0, 0, 178, 800, 313, 0, 0, 0, 0, 0, 0, 0, 955, 799, 0, 0, 0, 0, 0, 0, 0, 0, 124] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_2 :
    (evaluatedRows (2 : F) 1).det = point (2 : F) 1 * quotientValue 1 2 := by
  apply det_of_factors lower1_2 upper1_2
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_3 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 386, 1, 0, 0, 0, 0, 0, 0, 0, 303, 43, 1, 0, 0, 0, 0, 0, 0, 129, 293, 71, 1, 0, 0, 0, 0, 0, 621, 758, 108, 763, 1, 0, 0, 0, 0, 111, 671, 769, 850, 182, 1, 0, 0, 0, 382, 632, 665, 936, 445, 567, 1, 0, 0, 631, 967, 556, 440, 871, 197, 727, 1, 0, 914, 54, 631, 171, 944, 363, 458, 339, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_3 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[434, 866, 965, 811, 791, 876, 0, 950, 232, 0, 287, 970, 453, 391, 656, 59, 576, 116, 0, 0, 258, 365, 713, 933, 258, 305, 391, 0, 0, 0, 411, 734, 863, 719, 774, 793, 0, 0, 0, 0, 281, 767, 387, 505, 100, 0, 0, 0, 0, 0, 931, 812, 764, 425, 0, 0, 0, 0, 0, 0, 366, 494, 617, 0, 0, 0, 0, 0, 0, 0, 75, 598, 0, 0, 0, 0, 0, 0, 0, 0, 288] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_3 :
    (evaluatedRows (3 : F) 0).det = point (3 : F) 1 * quotientValue 0 3 := by
  apply det_of_factors lower0_3 upper0_3
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_3 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 141, 1, 0, 0, 0, 0, 0, 0, 0, 955, 404, 1, 0, 0, 0, 0, 0, 0, 996, 447, 326, 1, 0, 0, 0, 0, 0, 219, 477, 1, 811, 1, 0, 0, 0, 0, 200, 821, 945, 387, 823, 1, 0, 0, 0, 861, 575, 885, 98, 445, 316, 1, 0, 0, 437, 933, 1007, 547, 742, 22, 49, 1, 0, 956, 472, 839, 86, 473, 740, 858, 841, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_3 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[816, 217, 511, 148, 1001, 296, 0, 0, 0, 0, 257, 727, 21, 109, 410, 59, 0, 876, 0, 0, 646, 727, 841, 626, 148, 133, 255, 0, 0, 0, 38, 461, 928, 45, 986, 179, 0, 0, 0, 0, 44, 596, 825, 199, 294, 0, 0, 0, 0, 0, 339, 383, 839, 93, 0, 0, 0, 0, 0, 0, 718, 55, 314, 0, 0, 0, 0, 0, 0, 0, 252, 952, 0, 0, 0, 0, 0, 0, 0, 0, 399] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_3 :
    (evaluatedRows (3 : F) 1).det = point (3 : F) 1 * quotientValue 1 3 := by
  apply det_of_factors lower1_3 upper1_3
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_4 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 754, 1, 0, 0, 0, 0, 0, 0, 0, 60, 828, 1, 0, 0, 0, 0, 0, 0, 1, 143, 976, 1, 0, 0, 0, 0, 0, 545, 228, 70, 340, 1, 0, 0, 0, 0, 649, 106, 747, 562, 499, 1, 0, 0, 0, 954, 287, 318, 229, 981, 295, 1, 0, 0, 46, 542, 115, 440, 261, 282, 746, 1, 0, 824, 399, 982, 401, 94, 396, 134, 999, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_4 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[339, 11, 309, 180, 584, 115, 0, 60, 797, 0, 58, 832, 701, 277, 276, 949, 165, 541, 0, 0, 232, 600, 218, 738, 451, 925, 660, 0, 0, 0, 171, 93, 92, 256, 761, 396, 0, 0, 0, 0, 304, 184, 538, 810, 148, 0, 0, 0, 0, 0, 908, 626, 1008, 44, 0, 0, 0, 0, 0, 0, 538, 875, 658, 0, 0, 0, 0, 0, 0, 0, 318, 557, 0, 0, 0, 0, 0, 0, 0, 0, 561] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_4 :
    (evaluatedRows (4 : F) 0).det = point (4 : F) 1 * quotientValue 0 4 := by
  apply det_of_factors lower0_4 upper0_4
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_4 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 181, 1, 0, 0, 0, 0, 0, 0, 0, 729, 11, 1, 0, 0, 0, 0, 0, 0, 668, 200, 209, 1, 0, 0, 0, 0, 0, 820, 130, 963, 308, 1, 0, 0, 0, 0, 671, 11, 822, 134, 978, 1, 0, 0, 0, 593, 381, 868, 843, 640, 152, 1, 0, 0, 458, 132, 859, 981, 370, 1005, 493, 1, 0, 527, 1005, 231, 246, 957, 256, 891, 221, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_4 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[576, 71, 371, 741, 761, 75, 0, 0, 0, 0, 546, 182, 282, 172, 763, 949, 0, 115, 0, 0, 328, 105, 563, 559, 872, 894, 753, 0, 0, 0, 862, 277, 508, 273, 773, 506, 0, 0, 0, 0, 297, 25, 684, 905, 168, 0, 0, 0, 0, 0, 184, 896, 23, 165, 0, 0, 0, 0, 0, 0, 396, 610, 365, 0, 0, 0, 0, 0, 0, 0, 676, 122, 0, 0, 0, 0, 0, 0, 0, 0, 462] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_4 :
    (evaluatedRows (4 : F) 1).det = point (4 : F) 1 * quotientValue 1 4 := by
  apply det_of_factors lower1_4 upper1_4
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_5 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 614, 1, 0, 0, 0, 0, 0, 0, 0, 93, 913, 1, 0, 0, 0, 0, 0, 0, 415, 684, 469, 1, 0, 0, 0, 0, 0, 961, 775, 556, 221, 1, 0, 0, 0, 0, 479, 826, 436, 38, 350, 1, 0, 0, 0, 98, 575, 995, 843, 190, 697, 1, 0, 0, 615, 390, 255, 773, 983, 817, 613, 1, 0, 272, 164, 333, 463, 339, 580, 101, 19, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_5 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[387, 102, 177, 408, 494, 985, 0, 23, 402, 0, 940, 465, 364, 225, 208, 986, 4, 353, 0, 0, 345, 932, 557, 25, 417, 287, 538, 0, 0, 0, 174, 800, 210, 770, 871, 285, 0, 0, 0, 0, 183, 330, 516, 791, 12, 0, 0, 0, 0, 0, 661, 659, 435, 127, 0, 0, 0, 0, 0, 0, 819, 328, 162, 0, 0, 0, 0, 0, 0, 0, 514, 1, 0, 0, 0, 0, 0, 0, 0, 0, 658] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_5 :
    (evaluatedRows (5 : F) 0).det = point (5 : F) 1 * quotientValue 0 5 := by
  apply det_of_factors lower0_5 upper0_5
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_5 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 138, 1, 0, 0, 0, 0, 0, 0, 0, 366, 549, 1, 0, 0, 0, 0, 0, 0, 136, 394, 526, 1, 0, 0, 0, 0, 0, 755, 77, 19, 799, 1, 0, 0, 0, 0, 811, 225, 622, 764, 184, 1, 0, 0, 0, 939, 774, 99, 191, 506, 163, 1, 0, 0, 858, 496, 398, 665, 248, 946, 841, 1, 0, 94, 143, 670, 397, 335, 628, 363, 55, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_5 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[669, 544, 144, 432, 650, 48, 0, 0, 0, 0, 604, 479, 559, 942, 37, 986, 0, 985, 0, 0, 560, 42, 357, 484, 117, 24, 59, 0, 0, 0, 547, 856, 736, 997, 934, 614, 0, 0, 0, 0, 835, 333, 339, 629, 420, 0, 0, 0, 0, 0, 515, 276, 115, 801, 0, 0, 0, 0, 0, 0, 479, 837, 380, 0, 0, 0, 0, 0, 0, 0, 910, 634, 0, 0, 0, 0, 0, 0, 0, 0, 389] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_5 :
    (evaluatedRows (5 : F) 1).det = point (5 : F) 1 * quotientValue 1 5 := by
  apply det_of_factors lower1_5 upper1_5
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel


end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
