/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch12
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch12
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 12 through 17. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_12 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 943, 1, 0, 0, 0, 0, 0, 0, 0, 49, 77, 1, 0, 0, 0, 0, 0, 0, 100, 697, 134, 1, 0, 0, 0, 0, 0, 875, 557, 405, 112, 1, 0, 0, 0, 0, 191, 727, 446, 197, 184, 1, 0, 0, 0, 805, 775, 668, 793, 968, 49, 1, 0, 0, 489, 590, 429, 594, 293, 961, 163, 1, 0, 826, 469, 469, 819, 549, 329, 609, 775, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_12 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[889, 743, 228, 312, 93, 612, 0, 517, 902, 0, 792, 147, 973, 960, 139, 492, 825, 613, 0, 0, 52, 295, 850, 186, 565, 331, 420, 0, 0, 0, 651, 400, 775, 101, 191, 894, 0, 0, 0, 0, 83, 611, 771, 699, 489, 0, 0, 0, 0, 0, 696, 193, 17, 696, 0, 0, 0, 0, 0, 0, 592, 187, 418, 0, 0, 0, 0, 0, 0, 0, 740, 773, 0, 0, 0, 0, 0, 0, 0, 0, 759] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_12 :
    (evaluatedRows (12 : F) 0).det = point (12 : F) 1 * quotientValue 0 12 := by
  apply det_of_factors lower0_12 upper0_12
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_12 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 734, 1, 0, 0, 0, 0, 0, 0, 0, 36, 856, 1, 0, 0, 0, 0, 0, 0, 753, 804, 343, 1, 0, 0, 0, 0, 0, 787, 401, 874, 173, 1, 0, 0, 0, 0, 964, 528, 418, 175, 4, 1, 0, 0, 0, 159, 786, 27, 791, 1001, 140, 1, 0, 0, 524, 311, 689, 505, 785, 655, 397, 1, 0, 751, 889, 937, 2, 549, 431, 286, 118, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_12 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[173, 401, 862, 191, 102, 706, 0, 0, 0, 0, 480, 169, 618, 674, 529, 492, 0, 612, 0, 0, 215, 598, 184, 543, 717, 397, 808, 0, 0, 0, 617, 925, 158, 225, 329, 180, 0, 0, 0, 0, 869, 407, 182, 229, 938, 0, 0, 0, 0, 0, 344, 513, 951, 563, 0, 0, 0, 0, 0, 0, 392, 325, 341, 0, 0, 0, 0, 0, 0, 0, 115, 771, 0, 0, 0, 0, 0, 0, 0, 0, 409] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_12 :
    (evaluatedRows (12 : F) 1).det = point (12 : F) 1 * quotientValue 1 12 := by
  apply det_of_factors lower1_12 upper1_12
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_13 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 180, 308, 1, 0, 0, 0, 0, 0, 0, 240, 956, 655, 1, 0, 0, 0, 0, 0, 997, 701, 955, 496, 1, 0, 0, 0, 0, 829, 972, 266, 513, 981, 1, 0, 0, 0, 505, 743, 778, 480, 828, 662, 1, 0, 0, 508, 753, 530, 165, 361, 633, 610, 1, 0, 1001, 78, 218, 279, 526, 993, 575, 739, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_13 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[455, 954, 728, 713, 796, 83, 0, 735, 363, 0, 110, 241, 582, 899, 480, 274, 548, 366, 0, 0, 431, 951, 401, 404, 1, 524, 525, 0, 0, 0, 154, 488, 64, 750, 16, 870, 0, 0, 0, 0, 175, 782, 911, 829, 487, 0, 0, 0, 0, 0, 174, 860, 431, 339, 0, 0, 0, 0, 0, 0, 611, 898, 285, 0, 0, 0, 0, 0, 0, 0, 140, 969, 0, 0, 0, 0, 0, 0, 0, 0, 981] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_13 :
    (evaluatedRows (13 : F) 0).det = point (13 : F) 1 * quotientValue 0 13 := by
  apply det_of_factors lower0_13 upper0_13
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_13 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 942, 1, 0, 0, 0, 0, 0, 0, 0, 24, 775, 1, 0, 0, 0, 0, 0, 0, 32, 553, 235, 1, 0, 0, 0, 0, 0, 402, 989, 124, 993, 1, 0, 0, 0, 0, 985, 868, 156, 902, 998, 1, 0, 0, 0, 740, 28, 583, 230, 13, 759, 1, 0, 0, 135, 364, 550, 843, 877, 144, 932, 1, 0, 268, 374, 916, 462, 422, 169, 73, 329, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_13 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[890, 399, 425, 270, 327, 624, 0, 0, 0, 0, 499, 911, 927, 184, 76, 274, 0, 83, 0, 0, 28, 359, 722, 516, 186, 926, 251, 0, 0, 0, 293, 543, 233, 514, 552, 847, 0, 0, 0, 0, 968, 286, 621, 582, 249, 0, 0, 0, 0, 0, 625, 924, 199, 710, 0, 0, 0, 0, 0, 0, 456, 946, 522, 0, 0, 0, 0, 0, 0, 0, 890, 784, 0, 0, 0, 0, 0, 0, 0, 0, 85] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_13 :
    (evaluatedRows (13 : F) 1).det = point (13 : F) 1 * quotientValue 1 13 := by
  apply det_of_factors lower1_13 upper1_13
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_14 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 184, 1, 0, 0, 0, 0, 0, 0, 0, 365, 252, 1, 0, 0, 0, 0, 0, 0, 262, 664, 970, 1, 0, 0, 0, 0, 0, 604, 723, 660, 144, 1, 0, 0, 0, 0, 481, 925, 37, 275, 150, 1, 0, 0, 0, 922, 943, 269, 650, 715, 754, 1, 0, 0, 92, 19, 536, 16, 390, 795, 978, 1, 0, 522, 930, 290, 737, 548, 635, 730, 959, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_14 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[944, 249, 357, 612, 767, 977, 0, 904, 226, 0, 790, 814, 232, 636, 617, 105, 149, 762, 0, 0, 641, 161, 631, 378, 557, 809, 943, 0, 0, 0, 441, 436, 202, 435, 919, 964, 0, 0, 0, 0, 471, 139, 126, 471, 10, 0, 0, 0, 0, 0, 258, 206, 176, 189, 0, 0, 0, 0, 0, 0, 500, 716, 957, 0, 0, 0, 0, 0, 0, 0, 541, 662, 0, 0, 0, 0, 0, 0, 0, 0, 636] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_14 :
    (evaluatedRows (14 : F) 0).det = point (14 : F) 1 * quotientValue 0 14 := by
  apply det_of_factors lower0_14 upper0_14
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_14 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 754, 1, 0, 0, 0, 0, 0, 0, 0, 388, 58, 1, 0, 0, 0, 0, 0, 0, 613, 903, 877, 1, 0, 0, 0, 0, 0, 150, 406, 191, 72, 1, 0, 0, 0, 0, 644, 625, 419, 193, 916, 1, 0, 0, 0, 817, 562, 689, 398, 520, 442, 1, 0, 0, 377, 467, 175, 91, 924, 726, 578, 1, 0, 143, 58, 860, 943, 365, 698, 755, 673, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_14 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[680, 360, 79, 818, 568, 731, 0, 0, 0, 0, 173, 882, 568, 48, 523, 105, 0, 977, 0, 0, 1007, 289, 755, 741, 747, 32, 847, 0, 0, 0, 322, 481, 92, 762, 622, 91, 0, 0, 0, 0, 305, 230, 763, 272, 770, 0, 0, 0, 0, 0, 588, 513, 685, 956, 0, 0, 0, 0, 0, 0, 490, 558, 297, 0, 0, 0, 0, 0, 0, 0, 573, 789, 0, 0, 0, 0, 0, 0, 0, 0, 499] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_14 :
    (evaluatedRows (14 : F) 1).det = point (14 : F) 1 * quotientValue 1 14 := by
  apply det_of_factors lower1_14 upper1_14
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_15 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 488, 1, 0, 0, 0, 0, 0, 0, 0, 852, 190, 1, 0, 0, 0, 0, 0, 0, 744, 602, 600, 1, 0, 0, 0, 0, 0, 505, 911, 78, 542, 1, 0, 0, 0, 0, 491, 375, 725, 758, 857, 1, 0, 0, 0, 275, 771, 584, 736, 527, 174, 1, 0, 0, 968, 434, 775, 11, 126, 419, 648, 1, 0, 308, 356, 118, 316, 540, 719, 675, 365, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_15 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[369, 220, 488, 206, 115, 346, 0, 565, 172, 0, 237, 870, 736, 779, 492, 444, 746, 157, 0, 0, 318, 533, 2, 758, 224, 96, 201, 0, 0, 0, 836, 626, 690, 903, 550, 305, 0, 0, 0, 0, 49, 718, 84, 595, 438, 0, 0, 0, 0, 0, 604, 663, 800, 610, 0, 0, 0, 0, 0, 0, 648, 500, 56, 0, 0, 0, 0, 0, 0, 0, 394, 446, 0, 0, 0, 0, 0, 0, 0, 0, 189] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_15 :
    (evaluatedRows (15 : F) 0).det = point (15 : F) 1 * quotientValue 0 15 := by
  apply det_of_factors lower0_15 upper0_15
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_15 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 601, 1, 0, 0, 0, 0, 0, 0, 0, 429, 690, 1, 0, 0, 0, 0, 0, 0, 602, 172, 66, 1, 0, 0, 0, 0, 0, 471, 500, 61, 80, 1, 0, 0, 0, 0, 400, 942, 574, 274, 650, 1, 0, 0, 0, 746, 971, 309, 487, 598, 730, 1, 0, 0, 729, 779, 978, 765, 761, 306, 717, 1, 0, 553, 759, 349, 786, 723, 419, 424, 416, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_15 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[627, 900, 684, 141, 393, 750, 0, 0, 0, 0, 567, 469, 379, 308, 101, 444, 0, 346, 0, 0, 672, 949, 81, 617, 204, 663, 393, 0, 0, 0, 995, 105, 49, 978, 969, 642, 0, 0, 0, 0, 65, 3, 445, 873, 531, 0, 0, 0, 0, 0, 816, 522, 829, 221, 0, 0, 0, 0, 0, 0, 263, 98, 899, 0, 0, 0, 0, 0, 0, 0, 889, 521, 0, 0, 0, 0, 0, 0, 0, 0, 851] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_15 :
    (evaluatedRows (15 : F) 1).det = point (15 : F) 1 * quotientValue 1 15 := by
  apply det_of_factors lower1_15 upper1_15
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_16 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 239, 1, 0, 0, 0, 0, 0, 0, 0, 54, 845, 1, 0, 0, 0, 0, 0, 0, 971, 63, 506, 1, 0, 0, 0, 0, 0, 733, 424, 675, 886, 1, 0, 0, 0, 0, 821, 833, 85, 517, 531, 1, 0, 0, 0, 624, 45, 307, 581, 673, 745, 1, 0, 0, 390, 865, 188, 992, 432, 499, 565, 1, 0, 299, 665, 765, 18, 907, 937, 66, 301, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_16 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[991, 175, 922, 969, 962, 691, 0, 156, 599, 0, 397, 588, 883, 739, 737, 853, 49, 808, 0, 0, 734, 995, 903, 972, 51, 939, 275, 0, 0, 0, 443, 578, 626, 166, 20, 870, 0, 0, 0, 0, 82, 47, 123, 288, 865, 0, 0, 0, 0, 0, 486, 378, 831, 451, 0, 0, 0, 0, 0, 0, 848, 457, 279, 0, 0, 0, 0, 0, 0, 0, 230, 141, 0, 0, 0, 0, 0, 0, 0, 0, 266] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_16 :
    (evaluatedRows (16 : F) 0).det = point (16 : F) 1 * quotientValue 0 16 := by
  apply det_of_factors lower0_16 upper0_16
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_16 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 145, 1, 0, 0, 0, 0, 0, 0, 0, 894, 470, 1, 0, 0, 0, 0, 0, 0, 492, 731, 805, 1, 0, 0, 0, 0, 0, 812, 238, 899, 463, 1, 0, 0, 0, 0, 363, 118, 471, 953, 716, 1, 0, 0, 0, 577, 672, 606, 39, 228, 592, 1, 0, 0, 739, 134, 488, 286, 268, 715, 462, 1, 0, 802, 876, 394, 52, 797, 558, 85, 532, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_16 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[26, 836, 166, 82, 321, 641, 0, 0, 0, 0, 713, 121, 622, 474, 293, 853, 0, 691, 0, 0, 57, 947, 58, 737, 73, 318, 128, 0, 0, 0, 920, 128, 236, 785, 397, 934, 0, 0, 0, 0, 567, 768, 1001, 438, 844, 0, 0, 0, 0, 0, 768, 82, 914, 429, 0, 0, 0, 0, 0, 0, 538, 435, 739, 0, 0, 0, 0, 0, 0, 0, 814, 593, 0, 0, 0, 0, 0, 0, 0, 0, 136] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_16 :
    (evaluatedRows (16 : F) 1).det = point (16 : F) 1 * quotientValue 1 16 := by
  apply det_of_factors lower1_16 upper1_16
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_17 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 829, 1, 0, 0, 0, 0, 0, 0, 0, 983, 511, 1, 0, 0, 0, 0, 0, 0, 778, 969, 113, 1, 0, 0, 0, 0, 0, 67, 964, 387, 437, 1, 0, 0, 0, 0, 147, 488, 591, 23, 737, 1, 0, 0, 0, 337, 142, 144, 802, 354, 221, 1, 0, 0, 790, 152, 902, 149, 364, 213, 626, 1, 0, 232, 216, 77, 776, 132, 970, 255, 132, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_17 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[519, 667, 495, 178, 551, 727, 0, 93, 624, 0, 593, 460, 4, 748, 75, 916, 596, 39, 0, 0, 316, 988, 896, 850, 485, 844, 331, 0, 0, 0, 798, 254, 904, 1006, 544, 901, 0, 0, 0, 0, 51, 758, 565, 116, 992, 0, 0, 0, 0, 0, 245, 504, 58, 201, 0, 0, 0, 0, 0, 0, 581, 819, 86, 0, 0, 0, 0, 0, 0, 0, 139, 533, 0, 0, 0, 0, 0, 0, 0, 0, 510] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_17 :
    (evaluatedRows (17 : F) 0).det = point (17 : F) 1 * quotientValue 0 17 := by
  apply det_of_factors lower0_17 upper0_17
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_17 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 906, 1, 0, 0, 0, 0, 0, 0, 0, 669, 113, 1, 0, 0, 0, 0, 0, 0, 860, 589, 391, 1, 0, 0, 0, 0, 0, 100, 423, 643, 452, 1, 0, 0, 0, 0, 370, 918, 641, 52, 4, 1, 0, 0, 0, 759, 134, 299, 985, 818, 569, 1, 0, 0, 396, 946, 675, 177, 905, 572, 256, 1, 0, 783, 375, 23, 358, 658, 702, 475, 52, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_17 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[378, 174, 425, 5, 392, 310, 0, 0, 0, 0, 364, 540, 767, 466, 27, 916, 0, 727, 0, 0, 259, 207, 415, 533, 804, 282, 587, 0, 0, 0, 322, 849, 151, 735, 871, 711, 0, 0, 0, 0, 954, 881, 807, 144, 505, 0, 0, 0, 0, 0, 453, 997, 743, 989, 0, 0, 0, 0, 0, 0, 48, 418, 737, 0, 0, 0, 0, 0, 0, 0, 927, 957, 0, 0, 0, 0, 0, 0, 0, 0, 479] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_17 :
    (evaluatedRows (17 : F) 1).det = point (17 : F) 1 * quotientValue 1 17 := by
  apply det_of_factors lower1_17 upper1_17
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
