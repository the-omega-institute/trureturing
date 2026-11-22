/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch30
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch30
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 30 through 35. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_30 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 638, 1, 0, 0, 0, 0, 0, 0, 0, 287, 78, 1, 0, 0, 0, 0, 0, 0, 881, 271, 544, 1, 0, 0, 0, 0, 0, 993, 681, 479, 67, 1, 0, 0, 0, 0, 567, 862, 465, 126, 419, 1, 0, 0, 0, 349, 661, 521, 595, 127, 605, 1, 0, 0, 403, 548, 880, 83, 851, 273, 410, 1, 0, 589, 557, 292, 125, 924, 450, 319, 731, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_30 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[237, 160, 423, 544, 689, 374, 0, 299, 15, 0, 233, 457, 42, 744, 506, 710, 948, 894, 0, 0, 864, 119, 410, 807, 100, 300, 629, 0, 0, 0, 213, 394, 425, 395, 857, 445, 0, 0, 0, 0, 566, 711, 970, 778, 812, 0, 0, 0, 0, 0, 464, 843, 662, 1002, 0, 0, 0, 0, 0, 0, 390, 410, 169, 0, 0, 0, 0, 0, 0, 0, 67, 799, 0, 0, 0, 0, 0, 0, 0, 0, 813] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_30 :
    (evaluatedRows (30 : F) 0).det = point (30 : F) 1 * quotientValue 0 30 := by
  apply det_of_factors lower0_30 upper0_30
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_30 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 853, 1, 0, 0, 0, 0, 0, 0, 0, 787, 640, 1, 0, 0, 0, 0, 0, 0, 433, 194, 718, 1, 0, 0, 0, 0, 0, 937, 1005, 696, 12, 1, 0, 0, 0, 0, 29, 206, 141, 531, 872, 1, 0, 0, 0, 57, 748, 600, 170, 1008, 995, 1, 0, 0, 300, 817, 925, 361, 267, 940, 521, 1, 0, 128, 451, 262, 977, 910, 439, 551, 589, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_30 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[389, 923, 207, 102, 326, 769, 0, 0, 0, 0, 105, 932, 795, 808, 887, 710, 0, 374, 0, 0, 895, 283, 120, 883, 644, 635, 782, 0, 0, 0, 637, 219, 83, 223, 420, 402, 0, 0, 0, 0, 673, 938, 804, 173, 391, 0, 0, 0, 0, 0, 235, 476, 641, 718, 0, 0, 0, 0, 0, 0, 166, 707, 578, 0, 0, 0, 0, 0, 0, 0, 987, 771, 0, 0, 0, 0, 0, 0, 0, 0, 798] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_30 :
    (evaluatedRows (30 : F) 1).det = point (30 : F) 1 * quotientValue 1 30 := by
  apply det_of_factors lower1_30 upper1_30
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_31 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 620, 1, 0, 0, 0, 0, 0, 0, 0, 28, 632, 1, 0, 0, 0, 0, 0, 0, 428, 76, 56, 1, 0, 0, 0, 0, 0, 136, 203, 110, 408, 1, 0, 0, 0, 0, 21, 895, 95, 633, 266, 1, 0, 0, 0, 69, 879, 8, 570, 895, 132, 1, 0, 0, 636, 929, 134, 512, 580, 236, 767, 1, 0, 24, 840, 549, 383, 114, 332, 614, 3, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_31 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[616, 735, 115, 565, 402, 219, 0, 74, 87, 0, 848, 33, 918, 936, 348, 935, 534, 765, 0, 0, 447, 573, 136, 22, 267, 254, 422, 0, 0, 0, 718, 640, 138, 762, 65, 660, 0, 0, 0, 0, 740, 976, 273, 294, 523, 0, 0, 0, 0, 0, 202, 188, 141, 286, 0, 0, 0, 0, 0, 0, 790, 785, 502, 0, 0, 0, 0, 0, 0, 0, 582, 126, 0, 0, 0, 0, 0, 0, 0, 0, 885] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_31 :
    (evaluatedRows (31 : F) 0).det = point (31 : F) 1 * quotientValue 0 31 := by
  apply det_of_factors lower0_31 upper0_31
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_31 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 950, 1, 0, 0, 0, 0, 0, 0, 0, 108, 95, 1, 0, 0, 0, 0, 0, 0, 786, 32, 963, 1, 0, 0, 0, 0, 0, 957, 898, 267, 75, 1, 0, 0, 0, 0, 81, 311, 604, 419, 748, 1, 0, 0, 0, 122, 929, 147, 563, 904, 166, 1, 0, 0, 291, 387, 532, 450, 237, 39, 631, 1, 0, 525, 732, 398, 113, 780, 623, 821, 281, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_31 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[795, 499, 952, 370, 656, 595, 0, 0, 0, 0, 660, 367, 727, 306, 712, 935, 0, 219, 0, 0, 859, 197, 544, 353, 889, 790, 384, 0, 0, 0, 21, 287, 484, 884, 796, 163, 0, 0, 0, 0, 34, 307, 523, 463, 405, 0, 0, 0, 0, 0, 282, 540, 866, 31, 0, 0, 0, 0, 0, 0, 603, 467, 922, 0, 0, 0, 0, 0, 0, 0, 495, 311, 0, 0, 0, 0, 0, 0, 0, 0, 357] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_31 :
    (evaluatedRows (31 : F) 1).det = point (31 : F) 1 * quotientValue 1 31 := by
  apply det_of_factors lower1_31 upper1_31
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_32 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 343, 1, 0, 0, 0, 0, 0, 0, 0, 411, 393, 1, 0, 0, 0, 0, 0, 0, 404, 199, 452, 1, 0, 0, 0, 0, 0, 773, 860, 616, 876, 1, 0, 0, 0, 0, 62, 872, 228, 191, 931, 1, 0, 0, 0, 75, 476, 555, 430, 132, 987, 1, 0, 0, 158, 633, 942, 988, 325, 919, 370, 1, 0, 420, 487, 103, 920, 4, 463, 54, 457, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_32 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[859, 438, 971, 297, 874, 721, 0, 588, 372, 0, 321, 913, 762, 438, 539, 421, 116, 259, 0, 0, 350, 739, 738, 966, 660, 597, 598, 0, 0, 0, 389, 340, 615, 312, 842, 621, 0, 0, 0, 0, 304, 288, 71, 865, 566, 0, 0, 0, 0, 0, 742, 190, 120, 706, 0, 0, 0, 0, 0, 0, 894, 822, 409, 0, 0, 0, 0, 0, 0, 0, 244, 880, 0, 0, 0, 0, 0, 0, 0, 0, 211] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_32 :
    (evaluatedRows (32 : F) 0).det = point (32 : F) 1 * quotientValue 0 32 := by
  apply det_of_factors lower0_32 upper0_32
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_32 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 856, 1, 0, 0, 0, 0, 0, 0, 0, 708, 7, 1, 0, 0, 0, 0, 0, 0, 11, 539, 494, 1, 0, 0, 0, 0, 0, 573, 126, 877, 762, 1, 0, 0, 0, 0, 696, 568, 856, 696, 186, 1, 0, 0, 0, 549, 721, 684, 294, 21, 690, 1, 0, 0, 309, 628, 860, 54, 778, 111, 138, 1, 0, 451, 228, 804, 674, 837, 647, 660, 34, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_32 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[178, 701, 872, 951, 20, 694, 0, 0, 0, 0, 513, 215, 931, 580, 874, 421, 0, 721, 0, 0, 117, 751, 285, 555, 717, 288, 1007, 0, 0, 0, 254, 691, 164, 67, 585, 359, 0, 0, 0, 0, 592, 234, 340, 570, 117, 0, 0, 0, 0, 0, 472, 576, 998, 945, 0, 0, 0, 0, 0, 0, 258, 977, 352, 0, 0, 0, 0, 0, 0, 0, 573, 724, 0, 0, 0, 0, 0, 0, 0, 0, 205] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_32 :
    (evaluatedRows (32 : F) 1).det = point (32 : F) 1 * quotientValue 1 32 := by
  apply det_of_factors lower1_32 upper1_32
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_33 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 965, 1, 0, 0, 0, 0, 0, 0, 0, 87, 719, 1, 0, 0, 0, 0, 0, 0, 180, 310, 412, 1, 0, 0, 0, 0, 0, 296, 596, 577, 284, 1, 0, 0, 0, 0, 30, 982, 320, 944, 539, 1, 0, 0, 0, 981, 592, 130, 209, 959, 720, 1, 0, 0, 17, 628, 548, 446, 550, 937, 725, 1, 0, 377, 335, 727, 332, 65, 165, 933, 447, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_33 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[383, 231, 327, 673, 35, 162, 0, 804, 738, 0, 305, 507, 473, 624, 336, 205, 61, 346, 0, 0, 82, 65, 207, 403, 190, 48, 819, 0, 0, 0, 697, 586, 218, 439, 56, 829, 0, 0, 0, 0, 780, 91, 788, 502, 211, 0, 0, 0, 0, 0, 716, 470, 179, 668, 0, 0, 0, 0, 0, 0, 781, 891, 834, 0, 0, 0, 0, 0, 0, 0, 693, 282, 0, 0, 0, 0, 0, 0, 0, 0, 569] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_33 :
    (evaluatedRows (33 : F) 0).det = point (33 : F) 1 * quotientValue 0 33 := by
  apply det_of_factors lower0_33 upper0_33
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_33 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 497, 1, 0, 0, 0, 0, 0, 0, 0, 462, 780, 1, 0, 0, 0, 0, 0, 0, 260, 827, 889, 1, 0, 0, 0, 0, 0, 876, 858, 411, 856, 1, 0, 0, 0, 0, 716, 782, 597, 1006, 881, 1, 0, 0, 0, 408, 149, 65, 267, 271, 718, 1, 0, 0, 473, 252, 881, 819, 818, 597, 620, 1, 0, 993, 128, 180, 130, 322, 709, 1005, 697, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_33 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[498, 120, 984, 10, 132, 401, 0, 0, 0, 0, 122, 562, 197, 74, 756, 205, 0, 162, 0, 0, 560, 281, 234, 774, 802, 847, 774, 0, 0, 0, 999, 228, 997, 362, 564, 475, 0, 0, 0, 0, 677, 807, 985, 113, 770, 0, 0, 0, 0, 0, 829, 534, 94, 990, 0, 0, 0, 0, 0, 0, 526, 960, 36, 0, 0, 0, 0, 0, 0, 0, 640, 974, 0, 0, 0, 0, 0, 0, 0, 0, 116] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_33 :
    (evaluatedRows (33 : F) 1).det = point (33 : F) 1 * quotientValue 1 33 := by
  apply det_of_factors lower1_33 upper1_33
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_34 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 139, 1, 0, 0, 0, 0, 0, 0, 0, 875, 432, 1, 0, 0, 0, 0, 0, 0, 949, 767, 413, 1, 0, 0, 0, 0, 0, 720, 725, 373, 951, 1, 0, 0, 0, 0, 691, 711, 854, 844, 20, 1, 0, 0, 0, 778, 664, 321, 757, 118, 851, 1, 0, 0, 204, 742, 818, 225, 609, 192, 76, 1, 0, 581, 546, 692, 785, 594, 821, 891, 361, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_34 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[848, 765, 837, 217, 906, 768, 0, 142, 748, 0, 211, 336, 633, 898, 463, 867, 442, 723, 0, 0, 178, 28, 763, 911, 56, 864, 795, 0, 0, 0, 182, 169, 772, 21, 94, 589, 0, 0, 0, 0, 498, 851, 901, 998, 417, 0, 0, 0, 0, 0, 761, 188, 41, 555, 0, 0, 0, 0, 0, 0, 141, 961, 684, 0, 0, 0, 0, 0, 0, 0, 351, 63, 0, 0, 0, 0, 0, 0, 0, 0, 959] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_34 :
    (evaluatedRows (34 : F) 0).det = point (34 : F) 1 * quotientValue 0 34 := by
  apply det_of_factors lower0_34 upper0_34
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_34 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 123, 1, 0, 0, 0, 0, 0, 0, 0, 346, 341, 1, 0, 0, 0, 0, 0, 0, 426, 394, 903, 1, 0, 0, 0, 0, 0, 942, 203, 847, 608, 1, 0, 0, 0, 0, 38, 815, 274, 132, 879, 1, 0, 0, 0, 732, 207, 938, 360, 634, 942, 1, 0, 0, 166, 2, 991, 248, 534, 528, 807, 1, 0, 819, 640, 30, 944, 161, 849, 105, 86, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_34 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[179, 900, 617, 942, 115, 75, 0, 0, 0, 0, 891, 428, 695, 688, 117, 867, 0, 768, 0, 0, 658, 323, 969, 889, 251, 241, 452, 0, 0, 0, 757, 821, 987, 825, 612, 703, 0, 0, 0, 0, 670, 382, 99, 827, 149, 0, 0, 0, 0, 0, 1006, 314, 478, 248, 0, 0, 0, 0, 0, 0, 284, 709, 166, 0, 0, 0, 0, 0, 0, 0, 59, 1006, 0, 0, 0, 0, 0, 0, 0, 0, 247] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_34 :
    (evaluatedRows (34 : F) 1).det = point (34 : F) 1 * quotientValue 1 34 := by
  apply det_of_factors lower1_34 upper1_34
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_35 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 665, 1, 0, 0, 0, 0, 0, 0, 0, 417, 928, 1, 0, 0, 0, 0, 0, 0, 528, 985, 959, 1, 0, 0, 0, 0, 0, 488, 406, 116, 635, 1, 0, 0, 0, 0, 662, 443, 736, 279, 361, 1, 0, 0, 0, 687, 404, 621, 345, 429, 539, 1, 0, 0, 757, 789, 713, 759, 483, 757, 203, 1, 0, 628, 194, 190, 53, 852, 29, 253, 447, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_35 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[384, 864, 990, 669, 671, 454, 0, 404, 289, 0, 54, 784, 164, 290, 501, 605, 743, 988, 0, 0, 666, 109, 623, 999, 284, 233, 884, 0, 0, 0, 983, 120, 54, 468, 348, 847, 0, 0, 0, 0, 205, 117, 115, 15, 22, 0, 0, 0, 0, 0, 948, 789, 866, 545, 0, 0, 0, 0, 0, 0, 236, 54, 714, 0, 0, 0, 0, 0, 0, 0, 607, 1002, 0, 0, 0, 0, 0, 0, 0, 0, 42] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_35 :
    (evaluatedRows (35 : F) 0).det = point (35 : F) 1 * quotientValue 0 35 := by
  apply det_of_factors lower0_35 upper0_35
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_35 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 836, 1, 0, 0, 0, 0, 0, 0, 0, 899, 871, 1, 0, 0, 0, 0, 0, 0, 289, 725, 954, 1, 0, 0, 0, 0, 0, 527, 868, 919, 315, 1, 0, 0, 0, 0, 198, 563, 596, 836, 275, 1, 0, 0, 0, 806, 121, 74, 338, 665, 646, 1, 0, 0, 894, 643, 478, 116, 512, 309, 968, 1, 0, 703, 973, 87, 912, 585, 93, 7, 135, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_35 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[122, 627, 284, 302, 116, 33, 0, 0, 0, 0, 1001, 957, 867, 415, 375, 605, 0, 454, 0, 0, 726, 938, 54, 289, 463, 555, 94, 0, 0, 0, 419, 4, 58, 530, 795, 680, 0, 0, 0, 0, 543, 965, 115, 489, 566, 0, 0, 0, 0, 0, 786, 589, 896, 314, 0, 0, 0, 0, 0, 0, 720, 46, 41, 0, 0, 0, 0, 0, 0, 0, 909, 545, 0, 0, 0, 0, 0, 0, 0, 0, 165] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_35 :
    (evaluatedRows (35 : F) 1).det = point (35 : F) 1 * quotientValue 1 35 := by
  apply det_of_factors lower1_35 upper1_35
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
