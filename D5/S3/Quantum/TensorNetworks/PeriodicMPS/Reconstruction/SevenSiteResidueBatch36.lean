/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch36
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch36
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 36 through 41. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_36 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 24, 1, 0, 0, 0, 0, 0, 0, 0, 319, 728, 1, 0, 0, 0, 0, 0, 0, 446, 215, 707, 1, 0, 0, 0, 0, 0, 567, 336, 257, 925, 1, 0, 0, 0, 0, 119, 11, 437, 539, 508, 1, 0, 0, 0, 146, 504, 403, 686, 218, 839, 1, 0, 0, 951, 56, 393, 149, 738, 28, 942, 1, 0, 589, 785, 974, 926, 334, 280, 33, 174, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_36 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[935, 45, 762, 502, 938, 319, 0, 794, 403, 0, 785, 141, 872, 295, 13, 215, 115, 737, 0, 0, 776, 49, 775, 559, 481, 690, 847, 0, 0, 0, 727, 597, 492, 155, 497, 576, 0, 0, 0, 0, 916, 375, 74, 613, 764, 0, 0, 0, 0, 0, 231, 666, 903, 803, 0, 0, 0, 0, 0, 0, 421, 883, 641, 0, 0, 0, 0, 0, 0, 0, 957, 504, 0, 0, 0, 0, 0, 0, 0, 0, 520] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_36 :
    (evaluatedRows (36 : F) 0).det = point (36 : F) 1 * quotientValue 0 36 := by
  apply det_of_factors lower0_36 upper0_36
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_36 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 493, 1, 0, 0, 0, 0, 0, 0, 0, 709, 728, 1, 0, 0, 0, 0, 0, 0, 501, 760, 713, 1, 0, 0, 0, 0, 0, 422, 920, 493, 972, 1, 0, 0, 0, 0, 973, 513, 474, 760, 348, 1, 0, 0, 0, 897, 124, 982, 340, 327, 477, 1, 0, 0, 238, 171, 709, 295, 222, 465, 201, 1, 0, 958, 105, 948, 716, 130, 972, 346, 532, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_36 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[637, 362, 518, 960, 885, 506, 0, 0, 0, 0, 983, 170, 753, 192, 371, 215, 0, 319, 0, 0, 776, 49, 775, 559, 481, 690, 847, 0, 0, 0, 289, 414, 251, 165, 867, 437, 0, 0, 0, 0, 257, 560, 279, 116, 751, 0, 0, 0, 0, 0, 349, 609, 564, 286, 0, 0, 0, 0, 0, 0, 618, 92, 384, 0, 0, 0, 0, 0, 0, 0, 522, 194, 0, 0, 0, 0, 0, 0, 0, 0, 677] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_36 :
    (evaluatedRows (36 : F) 1).det = point (36 : F) 1 * quotientValue 1 36 := by
  apply det_of_factors lower1_36 upper1_36
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_37 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 534, 1, 0, 0, 0, 0, 0, 0, 0, 782, 54, 1, 0, 0, 0, 0, 0, 0, 773, 675, 62, 1, 0, 0, 0, 0, 0, 882, 202, 352, 782, 1, 0, 0, 0, 0, 721, 635, 429, 847, 79, 1, 0, 0, 0, 193, 132, 217, 594, 306, 156, 1, 0, 0, 164, 443, 747, 933, 601, 937, 983, 1, 0, 32, 440, 228, 683, 65, 199, 172, 552, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_37 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[468, 29, 205, 547, 847, 648, 0, 159, 284, 0, 695, 628, 988, 467, 780, 850, 859, 342, 0, 0, 640, 356, 368, 199, 230, 158, 595, 0, 0, 0, 13, 497, 865, 237, 990, 97, 0, 0, 0, 0, 72, 582, 339, 582, 683, 0, 0, 0, 0, 0, 360, 780, 342, 21, 0, 0, 0, 0, 0, 0, 558, 36, 470, 0, 0, 0, 0, 0, 0, 0, 293, 863, 0, 0, 0, 0, 0, 0, 0, 0, 362] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_37 :
    (evaluatedRows (37 : F) 0).det = point (37 : F) 1 * quotientValue 0 37 := by
  apply det_of_factors lower0_37 upper0_37
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_37 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 944, 1, 0, 0, 0, 0, 0, 0, 0, 808, 725, 1, 0, 0, 0, 0, 0, 0, 520, 25, 84, 1, 0, 0, 0, 0, 0, 981, 542, 44, 959, 1, 0, 0, 0, 0, 874, 108, 638, 215, 60, 1, 0, 0, 0, 122, 987, 328, 591, 238, 958, 1, 0, 0, 203, 14, 409, 517, 306, 643, 681, 1, 0, 15, 284, 155, 758, 308, 388, 356, 747, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_37 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[393, 566, 708, 31, 327, 599, 0, 0, 0, 0, 503, 732, 473, 799, 309, 850, 0, 648, 0, 0, 198, 481, 844, 460, 974, 361, 394, 0, 0, 0, 161, 833, 678, 861, 101, 167, 0, 0, 0, 0, 883, 167, 25, 193, 160, 0, 0, 0, 0, 0, 387, 190, 90, 487, 0, 0, 0, 0, 0, 0, 452, 519, 87, 0, 0, 0, 0, 0, 0, 0, 763, 725, 0, 0, 0, 0, 0, 0, 0, 0, 77] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_37 :
    (evaluatedRows (37 : F) 1).det = point (37 : F) 1 * quotientValue 1 37 := by
  apply det_of_factors lower1_37 upper1_37
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_38 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 107, 1, 0, 0, 0, 0, 0, 0, 0, 502, 977, 1, 0, 0, 0, 0, 0, 0, 532, 381, 504, 1, 0, 0, 0, 0, 0, 570, 122, 998, 267, 1, 0, 0, 0, 0, 279, 114, 687, 985, 122, 1, 0, 0, 0, 262, 440, 212, 708, 75, 17, 1, 0, 0, 993, 949, 26, 718, 574, 156, 938, 1, 0, 225, 851, 728, 760, 143, 97, 225, 701, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_38 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[317, 198, 54, 537, 268, 556, 0, 397, 531, 0, 501, 999, 592, 839, 517, 612, 908, 243, 0, 0, 528, 466, 844, 169, 891, 736, 527, 0, 0, 0, 941, 486, 8, 857, 670, 381, 0, 0, 0, 0, 976, 452, 703, 495, 329, 0, 0, 0, 0, 0, 564, 916, 69, 363, 0, 0, 0, 0, 0, 0, 244, 234, 168, 0, 0, 0, 0, 0, 0, 0, 434, 959, 0, 0, 0, 0, 0, 0, 0, 0, 183] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_38 :
    (evaluatedRows (38 : F) 0).det = point (38 : F) 1 * quotientValue 0 38 := by
  apply det_of_factors lower0_38 upper0_38
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_38 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 517, 1, 0, 0, 0, 0, 0, 0, 0, 549, 967, 1, 0, 0, 0, 0, 0, 0, 15, 851, 655, 1, 0, 0, 0, 0, 0, 953, 363, 229, 201, 1, 0, 0, 0, 0, 886, 865, 61, 432, 984, 1, 0, 0, 0, 785, 495, 723, 300, 881, 580, 1, 0, 0, 83, 247, 464, 533, 483, 598, 525, 1, 0, 31, 849, 136, 180, 725, 634, 396, 589, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_38 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[413, 52, 962, 12, 144, 291, 0, 0, 0, 0, 857, 806, 388, 472, 372, 612, 0, 556, 0, 0, 837, 482, 868, 549, 957, 453, 145, 0, 0, 0, 63, 481, 339, 595, 417, 285, 0, 0, 0, 0, 585, 520, 866, 948, 42, 0, 0, 0, 0, 0, 360, 527, 34, 789, 0, 0, 0, 0, 0, 0, 403, 137, 42, 0, 0, 0, 0, 0, 0, 0, 851, 335, 0, 0, 0, 0, 0, 0, 0, 0, 806] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_38 :
    (evaluatedRows (38 : F) 1).det = point (38 : F) 1 * quotientValue 1 38 := by
  apply det_of_factors lower1_38 upper1_38
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_39 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 612, 1, 0, 0, 0, 0, 0, 0, 0, 209, 499, 1, 0, 0, 0, 0, 0, 0, 935, 578, 67, 1, 0, 0, 0, 0, 0, 371, 936, 381, 652, 1, 0, 0, 0, 0, 509, 747, 374, 6, 169, 1, 0, 0, 0, 559, 764, 545, 619, 689, 389, 1, 0, 0, 602, 892, 134, 469, 819, 526, 912, 1, 0, 34, 890, 637, 312, 1002, 876, 708, 776, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_39 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[604, 26, 877, 301, 793, 969, 0, 470, 188, 0, 542, 268, 974, 928, 76, 539, 934, 939, 0, 0, 382, 106, 935, 167, 254, 784, 683, 0, 0, 0, 773, 930, 986, 374, 221, 845, 0, 0, 0, 0, 961, 865, 494, 938, 251, 0, 0, 0, 0, 0, 192, 699, 573, 746, 0, 0, 0, 0, 0, 0, 395, 937, 241, 0, 0, 0, 0, 0, 0, 0, 196, 707, 0, 0, 0, 0, 0, 0, 0, 0, 162] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_39 :
    (evaluatedRows (40 : F) 0).det = point (40 : F) 1 * quotientValue 0 40 := by
  apply det_of_factors lower0_39 upper0_39
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_39 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 448, 1, 0, 0, 0, 0, 0, 0, 0, 397, 514, 1, 0, 0, 0, 0, 0, 0, 236, 420, 993, 1, 0, 0, 0, 0, 0, 753, 569, 1008, 675, 1, 0, 0, 0, 0, 122, 475, 126, 951, 831, 1, 0, 0, 0, 917, 227, 318, 238, 474, 469, 1, 0, 0, 289, 670, 818, 241, 778, 659, 237, 1, 0, 137, 929, 396, 323, 193, 644, 132, 203, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_39 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[717, 801, 723, 479, 963, 723, 0, 0, 0, 0, 666, 189, 864, 334, 806, 539, 0, 969, 0, 0, 833, 547, 82, 410, 241, 40, 380, 0, 0, 0, 681, 484, 435, 465, 484, 988, 0, 0, 0, 0, 680, 164, 288, 273, 352, 0, 0, 0, 0, 0, 813, 553, 150, 253, 0, 0, 0, 0, 0, 0, 736, 261, 937, 0, 0, 0, 0, 0, 0, 0, 350, 697, 0, 0, 0, 0, 0, 0, 0, 0, 802] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_39 :
    (evaluatedRows (40 : F) 1).det = point (40 : F) 1 * quotientValue 1 40 := by
  apply det_of_factors lower1_39 upper1_39
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_40 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 714, 1, 0, 0, 0, 0, 0, 0, 0, 538, 256, 1, 0, 0, 0, 0, 0, 0, 247, 396, 864, 1, 0, 0, 0, 0, 0, 31, 877, 276, 938, 1, 0, 0, 0, 0, 646, 691, 659, 240, 683, 1, 0, 0, 0, 608, 101, 112, 785, 573, 970, 1, 0, 0, 650, 950, 89, 756, 168, 854, 810, 1, 0, 894, 357, 882, 404, 905, 836, 63, 131, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_40 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[876, 353, 91, 280, 772, 269, 0, 781, 575, 0, 56, 471, 878, 960, 78, 228, 343, 382, 0, 0, 504, 519, 597, 558, 588, 281, 494, 0, 0, 0, 592, 177, 976, 17, 867, 927, 0, 0, 0, 0, 698, 685, 548, 3, 744, 0, 0, 0, 0, 0, 731, 533, 609, 521, 0, 0, 0, 0, 0, 0, 118, 175, 264, 0, 0, 0, 0, 0, 0, 0, 419, 657, 0, 0, 0, 0, 0, 0, 0, 0, 626] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_40 :
    (evaluatedRows (41 : F) 0).det = point (41 : F) 1 * quotientValue 0 41 := by
  apply det_of_factors lower0_40 upper0_40
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_40 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 407, 1, 0, 0, 0, 0, 0, 0, 0, 41, 680, 1, 0, 0, 0, 0, 0, 0, 227, 432, 404, 1, 0, 0, 0, 0, 0, 53, 165, 139, 523, 1, 0, 0, 0, 0, 128, 867, 486, 56, 797, 1, 0, 0, 0, 714, 704, 793, 654, 347, 24, 1, 0, 0, 916, 213, 709, 780, 575, 622, 13, 1, 0, 552, 507, 103, 242, 915, 551, 274, 591, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_40 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[322, 180, 628, 923, 385, 766, 0, 0, 0, 0, 245, 550, 703, 954, 453, 228, 0, 269, 0, 0, 342, 295, 215, 359, 780, 740, 718, 0, 0, 0, 380, 991, 220, 74, 996, 961, 0, 0, 0, 0, 152, 900, 268, 785, 309, 0, 0, 0, 0, 0, 191, 289, 540, 633, 0, 0, 0, 0, 0, 0, 936, 31, 200, 0, 0, 0, 0, 0, 0, 0, 748, 563, 0, 0, 0, 0, 0, 0, 0, 0, 91] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_40 :
    (evaluatedRows (41 : F) 1).det = point (41 : F) 1 * quotientValue 1 41 := by
  apply det_of_factors lower1_40 upper1_40
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_41 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 917, 1, 0, 0, 0, 0, 0, 0, 0, 706, 767, 1, 0, 0, 0, 0, 0, 0, 875, 153, 687, 1, 0, 0, 0, 0, 0, 454, 89, 574, 515, 1, 0, 0, 0, 0, 289, 415, 830, 161, 594, 1, 0, 0, 0, 420, 903, 729, 989, 727, 36, 1, 0, 0, 55, 257, 976, 786, 855, 266, 663, 1, 0, 447, 8, 566, 281, 695, 607, 37, 59, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_41 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[685, 178, 432, 765, 373, 331, 0, 749, 103, 0, 580, 581, 527, 91, 79, 260, 296, 726, 0, 0, 377, 929, 935, 89, 259, 593, 56, 0, 0, 0, 132, 697, 795, 231, 733, 406, 0, 0, 0, 0, 834, 227, 882, 128, 145, 0, 0, 0, 0, 0, 959, 450, 75, 972, 0, 0, 0, 0, 0, 0, 778, 513, 897, 0, 0, 0, 0, 0, 0, 0, 326, 461, 0, 0, 0, 0, 0, 0, 0, 0, 671] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_41 :
    (evaluatedRows (42 : F) 0).det = point (42 : F) 1 * quotientValue 0 42 := by
  apply det_of_factors lower0_41 upper0_41
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_41 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 683, 1, 0, 0, 0, 0, 0, 0, 0, 45, 829, 1, 0, 0, 0, 0, 0, 0, 929, 564, 713, 1, 0, 0, 0, 0, 0, 512, 428, 381, 195, 1, 0, 0, 0, 0, 37, 71, 784, 139, 897, 1, 0, 0, 0, 567, 844, 816, 635, 575, 561, 1, 0, 0, 831, 847, 453, 853, 134, 585, 318, 1, 0, 553, 69, 133, 514, 86, 164, 567, 819, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_41 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[769, 40, 74, 251, 216, 78, 0, 0, 0, 0, 271, 96, 874, 876, 100, 260, 0, 331, 0, 0, 124, 524, 737, 104, 283, 678, 49, 0, 0, 0, 60, 246, 205, 695, 802, 298, 0, 0, 0, 0, 320, 649, 592, 720, 111, 0, 0, 0, 0, 0, 42, 314, 90, 183, 0, 0, 0, 0, 0, 0, 877, 618, 16, 0, 0, 0, 0, 0, 0, 0, 505, 285, 0, 0, 0, 0, 0, 0, 0, 0, 576] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_41 :
    (evaluatedRows (42 : F) 1).det = point (42 : F) 1 * quotientValue 1 42 := by
  apply det_of_factors lower1_41 upper1_41
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
