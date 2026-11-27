/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch42
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch42
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 42 through 46. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_42 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 262, 1, 0, 0, 0, 0, 0, 0, 0, 768, 498, 1, 0, 0, 0, 0, 0, 0, 570, 566, 347, 1, 0, 0, 0, 0, 0, 182, 829, 911, 99, 1, 0, 0, 0, 0, 135, 745, 972, 333, 572, 1, 0, 0, 0, 698, 275, 671, 384, 491, 837, 1, 0, 0, 779, 807, 749, 515, 560, 699, 942, 1, 0, 892, 353, 256, 481, 671, 336, 998, 288, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_42 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[217, 772, 20, 663, 636, 515, 0, 520, 712, 0, 22, 965, 238, 181, 573, 489, 984, 636, 0, 0, 287, 972, 840, 721, 953, 31, 160, 0, 0, 0, 716, 236, 133, 962, 195, 173, 0, 0, 0, 0, 536, 720, 115, 383, 800, 0, 0, 0, 0, 0, 696, 624, 767, 646, 0, 0, 0, 0, 0, 0, 754, 641, 523, 0, 0, 0, 0, 0, 0, 0, 226, 46, 0, 0, 0, 0, 0, 0, 0, 0, 434] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_42 :
    (evaluatedRows (43 : F) 0).det = point (43 : F) 1 * quotientValue 0 43 := by
  apply det_of_factors lower0_42 upper0_42
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_42 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 737, 1, 0, 0, 0, 0, 0, 0, 0, 928, 742, 1, 0, 0, 0, 0, 0, 0, 941, 99, 575, 1, 0, 0, 0, 0, 0, 304, 625, 977, 867, 1, 0, 0, 0, 0, 37, 841, 17, 33, 783, 1, 0, 0, 0, 423, 512, 353, 483, 995, 308, 1, 0, 0, 647, 853, 835, 845, 774, 123, 660, 1, 0, 237, 247, 194, 91, 536, 903, 144, 376, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_42 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[110, 459, 439, 188, 702, 166, 0, 0, 0, 0, 218, 497, 73, 571, 44, 489, 0, 515, 0, 0, 553, 486, 716, 489, 699, 494, 281, 0, 0, 0, 586, 192, 653, 687, 71, 522, 0, 0, 0, 0, 64, 553, 666, 420, 572, 0, 0, 0, 0, 0, 807, 763, 650, 306, 0, 0, 0, 0, 0, 0, 279, 605, 842, 0, 0, 0, 0, 0, 0, 0, 166, 378, 0, 0, 0, 0, 0, 0, 0, 0, 87] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_42 :
    (evaluatedRows (43 : F) 1).det = point (43 : F) 1 * quotientValue 1 43 := by
  apply det_of_factors lower1_42 upper1_42
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_43 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 131, 1, 0, 0, 0, 0, 0, 0, 0, 176, 957, 1, 0, 0, 0, 0, 0, 0, 104, 261, 962, 1, 0, 0, 0, 0, 0, 118, 146, 725, 193, 1, 0, 0, 0, 0, 482, 203, 807, 419, 400, 1, 0, 0, 0, 989, 598, 358, 124, 237, 282, 1, 0, 0, 319, 627, 107, 947, 522, 333, 408, 1, 0, 183, 725, 736, 165, 273, 564, 652, 132, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_43 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[675, 43, 291, 254, 321, 709, 0, 823, 246, 0, 389, 513, 639, 854, 712, 186, 150, 771, 0, 0, 574, 556, 584, 846, 345, 476, 832, 0, 0, 0, 157, 900, 684, 966, 754, 336, 0, 0, 0, 0, 839, 667, 318, 578, 607, 0, 0, 0, 0, 0, 74, 760, 172, 0, 0, 0, 0, 0, 0, 0, 1005, 28, 498, 0, 0, 0, 0, 0, 0, 0, 20, 242, 0, 0, 0, 0, 0, 0, 0, 0, 875] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_43 :
    (evaluatedRows (44 : F) 0).det = point (44 : F) 1 * quotientValue 0 44 := by
  apply det_of_factors lower0_43 upper0_43
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_43 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 771, 1, 0, 0, 0, 0, 0, 0, 0, 204, 759, 1, 0, 0, 0, 0, 0, 0, 304, 597, 161, 1, 0, 0, 0, 0, 0, 733, 92, 679, 510, 1, 0, 0, 0, 0, 788, 447, 401, 156, 787, 1, 0, 0, 0, 252, 255, 673, 580, 142, 999, 1, 0, 0, 622, 836, 693, 767, 845, 77, 304, 1, 0, 923, 20, 988, 407, 233, 598, 202, 457, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_43 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[523, 642, 872, 1006, 333, 549, 0, 0, 0, 0, 405, 983, 911, 70, 255, 186, 0, 709, 0, 0, 148, 252, 582, 0, 849, 300, 675, 0, 0, 0, 410, 69, 241, 483, 338, 168, 0, 0, 0, 0, 902, 427, 481, 46, 225, 0, 0, 0, 0, 0, 69, 662, 85, 406, 0, 0, 0, 0, 0, 0, 401, 987, 13, 0, 0, 0, 0, 0, 0, 0, 327, 27, 0, 0, 0, 0, 0, 0, 0, 0, 825] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_43 :
    (evaluatedRows (44 : F) 1).det = point (44 : F) 1 * quotientValue 1 44 := by
  apply det_of_factors lower1_43 upper1_43
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_44 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 887, 1, 0, 0, 0, 0, 0, 0, 0, 789, 634, 1, 0, 0, 0, 0, 0, 0, 996, 990, 459, 1, 0, 0, 0, 0, 0, 452, 902, 508, 637, 1, 0, 0, 0, 0, 313, 422, 229, 893, 929, 1, 0, 0, 0, 758, 664, 176, 899, 980, 206, 1, 0, 0, 664, 642, 362, 456, 646, 623, 341, 1, 0, 300, 626, 312, 471, 825, 746, 766, 489, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_44 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[524, 101, 550, 762, 115, 233, 0, 421, 147, 0, 407, 399, 381, 610, 27, 588, 912, 5, 0, 0, 16, 743, 476, 257, 391, 517, 918, 0, 0, 0, 18, 444, 253, 206, 359, 957, 0, 0, 0, 0, 339, 595, 479, 882, 15, 0, 0, 0, 0, 0, 338, 218, 180, 485, 0, 0, 0, 0, 0, 0, 184, 121, 333, 0, 0, 0, 0, 0, 0, 0, 1008, 604, 0, 0, 0, 0, 0, 0, 0, 0, 234] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_44 :
    (evaluatedRows (45 : F) 0).det = point (45 : F) 1 * quotientValue 0 45 := by
  apply det_of_factors lower0_44 upper0_44
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_44 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 201, 1, 0, 0, 0, 0, 0, 0, 0, 379, 403, 1, 0, 0, 0, 0, 0, 0, 559, 437, 820, 1, 0, 0, 0, 0, 0, 744, 300, 462, 108, 1, 0, 0, 0, 0, 667, 887, 970, 269, 54, 1, 0, 0, 0, 703, 897, 752, 936, 774, 945, 1, 0, 0, 709, 725, 816, 808, 217, 641, 388, 1, 0, 217, 305, 783, 495, 464, 203, 633, 910, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_44 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[199, 900, 156, 553, 467, 849, 0, 0, 0, 0, 913, 825, 82, 676, 734, 588, 0, 233, 0, 0, 705, 527, 278, 356, 4, 776, 947, 0, 0, 0, 859, 584, 81, 86, 303, 38, 0, 0, 0, 0, 990, 288, 166, 954, 743, 0, 0, 0, 0, 0, 244, 663, 503, 191, 0, 0, 0, 0, 0, 0, 849, 676, 423, 0, 0, 0, 0, 0, 0, 0, 915, 477, 0, 0, 0, 0, 0, 0, 0, 0, 370] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_44 :
    (evaluatedRows (45 : F) 1).det = point (45 : F) 1 * quotientValue 1 45 := by
  apply det_of_factors lower1_44 upper1_44
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_45 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 646, 1, 0, 0, 0, 0, 0, 0, 0, 54, 594, 1, 0, 0, 0, 0, 0, 0, 982, 481, 935, 1, 0, 0, 0, 0, 0, 382, 395, 99, 97, 1, 0, 0, 0, 0, 706, 613, 300, 58, 463, 1, 0, 0, 0, 103, 117, 380, 432, 257, 518, 1, 0, 0, 588, 689, 349, 439, 264, 344, 962, 1, 0, 106, 579, 908, 560, 664, 683, 58, 279, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_45 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[817, 697, 596, 899, 785, 385, 0, 783, 234, 0, 632, 610, 536, 630, 279, 226, 700, 571, 0, 0, 387, 215, 270, 932, 728, 628, 331, 0, 0, 0, 585, 795, 369, 661, 467, 432, 0, 0, 0, 0, 339, 560, 986, 87, 363, 0, 0, 0, 0, 0, 407, 260, 744, 486, 0, 0, 0, 0, 0, 0, 863, 334, 233, 0, 0, 0, 0, 0, 0, 0, 1000, 39, 0, 0, 0, 0, 0, 0, 0, 0, 92] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_45 :
    (evaluatedRows (46 : F) 0).det = point (46 : F) 1 * quotientValue 0 46 := by
  apply det_of_factors lower0_45 upper0_45
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_45 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 258, 1, 0, 0, 0, 0, 0, 0, 0, 537, 242, 1, 0, 0, 0, 0, 0, 0, 236, 984, 819, 1, 0, 0, 0, 0, 0, 996, 914, 471, 119, 1, 0, 0, 0, 0, 182, 913, 599, 610, 567, 1, 0, 0, 0, 744, 845, 599, 575, 965, 858, 1, 0, 0, 466, 679, 507, 502, 600, 724, 187, 1, 0, 942, 520, 498, 286, 704, 48, 457, 590, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_45 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[364, 593, 589, 345, 873, 877, 0, 0, 0, 0, 245, 585, 897, 995, 525, 226, 0, 385, 0, 0, 615, 121, 908, 112, 569, 624, 667, 0, 0, 0, 593, 758, 691, 752, 658, 233, 0, 0, 0, 0, 766, 410, 409, 186, 913, 0, 0, 0, 0, 0, 705, 709, 605, 681, 0, 0, 0, 0, 0, 0, 200, 236, 467, 0, 0, 0, 0, 0, 0, 0, 176, 309, 0, 0, 0, 0, 0, 0, 0, 0, 731] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_45 :
    (evaluatedRows (46 : F) 1).det = point (46 : F) 1 * quotientValue 1 46 := by
  apply det_of_factors lower1_45 upper1_45
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_46 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 210, 1, 0, 0, 0, 0, 0, 0, 0, 548, 244, 1, 0, 0, 0, 0, 0, 0, 453, 481, 422, 1, 0, 0, 0, 0, 0, 187, 766, 11, 27, 1, 0, 0, 0, 0, 247, 840, 894, 746, 747, 1, 0, 0, 0, 902, 403, 111, 673, 512, 850, 1, 0, 0, 35, 586, 139, 893, 999, 41, 958, 1, 0, 933, 759, 873, 489, 839, 827, 917, 493, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_46 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[431, 734, 320, 472, 322, 539, 0, 824, 747, 0, 968, 916, 695, 568, 80, 185, 508, 64, 0, 0, 154, 559, 483, 740, 527, 96, 826, 0, 0, 0, 141, 305, 853, 402, 282, 830, 0, 0, 0, 0, 118, 904, 788, 809, 417, 0, 0, 0, 0, 0, 140, 872, 94, 864, 0, 0, 0, 0, 0, 0, 26, 130, 567, 0, 0, 0, 0, 0, 0, 0, 941, 509, 0, 0, 0, 0, 0, 0, 0, 0, 313] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_46 :
    (evaluatedRows (47 : F) 0).det = point (47 : F) 1 * quotientValue 0 47 := by
  apply det_of_factors lower0_46 upper0_46
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_46 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 401, 1, 0, 0, 0, 0, 0, 0, 0, 220, 180, 1, 0, 0, 0, 0, 0, 0, 447, 505, 557, 1, 0, 0, 0, 0, 0, 679, 702, 271, 738, 1, 0, 0, 0, 0, 217, 543, 968, 667, 781, 1, 0, 0, 0, 723, 875, 414, 527, 367, 453, 1, 0, 0, 235, 647, 467, 160, 652, 994, 156, 1, 0, 787, 197, 451, 56, 930, 960, 636, 174, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_46 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[193, 109, 766, 559, 319, 732, 0, 0, 0, 0, 409, 83, 772, 809, 349, 185, 0, 539, 0, 0, 641, 370, 849, 962, 259, 470, 853, 0, 0, 0, 885, 756, 457, 436, 87, 522, 0, 0, 0, 0, 937, 378, 562, 906, 761, 0, 0, 0, 0, 0, 436, 158, 523, 728, 0, 0, 0, 0, 0, 0, 703, 377, 145, 0, 0, 0, 0, 0, 0, 0, 303, 740, 0, 0, 0, 0, 0, 0, 0, 0, 453] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_46 :
    (evaluatedRows (47 : F) 1).det = point (47 : F) 1 * quotientValue 1 47 := by
  apply det_of_factors lower1_46 upper1_46
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
