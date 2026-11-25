/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch18
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch18
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 18 through 23. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_18 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 131, 1, 0, 0, 0, 0, 0, 0, 0, 99, 922, 1, 0, 0, 0, 0, 0, 0, 922, 878, 633, 1, 0, 0, 0, 0, 0, 211, 957, 944, 844, 1, 0, 0, 0, 0, 994, 379, 971, 41, 143, 1, 0, 0, 0, 925, 834, 913, 582, 174, 1, 1, 0, 0, 617, 599, 516, 85, 626, 862, 6, 1, 0, 832, 457, 153, 930, 183, 175, 237, 56, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_18 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[463, 969, 712, 574, 498, 889, 0, 9, 323, 0, 818, 710, 67, 310, 262, 1000, 839, 954, 0, 0, 864, 169, 333, 377, 912, 583, 571, 0, 0, 0, 587, 485, 502, 691, 864, 304, 0, 0, 0, 0, 504, 574, 339, 706, 32, 0, 0, 0, 0, 0, 205, 201, 684, 585, 0, 0, 0, 0, 0, 0, 990, 953, 423, 0, 0, 0, 0, 0, 0, 0, 872, 332, 0, 0, 0, 0, 0, 0, 0, 0, 748] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_18 :
    (evaluatedRows (18 : F) 0).det = point (18 : F) 1 * quotientValue 0 18 := by
  apply det_of_factors lower0_18 upper0_18
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_18 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 475, 1, 0, 0, 0, 0, 0, 0, 0, 798, 940, 1, 0, 0, 0, 0, 0, 0, 216, 910, 864, 1, 0, 0, 0, 0, 0, 172, 424, 983, 557, 1, 0, 0, 0, 0, 246, 712, 189, 828, 931, 1, 0, 0, 0, 974, 548, 713, 434, 716, 536, 1, 0, 0, 173, 574, 996, 732, 24, 303, 377, 1, 0, 683, 205, 875, 410, 221, 250, 30, 94, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_18 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[304, 70, 117, 869, 755, 340, 0, 0, 0, 0, 670, 65, 501, 542, 626, 1000, 0, 889, 0, 0, 412, 700, 415, 926, 65, 120, 801, 0, 0, 0, 136, 398, 50, 462, 145, 147, 0, 0, 0, 0, 430, 847, 473, 550, 840, 0, 0, 0, 0, 0, 315, 213, 957, 451, 0, 0, 0, 0, 0, 0, 449, 172, 464, 0, 0, 0, 0, 0, 0, 0, 26, 110, 0, 0, 0, 0, 0, 0, 0, 0, 255] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_18 :
    (evaluatedRows (18 : F) 1).det = point (18 : F) 1 * quotientValue 1 18 := by
  apply det_of_factors lower1_18 upper1_18
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_19 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 76, 1, 0, 0, 0, 0, 0, 0, 0, 405, 110, 1, 0, 0, 0, 0, 0, 0, 703, 254, 819, 1, 0, 0, 0, 0, 0, 716, 17, 600, 154, 1, 0, 0, 0, 0, 739, 941, 365, 455, 948, 1, 0, 0, 0, 476, 765, 840, 542, 828, 546, 1, 0, 0, 446, 371, 115, 54, 969, 348, 791, 1, 0, 856, 272, 898, 200, 159, 353, 678, 673, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_19 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[361, 585, 300, 852, 909, 372, 0, 169, 146, 0, 154, 51, 227, 273, 843, 840, 273, 375, 0, 0, 651, 896, 590, 957, 282, 35, 520, 0, 0, 0, 49, 657, 409, 651, 263, 126, 0, 0, 0, 0, 216, 155, 733, 93, 287, 0, 0, 0, 0, 0, 175, 187, 681, 198, 0, 0, 0, 0, 0, 0, 836, 53, 234, 0, 0, 0, 0, 0, 0, 0, 285, 289, 0, 0, 0, 0, 0, 0, 0, 0, 790] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_19 :
    (evaluatedRows (19 : F) 0).det = point (19 : F) 1 * quotientValue 0 19 := by
  apply det_of_factors lower0_19 upper0_19
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_19 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 1002, 1, 0, 0, 0, 0, 0, 0, 0, 746, 458, 1, 0, 0, 0, 0, 0, 0, 692, 9, 699, 1, 0, 0, 0, 0, 0, 412, 477, 314, 319, 1, 0, 0, 0, 0, 848, 659, 17, 825, 65, 1, 0, 0, 0, 381, 290, 673, 150, 107, 592, 1, 0, 0, 251, 881, 146, 487, 300, 896, 420, 1, 0, 346, 682, 610, 376, 530, 345, 679, 364, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_19 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[549, 773, 553, 221, 238, 717, 0, 0, 0, 0, 584, 488, 941, 393, 837, 840, 0, 372, 0, 0, 255, 89, 863, 131, 572, 637, 145, 0, 0, 0, 471, 13, 642, 248, 857, 565, 0, 0, 0, 0, 328, 646, 415, 395, 42, 0, 0, 0, 0, 0, 67, 67, 800, 356, 0, 0, 0, 0, 0, 0, 730, 460, 725, 0, 0, 0, 0, 0, 0, 0, 30, 179, 0, 0, 0, 0, 0, 0, 0, 0, 109] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_19 :
    (evaluatedRows (19 : F) 1).det = point (19 : F) 1 * quotientValue 1 19 := by
  apply det_of_factors lower1_19 upper1_19
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_20 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 276, 1, 0, 0, 0, 0, 0, 0, 0, 543, 5, 1, 0, 0, 0, 0, 0, 0, 437, 50, 358, 1, 0, 0, 0, 0, 0, 79, 42, 998, 104, 1, 0, 0, 0, 0, 672, 708, 389, 157, 80, 1, 0, 0, 0, 888, 532, 870, 132, 342, 333, 1, 0, 0, 892, 590, 380, 593, 208, 119, 574, 1, 0, 13, 297, 552, 314, 95, 352, 851, 524, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_20 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[78, 761, 860, 277, 551, 840, 0, 16, 534, 0, 804, 255, 102, 36, 705, 993, 629, 770, 0, 0, 311, 897, 670, 475, 555, 444, 816, 0, 0, 0, 705, 32, 53, 883, 26, 765, 0, 0, 0, 0, 877, 247, 882, 505, 111, 0, 0, 0, 0, 0, 746, 581, 602, 861, 0, 0, 0, 0, 0, 0, 127, 194, 900, 0, 0, 0, 0, 0, 0, 0, 456, 172, 0, 0, 0, 0, 0, 0, 0, 0, 783] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_20 :
    (evaluatedRows (20 : F) 0).det = point (20 : F) 1 * quotientValue 0 20 := by
  apply det_of_factors lower0_20 upper0_20
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_20 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 485, 1, 0, 0, 0, 0, 0, 0, 0, 680, 101, 1, 0, 0, 0, 0, 0, 0, 852, 382, 903, 1, 0, 0, 0, 0, 0, 976, 773, 812, 854, 1, 0, 0, 0, 0, 128, 75, 696, 595, 138, 1, 0, 0, 0, 25, 53, 25, 951, 512, 774, 1, 0, 0, 266, 283, 361, 534, 686, 466, 30, 1, 0, 531, 591, 13, 379, 873, 460, 353, 851, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_20 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[914, 577, 499, 306, 972, 578, 0, 0, 0, 0, 616, 645, 792, 545, 647, 993, 0, 840, 0, 0, 534, 970, 755, 724, 73, 169, 925, 0, 0, 0, 661, 405, 377, 733, 417, 879, 0, 0, 0, 0, 392, 148, 285, 837, 27, 0, 0, 0, 0, 0, 452, 256, 929, 703, 0, 0, 0, 0, 0, 0, 627, 433, 810, 0, 0, 0, 0, 0, 0, 0, 215, 977, 0, 0, 0, 0, 0, 0, 0, 0, 660] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_20 :
    (evaluatedRows (20 : F) 1).det = point (20 : F) 1 * quotientValue 1 20 := by
  apply det_of_factors lower1_20 upper1_20
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_21 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 106, 1, 0, 0, 0, 0, 0, 0, 0, 570, 347, 1, 0, 0, 0, 0, 0, 0, 55, 927, 572, 1, 0, 0, 0, 0, 0, 179, 526, 885, 64, 1, 0, 0, 0, 0, 863, 272, 633, 401, 665, 1, 0, 0, 0, 463, 914, 41, 186, 746, 364, 1, 0, 0, 784, 435, 362, 987, 783, 464, 600, 1, 0, 778, 978, 122, 999, 488, 803, 214, 967, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_21 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[87, 951, 411, 273, 50, 660, 0, 911, 729, 0, 417, 678, 651, 995, 950, 98, 298, 70, 0, 0, 555, 221, 68, 352, 580, 226, 104, 0, 0, 0, 263, 276, 633, 165, 844, 206, 0, 0, 0, 0, 860, 680, 27, 5, 441, 0, 0, 0, 0, 0, 544, 244, 861, 123, 0, 0, 0, 0, 0, 0, 805, 963, 242, 0, 0, 0, 0, 0, 0, 0, 637, 575, 0, 0, 0, 0, 0, 0, 0, 0, 955] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_21 :
    (evaluatedRows (21 : F) 0).det = point (21 : F) 1 * quotientValue 0 21 := by
  apply det_of_factors lower0_21 upper0_21
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_21 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 240, 1, 0, 0, 0, 0, 0, 0, 0, 1005, 221, 1, 0, 0, 0, 0, 0, 0, 867, 546, 104, 1, 0, 0, 0, 0, 0, 767, 366, 672, 493, 1, 0, 0, 0, 0, 964, 332, 679, 534, 843, 1, 0, 0, 0, 896, 794, 32, 941, 997, 688, 1, 0, 0, 214, 220, 434, 491, 950, 248, 975, 1, 0, 1000, 442, 795, 263, 383, 738, 162, 500, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_21 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[215, 827, 57, 33, 907, 999, 0, 0, 0, 0, 616, 294, 480, 505, 662, 98, 0, 660, 0, 0, 736, 323, 489, 874, 820, 349, 445, 0, 0, 0, 131, 664, 228, 454, 427, 199, 0, 0, 0, 0, 827, 883, 811, 666, 536, 0, 0, 0, 0, 0, 888, 996, 603, 514, 0, 0, 0, 0, 0, 0, 528, 470, 625, 0, 0, 0, 0, 0, 0, 0, 781, 621, 0, 0, 0, 0, 0, 0, 0, 0, 918] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_21 :
    (evaluatedRows (21 : F) 1).det = point (21 : F) 1 * quotientValue 1 21 := by
  apply det_of_factors lower1_21 upper1_21
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_22 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 20, 1, 0, 0, 0, 0, 0, 0, 0, 845, 283, 1, 0, 0, 0, 0, 0, 0, 827, 971, 680, 1, 0, 0, 0, 0, 0, 4, 859, 648, 911, 1, 0, 0, 0, 0, 942, 910, 794, 1001, 724, 1, 0, 0, 0, 191, 277, 960, 516, 385, 179, 1, 0, 0, 279, 462, 694, 4, 772, 281, 462, 1, 0, 48, 833, 790, 511, 31, 672, 733, 465, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_22 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[741, 328, 51, 967, 44, 850, 0, 959, 813, 0, 842, 372, 965, 632, 349, 50, 1000, 734, 0, 0, 152, 388, 391, 223, 172, 560, 276, 0, 0, 0, 246, 174, 653, 975, 236, 321, 0, 0, 0, 0, 944, 206, 173, 384, 513, 0, 0, 0, 0, 0, 64, 640, 813, 18, 0, 0, 0, 0, 0, 0, 990, 697, 879, 0, 0, 0, 0, 0, 0, 0, 1003, 515, 0, 0, 0, 0, 0, 0, 0, 0, 45] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_22 :
    (evaluatedRows (22 : F) 0).det = point (22 : F) 1 * quotientValue 0 22 := by
  apply det_of_factors lower0_22 upper0_22
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_22 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 409, 1, 0, 0, 0, 0, 0, 0, 0, 884, 427, 1, 0, 0, 0, 0, 0, 0, 415, 552, 502, 1, 0, 0, 0, 0, 0, 889, 441, 494, 475, 1, 0, 0, 0, 0, 1001, 932, 5, 980, 188, 1, 0, 0, 0, 324, 850, 466, 854, 756, 895, 1, 0, 0, 711, 581, 116, 65, 682, 218, 537, 1, 0, 578, 268, 196, 820, 20, 552, 609, 333, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_22 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[278, 835, 510, 58, 454, 733, 0, 0, 0, 0, 875, 656, 619, 473, 72, 50, 0, 850, 0, 0, 773, 101, 576, 291, 35, 159, 290, 0, 0, 0, 220, 881, 828, 235, 897, 745, 0, 0, 0, 0, 885, 934, 892, 123, 486, 0, 0, 0, 0, 0, 135, 685, 427, 47, 0, 0, 0, 0, 0, 0, 391, 451, 597, 0, 0, 0, 0, 0, 0, 0, 33, 343, 0, 0, 0, 0, 0, 0, 0, 0, 577] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_22 :
    (evaluatedRows (22 : F) 1).det = point (22 : F) 1 * quotientValue 1 22 := by
  apply det_of_factors lower1_22 upper1_22
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_23 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 533, 1, 0, 0, 0, 0, 0, 0, 0, 868, 61, 1, 0, 0, 0, 0, 0, 0, 418, 323, 220, 1, 0, 0, 0, 0, 0, 742, 631, 295, 594, 1, 0, 0, 0, 0, 470, 120, 510, 949, 974, 1, 0, 0, 0, 498, 159, 812, 651, 61, 990, 1, 0, 0, 763, 10, 536, 1004, 193, 498, 475, 1, 0, 747, 521, 737, 622, 816, 262, 185, 578, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_23 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[536, 304, 528, 760, 345, 543, 0, 83, 922, 0, 686, 543, 122, 531, 251, 926, 157, 500, 0, 0, 549, 58, 92, 795, 105, 574, 620, 0, 0, 0, 805, 304, 972, 682, 1000, 877, 0, 0, 0, 0, 896, 538, 826, 986, 358, 0, 0, 0, 0, 0, 744, 475, 374, 536, 0, 0, 0, 0, 0, 0, 130, 609, 751, 0, 0, 0, 0, 0, 0, 0, 368, 151, 0, 0, 0, 0, 0, 0, 0, 0, 851] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_23 :
    (evaluatedRows (23 : F) 0).det = point (23 : F) 1 * quotientValue 0 23 := by
  apply det_of_factors lower0_23 upper0_23
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_23 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 523, 1, 0, 0, 0, 0, 0, 0, 0, 174, 467, 1, 0, 0, 0, 0, 0, 0, 944, 331, 215, 1, 0, 0, 0, 0, 0, 995, 357, 499, 550, 1, 0, 0, 0, 0, 429, 404, 695, 702, 847, 1, 0, 0, 0, 695, 771, 869, 298, 614, 654, 1, 0, 0, 690, 384, 795, 831, 494, 234, 65, 1, 0, 538, 61, 669, 391, 807, 445, 169, 161, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_23 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[853, 868, 131, 804, 46, 33, 0, 0, 0, 0, 355, 555, 854, 936, 990, 926, 0, 543, 0, 0, 125, 323, 844, 187, 506, 466, 687, 0, 0, 0, 162, 340, 116, 412, 496, 558, 0, 0, 0, 0, 268, 942, 658, 900, 588, 0, 0, 0, 0, 0, 204, 167, 604, 852, 0, 0, 0, 0, 0, 0, 868, 5, 487, 0, 0, 0, 0, 0, 0, 0, 846, 548, 0, 0, 0, 0, 0, 0, 0, 0, 389] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_23 :
    (evaluatedRows (23 : F) 1).det = point (23 : F) 1 * quotientValue 1 23 := by
  apply det_of_factors lower1_23 upper1_23
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
