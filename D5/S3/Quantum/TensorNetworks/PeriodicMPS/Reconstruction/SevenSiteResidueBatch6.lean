/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch6
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch6
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 6 through 11. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_6 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 971, 1, 0, 0, 0, 0, 0, 0, 0, 328, 882, 1, 0, 0, 0, 0, 0, 0, 976, 863, 440, 1, 0, 0, 0, 0, 0, 870, 920, 496, 975, 1, 0, 0, 0, 0, 912, 173, 786, 425, 984, 1, 0, 0, 0, 253, 233, 168, 391, 123, 941, 1, 0, 0, 799, 451, 820, 622, 744, 917, 633, 1, 0, 577, 521, 139, 574, 562, 104, 535, 895, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_6 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[247, 472, 18, 155, 298, 496, 0, 557, 205, 0, 378, 750, 298, 843, 481, 452, 986, 214, 0, 0, 702, 245, 430, 865, 695, 552, 298, 0, 0, 0, 506, 430, 261, 334, 262, 113, 0, 0, 0, 0, 910, 143, 945, 938, 503, 0, 0, 0, 0, 0, 541, 644, 794, 1005, 0, 0, 0, 0, 0, 0, 186, 379, 802, 0, 0, 0, 0, 0, 0, 0, 275, 322, 0, 0, 0, 0, 0, 0, 0, 0, 323] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_6 :
    (evaluatedRows (6 : F) 0).det = point (6 : F) 1 * quotientValue 0 6 := by
  apply det_of_factors lower0_6 upper0_6
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_6 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 578, 1, 0, 0, 0, 0, 0, 0, 0, 587, 300, 1, 0, 0, 0, 0, 0, 0, 24, 594, 442, 1, 0, 0, 0, 0, 0, 468, 337, 275, 162, 1, 0, 0, 0, 0, 254, 470, 233, 844, 600, 1, 0, 0, 0, 825, 423, 123, 725, 461, 791, 1, 0, 0, 61, 980, 735, 445, 561, 279, 444, 1, 0, 39, 937, 470, 882, 370, 261, 770, 542, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_6 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[291, 544, 950, 701, 984, 727, 0, 0, 0, 0, 980, 871, 902, 942, 342, 452, 0, 496, 0, 0, 506, 119, 663, 933, 410, 513, 532, 0, 0, 0, 342, 825, 309, 306, 364, 353, 0, 0, 0, 0, 198, 483, 624, 493, 738, 0, 0, 0, 0, 0, 91, 565, 317, 239, 0, 0, 0, 0, 0, 0, 138, 163, 636, 0, 0, 0, 0, 0, 0, 0, 487, 308, 0, 0, 0, 0, 0, 0, 0, 0, 776] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_6 :
    (evaluatedRows (6 : F) 1).det = point (6 : F) 1 * quotientValue 1 6 := by
  apply det_of_factors lower1_6 upper1_6
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_7 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 145, 1, 0, 0, 0, 0, 0, 0, 0, 6, 679, 1, 0, 0, 0, 0, 0, 0, 371, 8, 860, 1, 0, 0, 0, 0, 0, 325, 681, 986, 432, 1, 0, 0, 0, 0, 584, 246, 511, 793, 414, 1, 0, 0, 0, 929, 697, 412, 391, 408, 718, 1, 0, 0, 719, 398, 659, 691, 573, 723, 388, 1, 0, 129, 260, 790, 434, 577, 811, 452, 197, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_7 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[298, 715, 318, 192, 247, 907, 0, 505, 901, 0, 886, 93, 853, 129, 772, 504, 432, 423, 0, 0, 796, 810, 949, 600, 952, 390, 996, 0, 0, 0, 548, 425, 825, 592, 278, 599, 0, 0, 0, 0, 96, 191, 685, 584, 251, 0, 0, 0, 0, 0, 597, 587, 530, 266, 0, 0, 0, 0, 0, 0, 135, 357, 493, 0, 0, 0, 0, 0, 0, 0, 18, 57, 0, 0, 0, 0, 0, 0, 0, 0, 26] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_7 :
    (evaluatedRows (7 : F) 0).det = point (7 : F) 1 * quotientValue 0 7 := by
  apply det_of_factors lower0_7 upper0_7
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_7 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 94, 1, 0, 0, 0, 0, 0, 0, 0, 658, 864, 1, 0, 0, 0, 0, 0, 0, 999, 603, 795, 1, 0, 0, 0, 0, 0, 663, 417, 351, 826, 1, 0, 0, 0, 0, 142, 980, 10, 533, 172, 1, 0, 0, 0, 644, 837, 751, 224, 347, 106, 1, 0, 0, 821, 388, 731, 575, 338, 987, 991, 1, 0, 21, 396, 524, 83, 494, 285, 262, 676, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_7 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[245, 558, 352, 169, 765, 11, 0, 0, 0, 0, 650, 1007, 699, 358, 83, 504, 0, 907, 0, 0, 430, 208, 793, 257, 540, 102, 345, 0, 0, 0, 345, 954, 853, 331, 430, 288, 0, 0, 0, 0, 594, 702, 498, 452, 86, 0, 0, 0, 0, 0, 430, 317, 556, 920, 0, 0, 0, 0, 0, 0, 58, 772, 514, 0, 0, 0, 0, 0, 0, 0, 624, 980, 0, 0, 0, 0, 0, 0, 0, 0, 171] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_7 :
    (evaluatedRows (7 : F) 1).det = point (7 : F) 1 * quotientValue 1 7 := by
  apply det_of_factors lower1_7 upper1_7
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_8 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 55, 1, 0, 0, 0, 0, 0, 0, 0, 689, 482, 1, 0, 0, 0, 0, 0, 0, 648, 153, 833, 1, 0, 0, 0, 0, 0, 519, 578, 584, 743, 1, 0, 0, 0, 0, 675, 852, 270, 932, 790, 1, 0, 0, 0, 195, 349, 505, 79, 754, 573, 1, 0, 0, 796, 559, 355, 51, 969, 345, 337, 1, 0, 65, 422, 859, 351, 828, 6, 644, 465, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_8 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[901, 179, 180, 954, 228, 1, 0, 539, 924, 0, 259, 842, 589, 321, 30, 470, 625, 640, 0, 0, 786, 90, 949, 525, 570, 381, 317, 0, 0, 0, 975, 15, 538, 158, 824, 55, 0, 0, 0, 0, 104, 159, 365, 729, 666, 0, 0, 0, 0, 0, 226, 782, 219, 85, 0, 0, 0, 0, 0, 0, 366, 321, 931, 0, 0, 0, 0, 0, 0, 0, 749, 717, 0, 0, 0, 0, 0, 0, 0, 0, 117] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_8 :
    (evaluatedRows (8 : F) 0).det = point (8 : F) 1 * quotientValue 0 8 := by
  apply det_of_factors lower0_8 upper0_8
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_8 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 158, 1, 0, 0, 0, 0, 0, 0, 0, 1007, 767, 1, 0, 0, 0, 0, 0, 0, 559, 212, 437, 1, 0, 0, 0, 0, 0, 60, 520, 850, 457, 1, 0, 0, 0, 0, 288, 453, 139, 284, 920, 1, 0, 0, 0, 285, 875, 730, 344, 286, 32, 1, 0, 0, 232, 502, 939, 172, 373, 466, 539, 1, 0, 95, 477, 582, 560, 801, 788, 309, 246, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_8 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[882, 595, 273, 690, 287, 850, 0, 0, 0, 0, 850, 905, 543, 812, 991, 470, 0, 1, 0, 0, 519, 504, 296, 910, 817, 1008, 242, 0, 0, 0, 622, 780, 904, 408, 727, 199, 0, 0, 0, 0, 408, 584, 593, 861, 24, 0, 0, 0, 0, 0, 316, 805, 855, 32, 0, 0, 0, 0, 0, 0, 40, 707, 169, 0, 0, 0, 0, 0, 0, 0, 275, 588, 0, 0, 0, 0, 0, 0, 0, 0, 340] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_8 :
    (evaluatedRows (8 : F) 1).det = point (8 : F) 1 * quotientValue 1 8 := by
  apply det_of_factors lower1_8 upper1_8
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_9 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 847, 1, 0, 0, 0, 0, 0, 0, 0, 438, 959, 1, 0, 0, 0, 0, 0, 0, 507, 103, 996, 1, 0, 0, 0, 0, 0, 500, 5, 456, 819, 1, 0, 0, 0, 0, 616, 347, 681, 725, 782, 1, 0, 0, 0, 550, 928, 103, 308, 965, 700, 1, 0, 0, 996, 808, 763, 437, 962, 405, 195, 1, 0, 431, 476, 255, 1000, 283, 866, 504, 295, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_9 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[662, 486, 958, 93, 944, 137, 0, 977, 905, 0, 738, 865, 1005, 550, 100, 32, 870, 442, 0, 0, 23, 393, 337, 457, 695, 875, 49, 0, 0, 0, 894, 899, 770, 694, 660, 11, 0, 0, 0, 0, 586, 965, 884, 708, 908, 0, 0, 0, 0, 0, 924, 17, 944, 478, 0, 0, 0, 0, 0, 0, 910, 469, 556, 0, 0, 0, 0, 0, 0, 0, 940, 431, 0, 0, 0, 0, 0, 0, 0, 0, 969] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_9 :
    (evaluatedRows (9 : F) 0).det = point (9 : F) 1 * quotientValue 0 9 := by
  apply det_of_factors lower0_9 upper0_9
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_9 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 906, 1, 0, 0, 0, 0, 0, 0, 0, 129, 682, 1, 0, 0, 0, 0, 0, 0, 640, 642, 51, 1, 0, 0, 0, 0, 0, 866, 252, 66, 350, 1, 0, 0, 0, 0, 292, 48, 447, 366, 80, 1, 0, 0, 0, 549, 326, 463, 430, 815, 764, 1, 0, 0, 708, 901, 829, 45, 342, 62, 1006, 1, 0, 355, 725, 50, 867, 415, 411, 480, 308, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_9 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[42, 147, 787, 326, 715, 760, 0, 0, 0, 0, 714, 387, 346, 978, 691, 32, 0, 137, 0, 0, 830, 416, 408, 751, 478, 872, 403, 0, 0, 0, 190, 622, 239, 483, 37, 709, 0, 0, 0, 0, 747, 992, 649, 446, 115, 0, 0, 0, 0, 0, 701, 947, 16, 339, 0, 0, 0, 0, 0, 0, 587, 741, 852, 0, 0, 0, 0, 0, 0, 0, 80, 218, 0, 0, 0, 0, 0, 0, 0, 0, 129] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_9 :
    (evaluatedRows (9 : F) 1).det = point (9 : F) 1 * quotientValue 1 9 := by
  apply det_of_factors lower1_9 upper1_9
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_10 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 876, 1, 0, 0, 0, 0, 0, 0, 0, 476, 95, 1, 0, 0, 0, 0, 0, 0, 840, 991, 367, 1, 0, 0, 0, 0, 0, 147, 942, 656, 32, 1, 0, 0, 0, 0, 688, 692, 474, 48, 575, 1, 0, 0, 0, 13, 297, 194, 101, 103, 389, 1, 0, 0, 253, 613, 156, 182, 837, 868, 884, 1, 0, 860, 335, 275, 469, 293, 768, 919, 302, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_10 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[749, 989, 810, 121, 49, 764, 0, 767, 260, 0, 688, 475, 49, 757, 452, 242, 102, 29, 0, 0, 733, 919, 500, 790, 966, 811, 619, 0, 0, 0, 1007, 244, 525, 966, 366, 414, 0, 0, 0, 0, 695, 196, 868, 706, 75, 0, 0, 0, 0, 0, 809, 385, 777, 55, 0, 0, 0, 0, 0, 0, 209, 909, 309, 0, 0, 0, 0, 0, 0, 0, 93, 91, 0, 0, 0, 0, 0, 0, 0, 0, 311] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_10 :
    (evaluatedRows (10 : F) 0).det = point (10 : F) 1 * quotientValue 0 10 := by
  apply det_of_factors lower0_10 upper0_10
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_10 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 455, 1, 0, 0, 0, 0, 0, 0, 0, 602, 302, 1, 0, 0, 0, 0, 0, 0, 1003, 118, 391, 1, 0, 0, 0, 0, 0, 453, 600, 963, 93, 1, 0, 0, 0, 0, 514, 244, 426, 592, 725, 1, 0, 0, 0, 699, 223, 430, 918, 720, 417, 1, 0, 0, 409, 298, 230, 864, 787, 384, 407, 1, 0, 138, 999, 187, 311, 542, 575, 651, 883, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_10 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[76, 168, 973, 448, 637, 522, 0, 0, 0, 0, 565, 944, 78, 42, 354, 242, 0, 764, 0, 0, 508, 979, 263, 368, 313, 245, 333, 0, 0, 0, 292, 357, 945, 411, 119, 103, 0, 0, 0, 0, 501, 573, 962, 756, 985, 0, 0, 0, 0, 0, 474, 720, 978, 927, 0, 0, 0, 0, 0, 0, 74, 675, 48, 0, 0, 0, 0, 0, 0, 0, 361, 351, 0, 0, 0, 0, 0, 0, 0, 0, 598] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_10 :
    (evaluatedRows (10 : F) 1).det = point (10 : F) 1 * quotientValue 1 10 := by
  apply det_of_factors lower1_10 upper1_10
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_11 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 414, 1, 0, 0, 0, 0, 0, 0, 0, 639, 410, 1, 0, 0, 0, 0, 0, 0, 885, 689, 535, 1, 0, 0, 0, 0, 0, 500, 923, 525, 165, 1, 0, 0, 0, 0, 588, 15, 851, 71, 479, 1, 0, 0, 0, 994, 295, 500, 409, 182, 630, 1, 0, 0, 695, 361, 415, 87, 220, 543, 172, 1, 0, 1003, 612, 231, 261, 928, 677, 194, 376, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_11 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[128, 283, 350, 918, 391, 631, 0, 665, 34, 0, 716, 204, 236, 17, 63, 344, 147, 681, 0, 0, 423, 307, 494, 451, 186, 502, 755, 0, 0, 0, 236, 26, 929, 480, 194, 907, 0, 0, 0, 0, 482, 575, 37, 328, 22, 0, 0, 0, 0, 0, 645, 139, 636, 775, 0, 0, 0, 0, 0, 0, 722, 241, 692, 0, 0, 0, 0, 0, 0, 0, 829, 381, 0, 0, 0, 0, 0, 0, 0, 0, 429] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_11 :
    (evaluatedRows (11 : F) 0).det = point (11 : F) 1 * quotientValue 0 11 := by
  apply det_of_factors lower0_11 upper0_11
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_11 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 221, 1, 0, 0, 0, 0, 0, 0, 0, 714, 666, 1, 0, 0, 0, 0, 0, 0, 392, 431, 102, 1, 0, 0, 0, 0, 0, 535, 457, 877, 119, 1, 0, 0, 0, 0, 387, 343, 427, 210, 679, 1, 0, 0, 0, 438, 103, 841, 592, 354, 860, 1, 0, 0, 895, 740, 407, 323, 110, 362, 977, 1, 0, 377, 506, 732, 152, 329, 936, 678, 107, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_11 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[742, 8, 778, 729, 688, 786, 0, 0, 0, 0, 75, 409, 226, 762, 817, 344, 0, 631, 0, 0, 471, 539, 204, 194, 914, 378, 507, 0, 0, 0, 108, 111, 571, 668, 817, 281, 0, 0, 0, 0, 752, 712, 981, 352, 381, 0, 0, 0, 0, 0, 742, 549, 221, 818, 0, 0, 0, 0, 0, 0, 530, 733, 194, 0, 0, 0, 0, 0, 0, 0, 107, 924, 0, 0, 0, 0, 0, 0, 0, 0, 23] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_11 :
    (evaluatedRows (11 : F) 1).det = point (11 : F) 1 * quotientValue 1 11 := by
  apply det_of_factors lower1_11 upper1_11
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
