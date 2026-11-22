/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch24
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBatch24
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Triangular factors certify both tabulated critical cofactor values at line nodes 24 through 29. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant

set_option autoImplicit false
namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

private def lower0_24 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 352, 1, 0, 0, 0, 0, 0, 0, 0, 640, 670, 1, 0, 0, 0, 0, 0, 0, 932, 814, 106, 1, 0, 0, 0, 0, 0, 182, 496, 97, 790, 1, 0, 0, 0, 0, 760, 426, 912, 759, 768, 1, 0, 0, 0, 569, 854, 260, 628, 546, 432, 1, 0, 0, 515, 22, 87, 579, 480, 471, 1007, 1, 0, 567, 20, 491, 924, 246, 843, 935, 546, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_24 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[428, 996, 829, 943, 110, 129, 0, 211, 662, 0, 793, 107, 942, 696, 344, 798, 394, 184, 0, 0, 68, 175, 775, 970, 457, 415, 927, 0, 0, 0, 995, 451, 173, 214, 854, 635, 0, 0, 0, 0, 1000, 464, 644, 599, 477, 0, 0, 0, 0, 0, 139, 396, 558, 195, 0, 0, 0, 0, 0, 0, 863, 29, 314, 0, 0, 0, 0, 0, 0, 0, 980, 62, 0, 0, 0, 0, 0, 0, 0, 0, 8] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_24 :
    (evaluatedRows (24 : F) 0).det = point (24 : F) 1 * quotientValue 0 24 := by
  apply det_of_factors lower0_24 upper0_24
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_24 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 297, 1, 0, 0, 0, 0, 0, 0, 0, 540, 636, 1, 0, 0, 0, 0, 0, 0, 408, 357, 405, 1, 0, 0, 0, 0, 0, 595, 858, 640, 315, 1, 0, 0, 0, 0, 389, 2, 904, 486, 86, 1, 0, 0, 0, 890, 694, 26, 15, 696, 746, 1, 0, 0, 403, 986, 257, 572, 312, 801, 452, 1, 0, 573, 107, 674, 394, 897, 823, 202, 815, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_24 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[582, 91, 82, 481, 726, 452, 0, 0, 0, 0, 469, 176, 329, 369, 300, 798, 0, 129, 0, 0, 124, 20, 572, 210, 346, 880, 694, 0, 0, 0, 429, 245, 546, 782, 985, 737, 0, 0, 0, 0, 393, 232, 229, 190, 653, 0, 0, 0, 0, 0, 842, 783, 210, 452, 0, 0, 0, 0, 0, 0, 981, 361, 887, 0, 0, 0, 0, 0, 0, 0, 760, 887, 0, 0, 0, 0, 0, 0, 0, 0, 728] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_24 :
    (evaluatedRows (24 : F) 1).det = point (24 : F) 1 * quotientValue 1 24 := by
  apply det_of_factors lower1_24 upper1_24
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_25 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 81, 1, 0, 0, 0, 0, 0, 0, 0, 56, 238, 1, 0, 0, 0, 0, 0, 0, 571, 332, 907, 1, 0, 0, 0, 0, 0, 174, 546, 228, 72, 1, 0, 0, 0, 0, 365, 164, 520, 213, 608, 1, 0, 0, 0, 997, 897, 382, 286, 658, 734, 1, 0, 0, 375, 560, 241, 91, 504, 926, 701, 1, 0, 612, 758, 117, 53, 119, 195, 557, 372, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_25 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[78, 719, 805, 223, 30, 976, 0, 576, 745, 0, 246, 648, 166, 598, 919, 433, 767, 162, 0, 0, 529, 686, 199, 637, 128, 148, 444, 0, 0, 0, 781, 138, 683, 470, 203, 407, 0, 0, 0, 0, 695, 507, 950, 432, 742, 0, 0, 0, 0, 0, 888, 785, 59, 591, 0, 0, 0, 0, 0, 0, 344, 783, 155, 0, 0, 0, 0, 0, 0, 0, 880, 35, 0, 0, 0, 0, 0, 0, 0, 0, 370] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_25 :
    (evaluatedRows (25 : F) 0).det = point (25 : F) 1 * quotientValue 0 25 := by
  apply det_of_factors lower0_25 upper0_25
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_25 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 386, 1, 0, 0, 0, 0, 0, 0, 0, 516, 927, 1, 0, 0, 0, 0, 0, 0, 865, 439, 218, 1, 0, 0, 0, 0, 0, 306, 726, 59, 886, 1, 0, 0, 0, 0, 120, 338, 795, 970, 174, 1, 0, 0, 0, 466, 53, 134, 718, 604, 390, 1, 0, 0, 68, 287, 790, 772, 603, 875, 756, 1, 0, 450, 817, 868, 274, 138, 347, 440, 137, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_25 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[994, 564, 223, 169, 699, 620, 0, 0, 0, 0, 203, 964, 418, 599, 77, 433, 0, 976, 0, 0, 355, 763, 131, 769, 455, 33, 321, 0, 0, 0, 653, 607, 837, 306, 449, 432, 0, 0, 0, 0, 632, 427, 863, 543, 888, 0, 0, 0, 0, 0, 577, 248, 246, 975, 0, 0, 0, 0, 0, 0, 156, 989, 851, 0, 0, 0, 0, 0, 0, 0, 994, 1005, 0, 0, 0, 0, 0, 0, 0, 0, 959] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_25 :
    (evaluatedRows (25 : F) 1).det = point (25 : F) 1 * quotientValue 1 25 := by
  apply det_of_factors lower1_25 upper1_25
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_26 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 527, 1, 0, 0, 0, 0, 0, 0, 0, 443, 856, 1, 0, 0, 0, 0, 0, 0, 363, 423, 142, 1, 0, 0, 0, 0, 0, 397, 407, 998, 852, 1, 0, 0, 0, 0, 265, 550, 477, 667, 777, 1, 0, 0, 0, 333, 678, 298, 347, 719, 705, 1, 0, 0, 299, 621, 999, 253, 912, 246, 214, 1, 0, 490, 413, 77, 632, 988, 513, 402, 28, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_26 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[151, 524, 769, 348, 483, 721, 0, 237, 791, 0, 593, 225, 990, 394, 644, 772, 217, 581, 0, 0, 396, 297, 498, 337, 281, 137, 820, 0, 0, 0, 688, 298, 242, 818, 956, 780, 0, 0, 0, 0, 775, 723, 717, 436, 537, 0, 0, 0, 0, 0, 788, 311, 583, 798, 0, 0, 0, 0, 0, 0, 798, 704, 573, 0, 0, 0, 0, 0, 0, 0, 488, 339, 0, 0, 0, 0, 0, 0, 0, 0, 676] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_26 :
    (evaluatedRows (26 : F) 0).det = point (26 : F) 1 * quotientValue 0 26 := by
  apply det_of_factors lower0_26 upper0_26
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_26 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 925, 1, 0, 0, 0, 0, 0, 0, 0, 835, 79, 1, 0, 0, 0, 0, 0, 0, 461, 67, 783, 1, 0, 0, 0, 0, 0, 65, 161, 2, 772, 1, 0, 0, 0, 0, 356, 657, 451, 99, 758, 1, 0, 0, 0, 573, 886, 550, 890, 124, 527, 1, 0, 0, 969, 376, 928, 924, 243, 601, 542, 1, 0, 525, 396, 913, 900, 204, 660, 477, 812, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_26 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[410, 140, 975, 829, 965, 106, 0, 0, 0, 0, 936, 41, 763, 1007, 41, 772, 0, 721, 0, 0, 837, 186, 382, 307, 779, 288, 554, 0, 0, 0, 956, 120, 654, 223, 980, 533, 0, 0, 0, 0, 526, 482, 424, 589, 867, 0, 0, 0, 0, 0, 654, 566, 227, 319, 0, 0, 0, 0, 0, 0, 121, 652, 294, 0, 0, 0, 0, 0, 0, 0, 548, 193, 0, 0, 0, 0, 0, 0, 0, 0, 62] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_26 :
    (evaluatedRows (26 : F) 1).det = point (26 : F) 1 * quotientValue 1 26 := by
  apply det_of_factors lower1_26 upper1_26
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_27 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 53, 1, 0, 0, 0, 0, 0, 0, 0, 286, 784, 1, 0, 0, 0, 0, 0, 0, 835, 222, 772, 1, 0, 0, 0, 0, 0, 724, 632, 660, 509, 1, 0, 0, 0, 0, 881, 77, 225, 562, 52, 1, 0, 0, 0, 665, 789, 184, 35, 364, 987, 1, 0, 0, 998, 159, 545, 463, 819, 472, 61, 1, 0, 693, 451, 700, 891, 444, 771, 510, 421, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_27 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[579, 664, 85, 633, 696, 275, 0, 758, 359, 0, 19, 657, 990, 875, 201, 251, 186, 419, 0, 0, 462, 828, 714, 630, 621, 353, 682, 0, 0, 0, 646, 880, 255, 645, 1004, 483, 0, 0, 0, 0, 479, 268, 563, 713, 414, 0, 0, 0, 0, 0, 870, 315, 900, 644, 0, 0, 0, 0, 0, 0, 908, 190, 760, 0, 0, 0, 0, 0, 0, 0, 127, 280, 0, 0, 0, 0, 0, 0, 0, 0, 252] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_27 :
    (evaluatedRows (27 : F) 0).det = point (27 : F) 1 * quotientValue 0 27 := by
  apply det_of_factors lower0_27 upper0_27
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_27 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 839, 1, 0, 0, 0, 0, 0, 0, 0, 777, 941, 1, 0, 0, 0, 0, 0, 0, 501, 674, 547, 1, 0, 0, 0, 0, 0, 838, 531, 168, 502, 1, 0, 0, 0, 0, 125, 68, 721, 392, 722, 1, 0, 0, 0, 399, 532, 289, 832, 214, 455, 1, 0, 0, 397, 904, 835, 606, 922, 317, 818, 1, 0, 214, 515, 579, 893, 481, 224, 492, 328, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_27 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[965, 498, 138, 314, 862, 266, 0, 0, 0, 0, 809, 370, 136, 665, 465, 251, 0, 275, 0, 0, 717, 852, 894, 253, 565, 734, 538, 0, 0, 0, 172, 786, 229, 37, 375, 210, 0, 0, 0, 0, 131, 532, 789, 710, 437, 0, 0, 0, 0, 0, 930, 624, 378, 259, 0, 0, 0, 0, 0, 0, 626, 513, 711, 0, 0, 0, 0, 0, 0, 0, 714, 820, 0, 0, 0, 0, 0, 0, 0, 0, 993] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_27 :
    (evaluatedRows (27 : F) 1).det = point (27 : F) 1 * quotientValue 1 27 := by
  apply det_of_factors lower1_27 upper1_27
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_28 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 0, 0, 0, 0, 0, 763, 318, 1, 0, 0, 0, 0, 0, 0, 654, 785, 841, 1, 0, 0, 0, 0, 0, 93, 996, 383, 236, 1, 0, 0, 0, 0, 554, 872, 535, 131, 424, 1, 0, 0, 0, 851, 203, 816, 349, 123, 240, 1, 0, 0, 85, 880, 13, 776, 855, 112, 166, 1, 0, 228, 823, 153, 369, 958, 538, 604, 51, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_28 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[842, 87, 802, 558, 934, 344, 0, 973, 180, 0, 637, 636, 604, 196, 118, 36, 180, 453, 0, 0, 978, 545, 235, 650, 480, 154, 117, 0, 0, 0, 15, 887, 98, 921, 410, 227, 0, 0, 0, 0, 658, 241, 112, 674, 725, 0, 0, 0, 0, 0, 239, 823, 86, 128, 0, 0, 0, 0, 0, 0, 838, 175, 240, 0, 0, 0, 0, 0, 0, 0, 198, 364, 0, 0, 0, 0, 0, 0, 0, 0, 409] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_28 :
    (evaluatedRows (28 : F) 0).det = point (28 : F) 1 * quotientValue 0 28 := by
  apply det_of_factors lower0_28 upper0_28
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_28 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 141, 1, 0, 0, 0, 0, 0, 0, 0, 933, 92, 1, 0, 0, 0, 0, 0, 0, 79, 711, 1006, 1, 0, 0, 0, 0, 0, 201, 68, 561, 159, 1, 0, 0, 0, 0, 286, 32, 484, 94, 702, 1, 0, 0, 0, 993, 451, 674, 747, 39, 422, 1, 0, 0, 379, 539, 281, 20, 407, 40, 661, 1, 0, 981, 893, 442, 426, 423, 261, 452, 656, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_28 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[495, 41, 808, 470, 672, 59, 0, 0, 0, 0, 336, 699, 691, 924, 582, 36, 0, 344, 0, 0, 7, 254, 663, 345, 544, 665, 640, 0, 0, 0, 905, 887, 948, 252, 452, 351, 0, 0, 0, 0, 345, 902, 672, 423, 652, 0, 0, 0, 0, 0, 192, 983, 602, 392, 0, 0, 0, 0, 0, 0, 92, 28, 880, 0, 0, 0, 0, 0, 0, 0, 941, 758, 0, 0, 0, 0, 0, 0, 0, 0, 241] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_28 :
    (evaluatedRows (28 : F) 1).det = point (28 : F) 1 * quotientValue 1 28 := by
  apply det_of_factors lower1_28 upper1_28
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower0_29 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 547, 1, 0, 0, 0, 0, 0, 0, 0, 763, 269, 1, 0, 0, 0, 0, 0, 0, 979, 676, 707, 1, 0, 0, 0, 0, 0, 678, 510, 767, 249, 1, 0, 0, 0, 0, 892, 264, 670, 259, 665, 1, 0, 0, 0, 276, 183, 458, 172, 813, 884, 1, 0, 0, 461, 388, 379, 987, 137, 687, 918, 1, 0, 153, 307, 904, 784, 594, 287, 531, 105, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper0_29 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[249, 974, 189, 348, 653, 583, 0, 990, 565, 0, 135, 284, 763, 363, 387, 19, 303, 282, 0, 0, 370, 151, 806, 954, 378, 10, 574, 0, 0, 0, 661, 851, 14, 412, 406, 161, 0, 0, 0, 0, 304, 253, 904, 975, 339, 0, 0, 0, 0, 0, 17, 735, 183, 692, 0, 0, 0, 0, 0, 0, 113, 566, 406, 0, 0, 0, 0, 0, 0, 0, 71, 237, 0, 0, 0, 0, 0, 0, 0, 0, 434] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_0_29 :
    (evaluatedRows (29 : F) 0).det = point (29 : F) 1 * quotientValue 0 29 := by
  apply det_of_factors lower0_29 upper0_29
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def lower1_29 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[1, 0, 0, 0, 0, 0, 0, 0, 0, 405, 1, 0, 0, 0, 0, 0, 0, 0, 386, 397, 1, 0, 0, 0, 0, 0, 0, 367, 386, 786, 1, 0, 0, 0, 0, 0, 585, 707, 334, 601, 1, 0, 0, 0, 0, 725, 724, 561, 630, 875, 1, 0, 0, 0, 256, 30, 1006, 210, 1, 668, 1, 0, 0, 179, 259, 658, 292, 972, 832, 902, 1, 0, 449, 869, 664, 907, 628, 334, 672, 616, 1] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

private def upper1_29 : Matrix (Fin 9) (Fin 9) F :=
  fun i j => ((#[568, 920, 123, 111, 191, 957, 0, 0, 0, 0, 891, 375, 868, 706, 315, 19, 0, 583, 0, 0, 404, 742, 524, 943, 973, 426, 619, 0, 0, 0, 865, 645, 244, 782, 127, 268, 0, 0, 0, 0, 193, 198, 329, 488, 556, 0, 0, 0, 0, 0, 472, 65, 776, 880, 0, 0, 0, 0, 0, 0, 933, 612, 91, 0, 0, 0, 0, 0, 0, 0, 107, 20, 0, 0, 0, 0, 0, 0, 0, 0, 470] : Array ℕ).getD (9 * i.val + j.val) 0 : F)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
theorem cofactor_at_1_29 :
    (evaluatedRows (29 : F) 1).det = point (29 : F) 1 * quotientValue 1 29 := by
  apply det_of_factors lower1_29 upper1_29
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
