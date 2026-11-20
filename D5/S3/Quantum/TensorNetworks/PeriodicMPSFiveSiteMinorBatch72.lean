/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch72
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch72
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch72

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower72 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    43, 1, 0, 0, 0, 0, 0, 0, 0;
    945, 470, 1, 0, 0, 0, 0, 0, 0;
    603, 666, 463, 1, 0, 0, 0, 0, 0;
    568, 297, 223, 558, 1, 0, 0, 0, 0;
    665, 490, 528, 812, 869, 1, 0, 0, 0;
    650, 30, 320, 986, 124, 599, 1, 0, 0;
    292, 349, 688, 689, 425, 500, 795, 1, 0;
    96, 596, 595, 348, 962, 928, 935, 542, 1]

private def firstUpper72 : Matrix (Fin 9) (Fin 9) F :=
  !![786, 865, 790, 190, 653, 418, 81, 918, 939;
    0, 83, 207, 853, 390, 473, 910, 154, 717;
    0, 0, 492, 261, 647, 455, 29, 557, 575;
    0, 0, 0, 339, 466, 887, 153, 618, 667;
    0, 0, 0, 0, 790, 272, 171, 955, 558;
    0, 0, 0, 0, 0, 755, 161, 781, 972;
    0, 0, 0, 0, 0, 0, 787, 680, 983;
    0, 0, 0, 0, 0, 0, 0, 941, 905;
    0, 0, 0, 0, 0, 0, 0, 0, 495]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt72 : residualMinor (72 : F) 0 = firstValue 72 := by
  apply value_of_factors firstLower72 firstUpper72
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower72 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    677, 1, 0, 0, 0, 0, 0, 0, 0;
    1003, 290, 1, 0, 0, 0, 0, 0, 0;
    6, 758, 317, 1, 0, 0, 0, 0, 0;
    394, 658, 31, 42, 1, 0, 0, 0, 0;
    872, 108, 702, 223, 701, 1, 0, 0, 0;
    825, 188, 183, 162, 291, 142, 1, 0, 0;
    7, 260, 937, 862, 243, 356, 107, 1, 0;
    973, 795, 166, 201, 247, 599, 978, 529, 1]

private def secondUpper72 : Matrix (Fin 9) (Fin 9) F :=
  !![884, 223, 134, 441, 778, 662, 344, 1001, 613;
    0, 324, 972, 49, 209, 107, 548, 648, 432;
    0, 0, 234, 81, 448, 452, 322, 774, 481;
    0, 0, 0, 806, 642, 357, 638, 549, 649;
    0, 0, 0, 0, 300, 876, 508, 839, 266;
    0, 0, 0, 0, 0, 582, 132, 722, 373;
    0, 0, 0, 0, 0, 0, 26, 911, 615;
    0, 0, 0, 0, 0, 0, 0, 608, 818;
    0, 0, 0, 0, 0, 0, 0, 0, 48]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt72 : residualMinor (72 : F) 1 = secondValue 72 := by
  apply value_of_factors secondLower72 secondUpper72
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower73 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    722, 1, 0, 0, 0, 0, 0, 0, 0;
    862, 129, 1, 0, 0, 0, 0, 0, 0;
    864, 586, 344, 1, 0, 0, 0, 0, 0;
    994, 271, 870, 157, 1, 0, 0, 0, 0;
    210, 621, 376, 356, 703, 1, 0, 0, 0;
    608, 474, 200, 887, 933, 502, 1, 0, 0;
    363, 569, 268, 784, 586, 719, 680, 1, 0;
    70, 395, 351, 416, 795, 419, 309, 654, 1]

private def firstUpper73 : Matrix (Fin 9) (Fin 9) F :=
  !![607, 406, 774, 417, 930, 523, 169, 338, 40;
    0, 985, 747, 190, 239, 240, 795, 20, 808;
    0, 0, 826, 767, 970, 588, 672, 496, 197;
    0, 0, 0, 550, 428, 834, 66, 345, 685;
    0, 0, 0, 0, 183, 154, 297, 155, 30;
    0, 0, 0, 0, 0, 468, 705, 412, 506;
    0, 0, 0, 0, 0, 0, 988, 795, 519;
    0, 0, 0, 0, 0, 0, 0, 871, 85;
    0, 0, 0, 0, 0, 0, 0, 0, 1007]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt73 : residualMinor (73 : F) 0 = firstValue 73 := by
  apply value_of_factors firstLower73 firstUpper73
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower73 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    333, 1, 0, 0, 0, 0, 0, 0, 0;
    836, 280, 1, 0, 0, 0, 0, 0, 0;
    349, 38, 202, 1, 0, 0, 0, 0, 0;
    264, 892, 299, 909, 1, 0, 0, 0, 0;
    134, 151, 620, 236, 900, 1, 0, 0, 0;
    209, 598, 254, 82, 192, 817, 1, 0, 0;
    643, 646, 381, 654, 569, 501, 145, 1, 0;
    273, 896, 856, 408, 206, 223, 580, 351, 1]

private def secondUpper73 : Matrix (Fin 9) (Fin 9) F :=
  !![23, 118, 860, 795, 820, 177, 529, 130, 65;
    0, 555, 765, 205, 84, 61, 133, 984, 980;
    0, 0, 729, 726, 314, 496, 482, 33, 870;
    0, 0, 0, 420, 638, 710, 122, 864, 803;
    0, 0, 0, 0, 898, 759, 273, 798, 304;
    0, 0, 0, 0, 0, 210, 425, 943, 261;
    0, 0, 0, 0, 0, 0, 162, 723, 179;
    0, 0, 0, 0, 0, 0, 0, 483, 875;
    0, 0, 0, 0, 0, 0, 0, 0, 189]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt73 : residualMinor (73 : F) 1 = secondValue 73 := by
  apply value_of_factors secondLower73 secondUpper73
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower74 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    150, 1, 0, 0, 0, 0, 0, 0, 0;
    172, 358, 1, 0, 0, 0, 0, 0, 0;
    96, 340, 226, 1, 0, 0, 0, 0, 0;
    976, 780, 384, 694, 1, 0, 0, 0, 0;
    110, 935, 352, 524, 933, 1, 0, 0, 0;
    786, 631, 984, 444, 368, 15, 1, 0, 0;
    79, 557, 812, 10, 562, 123, 1003, 1, 0;
    42, 853, 452, 523, 545, 554, 531, 54, 1]

private def firstUpper74 : Matrix (Fin 9) (Fin 9) F :=
  !![63, 352, 908, 901, 100, 304, 873, 601, 725;
    0, 792, 825, 679, 200, 990, 540, 415, 112;
    0, 0, 473, 481, 651, 999, 740, 88, 271;
    0, 0, 0, 777, 488, 379, 439, 626, 356;
    0, 0, 0, 0, 322, 536, 365, 589, 480;
    0, 0, 0, 0, 0, 292, 599, 740, 23;
    0, 0, 0, 0, 0, 0, 468, 907, 977;
    0, 0, 0, 0, 0, 0, 0, 749, 957;
    0, 0, 0, 0, 0, 0, 0, 0, 911]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt74 : residualMinor (74 : F) 0 = firstValue 74 := by
  apply value_of_factors firstLower74 firstUpper74
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower74 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    859, 1, 0, 0, 0, 0, 0, 0, 0;
    101, 680, 1, 0, 0, 0, 0, 0, 0;
    801, 440, 190, 1, 0, 0, 0, 0, 0;
    154, 745, 9, 868, 1, 0, 0, 0, 0;
    594, 1006, 81, 465, 902, 1, 0, 0, 0;
    539, 550, 285, 762, 128, 600, 1, 0, 0;
    703, 63, 210, 208, 966, 255, 8, 1, 0;
    923, 740, 638, 554, 449, 110, 838, 195, 1]

private def secondUpper74 : Matrix (Fin 9) (Fin 9) F :=
  !![653, 586, 17, 250, 555, 582, 984, 710, 890;
    0, 232, 333, 790, 577, 702, 606, 310, 202;
    0, 0, 853, 552, 240, 717, 246, 799, 375;
    0, 0, 0, 125, 814, 498, 472, 78, 544;
    0, 0, 0, 0, 942, 825, 972, 321, 31;
    0, 0, 0, 0, 0, 681, 138, 148, 252;
    0, 0, 0, 0, 0, 0, 818, 131, 47;
    0, 0, 0, 0, 0, 0, 0, 631, 883;
    0, 0, 0, 0, 0, 0, 0, 0, 927]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt74 : residualMinor (74 : F) 1 = secondValue 74 := by
  apply value_of_factors secondLower74 secondUpper74
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower75 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    823, 1, 0, 0, 0, 0, 0, 0, 0;
    539, 806, 1, 0, 0, 0, 0, 0, 0;
    897, 626, 537, 1, 0, 0, 0, 0, 0;
    849, 361, 810, 914, 1, 0, 0, 0, 0;
    636, 98, 105, 705, 745, 1, 0, 0, 0;
    556, 640, 745, 342, 892, 123, 1, 0, 0;
    870, 986, 955, 139, 656, 94, 713, 1, 0;
    103, 242, 668, 632, 957, 848, 788, 711, 1]

private def firstUpper75 : Matrix (Fin 9) (Fin 9) F :=
  !![632, 571, 269, 93, 925, 947, 629, 114, 973;
    0, 364, 19, 645, 39, 522, 603, 453, 190;
    0, 0, 473, 90, 277, 795, 29, 619, 968;
    0, 0, 0, 607, 576, 414, 95, 660, 427;
    0, 0, 0, 0, 642, 183, 990, 962, 860;
    0, 0, 0, 0, 0, 45, 891, 181, 887;
    0, 0, 0, 0, 0, 0, 332, 426, 500;
    0, 0, 0, 0, 0, 0, 0, 10, 428;
    0, 0, 0, 0, 0, 0, 0, 0, 352]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt75 : residualMinor (75 : F) 0 = firstValue 75 := by
  apply value_of_factors firstLower75 firstUpper75
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower75 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    633, 1, 0, 0, 0, 0, 0, 0, 0;
    223, 749, 1, 0, 0, 0, 0, 0, 0;
    53, 240, 809, 1, 0, 0, 0, 0, 0;
    517, 104, 266, 863, 1, 0, 0, 0, 0;
    975, 981, 894, 512, 91, 1, 0, 0, 0;
    545, 441, 963, 231, 141, 982, 1, 0, 0;
    131, 556, 570, 173, 686, 362, 155, 1, 0;
    463, 197, 114, 500, 586, 347, 949, 806, 1]

private def secondUpper75 : Matrix (Fin 9) (Fin 9) F :=
  !![351, 4, 796, 372, 745, 362, 88, 552, 984;
    0, 598, 58, 121, 146, 852, 444, 136, 513;
    0, 0, 368, 974, 529, 187, 686, 423, 220;
    0, 0, 0, 88, 514, 658, 569, 997, 380;
    0, 0, 0, 0, 186, 617, 955, 626, 346;
    0, 0, 0, 0, 0, 401, 914, 115, 149;
    0, 0, 0, 0, 0, 0, 267, 878, 1004;
    0, 0, 0, 0, 0, 0, 0, 864, 355;
    0, 0, 0, 0, 0, 0, 0, 0, 876]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt75 : residualMinor (75 : F) 1 = secondValue 75 := by
  apply value_of_factors secondLower75 secondUpper75
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 72 through 75. -/
theorem pointValues (t : Fin 4) :
    let q : F := ((72 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt72, secondAt72⟩
  · exact ⟨firstAt73, secondAt73⟩
  · exact ⟨firstAt74, secondAt74⟩
  · exact ⟨firstAt75, secondAt75⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch72
