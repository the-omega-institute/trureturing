/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch32
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch32
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch32

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower32 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    760, 1, 0, 0, 0, 0, 0, 0, 0;
    149, 410, 1, 0, 0, 0, 0, 0, 0;
    951, 422, 797, 1, 0, 0, 0, 0, 0;
    743, 955, 426, 51, 1, 0, 0, 0, 0;
    132, 764, 47, 1001, 673, 1, 0, 0, 0;
    591, 322, 236, 342, 2, 454, 1, 0, 0;
    889, 136, 475, 763, 202, 843, 476, 1, 0;
    52, 242, 117, 997, 825, 597, 796, 834, 1]

private def firstUpper32 : Matrix (Fin 9) (Fin 9) F :=
  !![560, 301, 587, 724, 334, 610, 646, 860, 922;
    0, 538, 802, 812, 462, 629, 279, 245, 945;
    0, 0, 416, 528, 999, 770, 845, 510, 630;
    0, 0, 0, 380, 463, 728, 439, 565, 992;
    0, 0, 0, 0, 502, 347, 198, 565, 11;
    0, 0, 0, 0, 0, 736, 588, 279, 743;
    0, 0, 0, 0, 0, 0, 620, 63, 301;
    0, 0, 0, 0, 0, 0, 0, 475, 43;
    0, 0, 0, 0, 0, 0, 0, 0, 987]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt32 : residualMinor (32 : F) 0 = firstValue 32 := by
  apply value_of_factors firstLower32 firstUpper32
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower32 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    570, 1, 0, 0, 0, 0, 0, 0, 0;
    588, 58, 1, 0, 0, 0, 0, 0, 0;
    987, 951, 739, 1, 0, 0, 0, 0, 0;
    137, 326, 171, 689, 1, 0, 0, 0, 0;
    153, 193, 806, 330, 465, 1, 0, 0, 0;
    259, 764, 70, 77, 23, 297, 1, 0, 0;
    265, 573, 590, 632, 256, 973, 831, 1, 0;
    58, 417, 950, 568, 570, 414, 927, 540, 1]

private def secondUpper32 : Matrix (Fin 9) (Fin 9) F :=
  !![746, 431, 7, 890, 991, 609, 223, 706, 955;
    0, 781, 990, 365, 204, 55, 889, 184, 920;
    0, 0, 1004, 761, 813, 376, 551, 55, 359;
    0, 0, 0, 457, 476, 1007, 862, 126, 626;
    0, 0, 0, 0, 618, 952, 405, 948, 280;
    0, 0, 0, 0, 0, 48, 727, 144, 379;
    0, 0, 0, 0, 0, 0, 830, 456, 478;
    0, 0, 0, 0, 0, 0, 0, 553, 967;
    0, 0, 0, 0, 0, 0, 0, 0, 133]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt32 : residualMinor (32 : F) 1 = secondValue 32 := by
  apply value_of_factors secondLower32 secondUpper32
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower33 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    275, 1, 0, 0, 0, 0, 0, 0, 0;
    538, 735, 1, 0, 0, 0, 0, 0, 0;
    758, 472, 803, 1, 0, 0, 0, 0, 0;
    314, 956, 231, 369, 1, 0, 0, 0, 0;
    368, 521, 957, 411, 844, 1, 0, 0, 0;
    708, 642, 73, 816, 518, 964, 1, 0, 0;
    488, 346, 593, 877, 181, 799, 938, 1, 0;
    270, 760, 92, 827, 858, 110, 159, 372, 1]

private def firstUpper33 : Matrix (Fin 9) (Fin 9) F :=
  !![471, 442, 115, 5, 95, 626, 300, 365, 373;
    0, 834, 659, 490, 506, 384, 1005, 874, 968;
    0, 0, 732, 849, 749, 398, 514, 891, 119;
    0, 0, 0, 840, 756, 260, 454, 391, 981;
    0, 0, 0, 0, 285, 624, 8, 965, 862;
    0, 0, 0, 0, 0, 85, 45, 218, 389;
    0, 0, 0, 0, 0, 0, 382, 283, 334;
    0, 0, 0, 0, 0, 0, 0, 450, 866;
    0, 0, 0, 0, 0, 0, 0, 0, 834]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt33 : residualMinor (33 : F) 0 = firstValue 33 := by
  apply value_of_factors firstLower33 firstUpper33
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower33 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    621, 1, 0, 0, 0, 0, 0, 0, 0;
    654, 628, 1, 0, 0, 0, 0, 0, 0;
    131, 622, 984, 1, 0, 0, 0, 0, 0;
    495, 908, 707, 193, 1, 0, 0, 0, 0;
    96, 144, 13, 458, 368, 1, 0, 0, 0;
    381, 703, 108, 880, 481, 513, 1, 0, 0;
    900, 314, 948, 525, 438, 654, 564, 1, 0;
    320, 912, 565, 61, 125, 573, 785, 923, 1]

private def secondUpper33 : Matrix (Fin 9) (Fin 9) F :=
  !![875, 761, 270, 749, 876, 90, 812, 849, 438;
    0, 935, 829, 876, 252, 609, 6, 827, 48;
    0, 0, 116, 754, 354, 530, 515, 146, 367;
    0, 0, 0, 906, 599, 944, 655, 115, 350;
    0, 0, 0, 0, 71, 337, 389, 595, 924;
    0, 0, 0, 0, 0, 323, 594, 286, 640;
    0, 0, 0, 0, 0, 0, 168, 106, 891;
    0, 0, 0, 0, 0, 0, 0, 440, 455;
    0, 0, 0, 0, 0, 0, 0, 0, 687]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt33 : residualMinor (33 : F) 1 = secondValue 33 := by
  apply value_of_factors secondLower33 secondUpper33
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower34 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    663, 1, 0, 0, 0, 0, 0, 0, 0;
    59, 794, 1, 0, 0, 0, 0, 0, 0;
    41, 2, 825, 1, 0, 0, 0, 0, 0;
    971, 923, 474, 949, 1, 0, 0, 0, 0;
    886, 773, 368, 224, 752, 1, 0, 0, 0;
    554, 105, 441, 773, 741, 1001, 1, 0, 0;
    591, 831, 713, 695, 132, 203, 860, 1, 0;
    580, 119, 730, 521, 229, 40, 794, 894, 1]

private def firstUpper34 : Matrix (Fin 9) (Fin 9) F :=
  !![227, 225, 199, 983, 779, 224, 324, 212, 921;
    0, 763, 332, 680, 556, 660, 666, 347, 840;
    0, 0, 39, 36, 739, 690, 804, 446, 219;
    0, 0, 0, 159, 780, 993, 287, 381, 615;
    0, 0, 0, 0, 919, 781, 881, 110, 324;
    0, 0, 0, 0, 0, 686, 1002, 888, 262;
    0, 0, 0, 0, 0, 0, 111, 982, 99;
    0, 0, 0, 0, 0, 0, 0, 428, 319;
    0, 0, 0, 0, 0, 0, 0, 0, 290]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt34 : residualMinor (34 : F) 0 = firstValue 34 := by
  apply value_of_factors firstLower34 firstUpper34
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower34 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    16, 1, 0, 0, 0, 0, 0, 0, 0;
    351, 386, 1, 0, 0, 0, 0, 0, 0;
    963, 496, 254, 1, 0, 0, 0, 0, 0;
    741, 971, 705, 37, 1, 0, 0, 0, 0;
    813, 267, 73, 523, 26, 1, 0, 0, 0;
    122, 296, 980, 686, 274, 52, 1, 0, 0;
    27, 117, 906, 247, 893, 93, 656, 1, 0;
    168, 868, 35, 882, 814, 237, 189, 606, 1]

private def secondUpper34 : Matrix (Fin 9) (Fin 9) F :=
  !![114, 87, 224, 527, 741, 155, 79, 745, 744;
    0, 223, 542, 235, 677, 387, 306, 840, 213;
    0, 0, 669, 395, 48, 180, 288, 392, 790;
    0, 0, 0, 963, 674, 82, 841, 715, 106;
    0, 0, 0, 0, 22, 149, 984, 819, 116;
    0, 0, 0, 0, 0, 520, 538, 472, 470;
    0, 0, 0, 0, 0, 0, 886, 973, 407;
    0, 0, 0, 0, 0, 0, 0, 723, 933;
    0, 0, 0, 0, 0, 0, 0, 0, 501]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt34 : residualMinor (34 : F) 1 = secondValue 34 := by
  apply value_of_factors secondLower34 secondUpper34
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower35 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    935, 1, 0, 0, 0, 0, 0, 0, 0;
    401, 221, 1, 0, 0, 0, 0, 0, 0;
    580, 719, 391, 1, 0, 0, 0, 0, 0;
    724, 318, 985, 840, 1, 0, 0, 0, 0;
    305, 394, 966, 344, 623, 1, 0, 0, 0;
    849, 811, 640, 596, 549, 741, 1, 0, 0;
    559, 745, 937, 135, 885, 156, 437, 1, 0;
    385, 957, 414, 632, 93, 666, 127, 920, 1]

private def firstUpper35 : Matrix (Fin 9) (Fin 9) F :=
  !![875, 87, 776, 234, 837, 348, 702, 768, 602;
    0, 965, 733, 88, 473, 784, 914, 940, 979;
    0, 0, 735, 6, 772, 151, 512, 143, 773;
    0, 0, 0, 248, 986, 669, 832, 943, 471;
    0, 0, 0, 0, 627, 153, 230, 897, 783;
    0, 0, 0, 0, 0, 41, 611, 697, 402;
    0, 0, 0, 0, 0, 0, 44, 336, 108;
    0, 0, 0, 0, 0, 0, 0, 171, 365;
    0, 0, 0, 0, 0, 0, 0, 0, 779]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt35 : residualMinor (35 : F) 0 = firstValue 35 := by
  apply value_of_factors firstLower35 firstUpper35
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower35 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    434, 1, 0, 0, 0, 0, 0, 0, 0;
    107, 421, 1, 0, 0, 0, 0, 0, 0;
    946, 571, 812, 1, 0, 0, 0, 0, 0;
    753, 935, 378, 822, 1, 0, 0, 0, 0;
    94, 1001, 774, 929, 440, 1, 0, 0, 0;
    802, 392, 233, 18, 928, 649, 1, 0, 0;
    280, 8, 584, 282, 625, 960, 194, 1, 0;
    330, 224, 735, 731, 439, 678, 621, 616, 1]

private def secondUpper35 : Matrix (Fin 9) (Fin 9) F :=
  !![140, 299, 91, 850, 580, 826, 340, 890, 935;
    0, 976, 679, 319, 614, 977, 179, 799, 655;
    0, 0, 724, 38, 317, 938, 957, 495, 1005;
    0, 0, 0, 762, 968, 712, 850, 709, 617;
    0, 0, 0, 0, 602, 79, 882, 236, 118;
    0, 0, 0, 0, 0, 759, 974, 159, 372;
    0, 0, 0, 0, 0, 0, 809, 637, 781;
    0, 0, 0, 0, 0, 0, 0, 820, 316;
    0, 0, 0, 0, 0, 0, 0, 0, 925]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt35 : residualMinor (35 : F) 1 = secondValue 35 := by
  apply value_of_factors secondLower35 secondUpper35
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower36 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    261, 1, 0, 0, 0, 0, 0, 0, 0;
    871, 12, 1, 0, 0, 0, 0, 0, 0;
    916, 464, 407, 1, 0, 0, 0, 0, 0;
    518, 10, 925, 74, 1, 0, 0, 0, 0;
    25, 960, 734, 404, 21, 1, 0, 0, 0;
    1004, 998, 532, 554, 323, 704, 1, 0, 0;
    275, 425, 871, 98, 959, 28, 985, 1, 0;
    1005, 819, 110, 592, 427, 271, 416, 260, 1]

private def firstUpper36 : Matrix (Fin 9) (Fin 9) F :=
  !![871, 297, 117, 214, 511, 698, 820, 993, 11;
    0, 402, 461, 423, 188, 825, 914, 985, 402;
    0, 0, 195, 746, 55, 753, 19, 122, 502;
    0, 0, 0, 13, 880, 20, 779, 918, 295;
    0, 0, 0, 0, 209, 227, 610, 285, 706;
    0, 0, 0, 0, 0, 534, 314, 147, 198;
    0, 0, 0, 0, 0, 0, 480, 679, 341;
    0, 0, 0, 0, 0, 0, 0, 189, 828;
    0, 0, 0, 0, 0, 0, 0, 0, 926]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt36 : residualMinor (36 : F) 0 = firstValue 36 := by
  apply value_of_factors firstLower36 firstUpper36
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower36 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    89, 1, 0, 0, 0, 0, 0, 0, 0;
    505, 295, 1, 0, 0, 0, 0, 0, 0;
    155, 644, 540, 1, 0, 0, 0, 0, 0;
    238, 342, 976, 673, 1, 0, 0, 0, 0;
    332, 414, 726, 896, 277, 1, 0, 0, 0;
    461, 709, 814, 530, 679, 891, 1, 0, 0;
    352, 474, 183, 996, 344, 478, 301, 1, 0;
    899, 838, 323, 65, 423, 282, 434, 73, 1]

private def secondUpper36 : Matrix (Fin 9) (Fin 9) F :=
  !![322, 488, 257, 362, 642, 1006, 795, 677, 46;
    0, 181, 53, 852, 746, 641, 901, 123, 188;
    0, 0, 556, 226, 985, 188, 424, 229, 793;
    0, 0, 0, 372, 500, 537, 58, 502, 177;
    0, 0, 0, 0, 802, 940, 454, 280, 483;
    0, 0, 0, 0, 0, 56, 178, 518, 310;
    0, 0, 0, 0, 0, 0, 988, 157, 93;
    0, 0, 0, 0, 0, 0, 0, 284, 360;
    0, 0, 0, 0, 0, 0, 0, 0, 336]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt36 : residualMinor (36 : F) 1 = secondValue 36 := by
  apply value_of_factors secondLower36 secondUpper36
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower37 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    587, 1, 0, 0, 0, 0, 0, 0, 0;
    382, 748, 1, 0, 0, 0, 0, 0, 0;
    970, 119, 251, 1, 0, 0, 0, 0, 0;
    384, 742, 216, 475, 1, 0, 0, 0, 0;
    617, 560, 299, 956, 793, 1, 0, 0, 0;
    728, 813, 225, 731, 355, 169, 1, 0, 0;
    83, 543, 181, 187, 382, 119, 263, 1, 0;
    782, 345, 863, 914, 293, 406, 241, 348, 1]

private def firstUpper37 : Matrix (Fin 9) (Fin 9) F :=
  !![118, 528, 199, 182, 502, 301, 230, 327, 481;
    0, 976, 840, 515, 446, 178, 207, 323, 90;
    0, 0, 637, 120, 296, 891, 351, 241, 282;
    0, 0, 0, 777, 274, 739, 843, 752, 468;
    0, 0, 0, 0, 685, 691, 919, 933, 789;
    0, 0, 0, 0, 0, 261, 187, 621, 1003;
    0, 0, 0, 0, 0, 0, 794, 669, 901;
    0, 0, 0, 0, 0, 0, 0, 304, 897;
    0, 0, 0, 0, 0, 0, 0, 0, 898]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt37 : residualMinor (37 : F) 0 = firstValue 37 := by
  apply value_of_factors firstLower37 firstUpper37
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower37 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    284, 1, 0, 0, 0, 0, 0, 0, 0;
    753, 648, 1, 0, 0, 0, 0, 0, 0;
    595, 684, 864, 1, 0, 0, 0, 0, 0;
    449, 228, 823, 494, 1, 0, 0, 0, 0;
    5, 768, 259, 496, 20, 1, 0, 0, 0;
    213, 92, 597, 195, 936, 672, 1, 0, 0;
    630, 662, 942, 596, 877, 906, 548, 1, 0;
    234, 703, 131, 150, 47, 297, 710, 639, 1]

private def secondUpper37 : Matrix (Fin 9) (Fin 9) F :=
  !![17, 780, 938, 400, 847, 904, 37, 3, 362;
    0, 600, 593, 812, 86, 849, 602, 719, 27;
    0, 0, 844, 818, 652, 919, 656, 497, 613;
    0, 0, 0, 551, 30, 187, 32, 399, 966;
    0, 0, 0, 0, 223, 508, 428, 980, 578;
    0, 0, 0, 0, 0, 820, 723, 612, 140;
    0, 0, 0, 0, 0, 0, 611, 623, 300;
    0, 0, 0, 0, 0, 0, 0, 510, 404;
    0, 0, 0, 0, 0, 0, 0, 0, 821]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt37 : residualMinor (37 : F) 1 = secondValue 37 := by
  apply value_of_factors secondLower37 secondUpper37
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower38 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    69, 1, 0, 0, 0, 0, 0, 0, 0;
    160, 378, 1, 0, 0, 0, 0, 0, 0;
    613, 908, 564, 1, 0, 0, 0, 0, 0;
    140, 47, 936, 909, 1, 0, 0, 0, 0;
    712, 592, 383, 51, 701, 1, 0, 0, 0;
    913, 5, 69, 132, 956, 613, 1, 0, 0;
    456, 852, 847, 910, 877, 889, 653, 1, 0;
    977, 742, 352, 824, 1006, 280, 545, 176, 1]

private def firstUpper38 : Matrix (Fin 9) (Fin 9) F :=
  !![58, 503, 136, 55, 208, 516, 725, 444, 711;
    0, 894, 704, 142, 92, 273, 150, 316, 946;
    0, 0, 285, 279, 172, 80, 830, 400, 122;
    0, 0, 0, 466, 118, 704, 92, 776, 623;
    0, 0, 0, 0, 522, 434, 447, 108, 790;
    0, 0, 0, 0, 0, 748, 873, 674, 151;
    0, 0, 0, 0, 0, 0, 699, 710, 484;
    0, 0, 0, 0, 0, 0, 0, 902, 268;
    0, 0, 0, 0, 0, 0, 0, 0, 464]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt38 : residualMinor (38 : F) 0 = firstValue 38 := by
  apply value_of_factors firstLower38 firstUpper38
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower38 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    578, 1, 0, 0, 0, 0, 0, 0, 0;
    413, 858, 1, 0, 0, 0, 0, 0, 0;
    219, 757, 1001, 1, 0, 0, 0, 0, 0;
    1004, 530, 485, 283, 1, 0, 0, 0, 0;
    988, 429, 509, 326, 735, 1, 0, 0, 0;
    781, 396, 997, 593, 272, 433, 1, 0, 0;
    691, 676, 502, 792, 101, 509, 588, 1, 0;
    535, 234, 474, 519, 617, 539, 501, 936, 1]

private def secondUpper38 : Matrix (Fin 9) (Fin 9) F :=
  !![36, 576, 641, 394, 400, 404, 78, 484, 58;
    0, 328, 812, 203, 179, 129, 46, 423, 337;
    0, 0, 740, 307, 687, 119, 948, 383, 966;
    0, 0, 0, 234, 758, 50, 562, 102, 313;
    0, 0, 0, 0, 665, 202, 782, 87, 81;
    0, 0, 0, 0, 0, 738, 345, 157, 36;
    0, 0, 0, 0, 0, 0, 849, 844, 708;
    0, 0, 0, 0, 0, 0, 0, 2, 960;
    0, 0, 0, 0, 0, 0, 0, 0, 88]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt38 : residualMinor (38 : F) 1 = secondValue 38 := by
  apply value_of_factors secondLower38 secondUpper38
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower39 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    928, 1, 0, 0, 0, 0, 0, 0, 0;
    915, 729, 1, 0, 0, 0, 0, 0, 0;
    128, 984, 264, 1, 0, 0, 0, 0, 0;
    249, 831, 469, 970, 1, 0, 0, 0, 0;
    599, 834, 186, 843, 266, 1, 0, 0, 0;
    563, 471, 251, 307, 572, 844, 1, 0, 0;
    932, 344, 36, 867, 885, 8, 579, 1, 0;
    265, 205, 619, 837, 180, 5, 634, 775, 1]

private def firstUpper39 : Matrix (Fin 9) (Fin 9) F :=
  !![561, 198, 26, 933, 844, 774, 936, 183, 885;
    0, 32, 805, 780, 141, 887, 843, 224, 93;
    0, 0, 389, 912, 861, 144, 779, 199, 849;
    0, 0, 0, 993, 522, 900, 828, 589, 892;
    0, 0, 0, 0, 975, 530, 6, 19, 201;
    0, 0, 0, 0, 0, 509, 781, 271, 324;
    0, 0, 0, 0, 0, 0, 864, 661, 946;
    0, 0, 0, 0, 0, 0, 0, 338, 907;
    0, 0, 0, 0, 0, 0, 0, 0, 872]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt39 : residualMinor (39 : F) 0 = firstValue 39 := by
  apply value_of_factors firstLower39 firstUpper39
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower39 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    878, 1, 0, 0, 0, 0, 0, 0, 0;
    23, 389, 1, 0, 0, 0, 0, 0, 0;
    186, 989, 803, 1, 0, 0, 0, 0, 0;
    464, 406, 949, 908, 1, 0, 0, 0, 0;
    840, 996, 914, 61, 952, 1, 0, 0, 0;
    330, 20, 115, 890, 472, 185, 1, 0, 0;
    570, 455, 220, 824, 232, 405, 223, 1, 0;
    878, 987, 885, 529, 793, 619, 918, 713, 1]

private def secondUpper39 : Matrix (Fin 9) (Fin 9) F :=
  !![323, 109, 628, 536, 768, 766, 59, 651, 455;
    0, 291, 247, 468, 97, 197, 359, 52, 121;
    0, 0, 33, 894, 196, 485, 896, 102, 570;
    0, 0, 0, 634, 740, 503, 670, 167, 890;
    0, 0, 0, 0, 937, 877, 126, 892, 406;
    0, 0, 0, 0, 0, 999, 676, 458, 894;
    0, 0, 0, 0, 0, 0, 640, 383, 683;
    0, 0, 0, 0, 0, 0, 0, 661, 704;
    0, 0, 0, 0, 0, 0, 0, 0, 253]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt39 : residualMinor (39 : F) 1 = secondValue 39 := by
  apply value_of_factors secondLower39 secondUpper39
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 32 through 39. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((32 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt32, secondAt32⟩
  · exact ⟨firstAt33, secondAt33⟩
  · exact ⟨firstAt34, secondAt34⟩
  · exact ⟨firstAt35, secondAt35⟩
  · exact ⟨firstAt36, secondAt36⟩
  · exact ⟨firstAt37, secondAt37⟩
  · exact ⟨firstAt38, secondAt38⟩
  · exact ⟨firstAt39, secondAt39⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch32
