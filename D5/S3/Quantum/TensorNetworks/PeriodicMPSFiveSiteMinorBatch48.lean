/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch48
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch48
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch48

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower48 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    398, 1, 0, 0, 0, 0, 0, 0, 0;
    290, 166, 1, 0, 0, 0, 0, 0, 0;
    911, 246, 754, 1, 0, 0, 0, 0, 0;
    358, 803, 957, 373, 1, 0, 0, 0, 0;
    267, 106, 118, 138, 288, 1, 0, 0, 0;
    493, 799, 467, 750, 898, 139, 1, 0, 0;
    0, 568, 998, 82, 725, 928, 15, 1, 0;
    287, 548, 781, 223, 679, 420, 410, 354, 1]

private def firstUpper48 : Matrix (Fin 9) (Fin 9) F :=
  !![429, 508, 956, 680, 360, 1006, 167, 862, 975;
    0, 122, 657, 239, 34, 475, 142, 599, 893;
    0, 0, 689, 503, 588, 531, 198, 99, 407;
    0, 0, 0, 509, 702, 774, 88, 766, 724;
    0, 0, 0, 0, 988, 401, 348, 669, 314;
    0, 0, 0, 0, 0, 691, 812, 607, 605;
    0, 0, 0, 0, 0, 0, 290, 373, 673;
    0, 0, 0, 0, 0, 0, 0, 953, 238;
    0, 0, 0, 0, 0, 0, 0, 0, 163]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt48 : residualMinor (48 : F) 0 = firstValue 48 := by
  apply value_of_factors firstLower48 firstUpper48
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower48 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    125, 1, 0, 0, 0, 0, 0, 0, 0;
    309, 73, 1, 0, 0, 0, 0, 0, 0;
    196, 416, 422, 1, 0, 0, 0, 0, 0;
    54, 247, 321, 709, 1, 0, 0, 0, 0;
    279, 12, 882, 566, 721, 1, 0, 0, 0;
    363, 799, 343, 749, 145, 159, 1, 0, 0;
    299, 906, 820, 655, 314, 444, 353, 1, 0;
    484, 453, 876, 758, 54, 440, 905, 946, 1]

private def secondUpper48 : Matrix (Fin 9) (Fin 9) F :=
  !![214, 413, 114, 333, 232, 360, 494, 994, 902;
    0, 340, 628, 211, 297, 695, 822, 472, 736;
    0, 0, 194, 15, 110, 283, 808, 848, 67;
    0, 0, 0, 661, 903, 844, 657, 712, 199;
    0, 0, 0, 0, 346, 631, 565, 458, 7;
    0, 0, 0, 0, 0, 689, 491, 531, 298;
    0, 0, 0, 0, 0, 0, 379, 439, 749;
    0, 0, 0, 0, 0, 0, 0, 327, 254;
    0, 0, 0, 0, 0, 0, 0, 0, 608]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt48 : residualMinor (48 : F) 1 = secondValue 48 := by
  apply value_of_factors secondLower48 secondUpper48
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower49 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    290, 1, 0, 0, 0, 0, 0, 0, 0;
    962, 457, 1, 0, 0, 0, 0, 0, 0;
    233, 994, 835, 1, 0, 0, 0, 0, 0;
    836, 276, 733, 592, 1, 0, 0, 0, 0;
    854, 671, 498, 538, 733, 1, 0, 0, 0;
    774, 776, 938, 369, 82, 780, 1, 0, 0;
    878, 569, 569, 352, 883, 435, 933, 1, 0;
    261, 33, 497, 59, 252, 574, 113, 616, 1]

private def firstUpper49 : Matrix (Fin 9) (Fin 9) F :=
  !![907, 1002, 908, 603, 520, 313, 178, 967, 444;
    0, 391, 829, 259, 78, 252, 944, 997, 504;
    0, 0, 987, 463, 860, 878, 544, 991, 411;
    0, 0, 0, 350, 907, 722, 364, 58, 443;
    0, 0, 0, 0, 962, 878, 430, 656, 923;
    0, 0, 0, 0, 0, 393, 652, 477, 537;
    0, 0, 0, 0, 0, 0, 261, 758, 1000;
    0, 0, 0, 0, 0, 0, 0, 64, 713;
    0, 0, 0, 0, 0, 0, 0, 0, 513]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt49 : residualMinor (49 : F) 0 = firstValue 49 := by
  apply value_of_factors firstLower49 firstUpper49
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower49 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    169, 1, 0, 0, 0, 0, 0, 0, 0;
    323, 489, 1, 0, 0, 0, 0, 0, 0;
    24, 63, 149, 1, 0, 0, 0, 0, 0;
    559, 963, 206, 313, 1, 0, 0, 0, 0;
    253, 481, 112, 397, 338, 1, 0, 0, 0;
    336, 54, 653, 921, 7, 49, 1, 0, 0;
    913, 985, 617, 697, 53, 366, 349, 1, 0;
    937, 420, 550, 148, 200, 38, 198, 1006, 1]

private def secondUpper49 : Matrix (Fin 9) (Fin 9) F :=
  !![217, 21, 115, 264, 997, 434, 467, 785, 740;
    0, 866, 536, 352, 547, 523, 884, 439, 168;
    0, 0, 582, 579, 709, 30, 900, 458, 698;
    0, 0, 0, 141, 955, 434, 416, 934, 438;
    0, 0, 0, 0, 635, 229, 678, 398, 460;
    0, 0, 0, 0, 0, 96, 835, 790, 539;
    0, 0, 0, 0, 0, 0, 370, 868, 113;
    0, 0, 0, 0, 0, 0, 0, 646, 786;
    0, 0, 0, 0, 0, 0, 0, 0, 323]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt49 : residualMinor (49 : F) 1 = secondValue 49 := by
  apply value_of_factors secondLower49 secondUpper49
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower50 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    70, 1, 0, 0, 0, 0, 0, 0, 0;
    918, 812, 1, 0, 0, 0, 0, 0, 0;
    793, 532, 639, 1, 0, 0, 0, 0, 0;
    449, 262, 578, 750, 1, 0, 0, 0, 0;
    910, 703, 315, 138, 559, 1, 0, 0, 0;
    709, 27, 729, 702, 737, 277, 1, 0, 0;
    482, 154, 133, 183, 690, 691, 492, 1, 0;
    404, 874, 828, 518, 773, 454, 429, 934, 1]

private def firstUpper50 : Matrix (Fin 9) (Fin 9) F :=
  !![972, 428, 473, 986, 6, 940, 752, 983, 945;
    0, 98, 4, 904, 954, 946, 957, 165, 254;
    0, 0, 547, 944, 371, 216, 113, 138, 488;
    0, 0, 0, 452, 915, 669, 514, 959, 545;
    0, 0, 0, 0, 100, 364, 42, 966, 400;
    0, 0, 0, 0, 0, 726, 510, 30, 867;
    0, 0, 0, 0, 0, 0, 150, 435, 873;
    0, 0, 0, 0, 0, 0, 0, 27, 899;
    0, 0, 0, 0, 0, 0, 0, 0, 972]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt50 : residualMinor (50 : F) 0 = firstValue 50 := by
  apply value_of_factors firstLower50 firstUpper50
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower50 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    527, 1, 0, 0, 0, 0, 0, 0, 0;
    311, 389, 1, 0, 0, 0, 0, 0, 0;
    501, 208, 10, 1, 0, 0, 0, 0, 0;
    795, 913, 522, 548, 1, 0, 0, 0, 0;
    167, 469, 683, 1003, 525, 1, 0, 0, 0;
    285, 646, 487, 878, 636, 785, 1, 0, 0;
    764, 780, 736, 361, 591, 964, 373, 1, 0;
    1, 766, 496, 329, 191, 451, 901, 86, 1]

private def secondUpper50 : Matrix (Fin 9) (Fin 9) F :=
  !![652, 284, 539, 656, 848, 599, 145, 818, 793;
    0, 461, 302, 678, 456, 296, 389, 120, 634;
    0, 0, 543, 933, 391, 1002, 786, 882, 822;
    0, 0, 0, 109, 648, 644, 701, 270, 628;
    0, 0, 0, 0, 164, 372, 382, 90, 708;
    0, 0, 0, 0, 0, 476, 890, 546, 595;
    0, 0, 0, 0, 0, 0, 546, 281, 348;
    0, 0, 0, 0, 0, 0, 0, 822, 593;
    0, 0, 0, 0, 0, 0, 0, 0, 300]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt50 : residualMinor (50 : F) 1 = secondValue 50 := by
  apply value_of_factors secondLower50 secondUpper50
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower51 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    321, 1, 0, 0, 0, 0, 0, 0, 0;
    37, 817, 1, 0, 0, 0, 0, 0, 0;
    837, 477, 394, 1, 0, 0, 0, 0, 0;
    118, 372, 566, 456, 1, 0, 0, 0, 0;
    785, 775, 956, 696, 805, 1, 0, 0, 0;
    836, 778, 152, 842, 314, 772, 1, 0, 0;
    604, 6, 927, 218, 978, 938, 790, 1, 0;
    677, 453, 149, 400, 194, 19, 82, 774, 1]

private def firstUpper51 : Matrix (Fin 9) (Fin 9) F :=
  !![766, 457, 623, 256, 236, 646, 482, 2, 314;
    0, 695, 57, 708, 95, 491, 250, 929, 993;
    0, 0, 438, 80, 440, 486, 848, 239, 51;
    0, 0, 0, 906, 120, 337, 410, 95, 978;
    0, 0, 0, 0, 725, 657, 178, 270, 504;
    0, 0, 0, 0, 0, 967, 832, 985, 521;
    0, 0, 0, 0, 0, 0, 141, 695, 450;
    0, 0, 0, 0, 0, 0, 0, 368, 464;
    0, 0, 0, 0, 0, 0, 0, 0, 204]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt51 : residualMinor (51 : F) 0 = firstValue 51 := by
  apply value_of_factors firstLower51 firstUpper51
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower51 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    102, 1, 0, 0, 0, 0, 0, 0, 0;
    686, 526, 1, 0, 0, 0, 0, 0, 0;
    899, 110, 793, 1, 0, 0, 0, 0, 0;
    779, 330, 424, 916, 1, 0, 0, 0, 0;
    781, 839, 859, 171, 824, 1, 0, 0, 0;
    706, 746, 141, 585, 693, 393, 1, 0, 0;
    651, 636, 61, 1002, 145, 94, 100, 1, 0;
    655, 950, 373, 642, 978, 63, 104, 378, 1]

private def secondUpper51 : Matrix (Fin 9) (Fin 9) F :=
  !![912, 209, 669, 907, 972, 388, 449, 866, 381;
    0, 958, 632, 460, 923, 787, 202, 13, 367;
    0, 0, 127, 292, 1, 682, 376, 988, 257;
    0, 0, 0, 446, 171, 612, 988, 764, 340;
    0, 0, 0, 0, 431, 16, 41, 406, 82;
    0, 0, 0, 0, 0, 655, 596, 191, 104;
    0, 0, 0, 0, 0, 0, 946, 795, 768;
    0, 0, 0, 0, 0, 0, 0, 447, 762;
    0, 0, 0, 0, 0, 0, 0, 0, 355]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt51 : residualMinor (51 : F) 1 = secondValue 51 := by
  apply value_of_factors secondLower51 secondUpper51
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower52 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    121, 1, 0, 0, 0, 0, 0, 0, 0;
    558, 325, 1, 0, 0, 0, 0, 0, 0;
    584, 729, 91, 1, 0, 0, 0, 0, 0;
    861, 584, 623, 707, 1, 0, 0, 0, 0;
    851, 510, 454, 882, 796, 1, 0, 0, 0;
    319, 36, 704, 318, 598, 346, 1, 0, 0;
    533, 485, 233, 646, 28, 395, 453, 1, 0;
    786, 298, 596, 355, 319, 761, 869, 338, 1]

private def firstUpper52 : Matrix (Fin 9) (Fin 9) F :=
  !![342, 341, 462, 207, 821, 784, 569, 980, 490;
    0, 276, 922, 286, 804, 419, 42, 718, 633;
    0, 0, 80, 775, 989, 41, 295, 904, 939;
    0, 0, 0, 443, 408, 703, 38, 160, 151;
    0, 0, 0, 0, 21, 192, 694, 47, 431;
    0, 0, 0, 0, 0, 558, 219, 363, 937;
    0, 0, 0, 0, 0, 0, 784, 372, 292;
    0, 0, 0, 0, 0, 0, 0, 348, 674;
    0, 0, 0, 0, 0, 0, 0, 0, 888]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt52 : residualMinor (52 : F) 0 = firstValue 52 := by
  apply value_of_factors firstLower52 firstUpper52
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower52 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    730, 1, 0, 0, 0, 0, 0, 0, 0;
    320, 260, 1, 0, 0, 0, 0, 0, 0;
    230, 682, 527, 1, 0, 0, 0, 0, 0;
    960, 926, 73, 915, 1, 0, 0, 0, 0;
    368, 290, 795, 927, 152, 1, 0, 0, 0;
    536, 322, 241, 675, 23, 773, 1, 0, 0;
    433, 666, 880, 368, 437, 495, 275, 1, 0;
    545, 381, 12, 427, 884, 370, 66, 147, 1]

private def secondUpper52 : Matrix (Fin 9) (Fin 9) F :=
  !![721, 553, 4, 666, 1, 216, 181, 492, 220;
    0, 78, 427, 266, 533, 161, 328, 280, 223;
    0, 0, 257, 608, 323, 586, 573, 949, 572;
    0, 0, 0, 619, 486, 773, 84, 593, 153;
    0, 0, 0, 0, 282, 969, 453, 669, 414;
    0, 0, 0, 0, 0, 82, 628, 281, 722;
    0, 0, 0, 0, 0, 0, 60, 708, 720;
    0, 0, 0, 0, 0, 0, 0, 303, 142;
    0, 0, 0, 0, 0, 0, 0, 0, 706]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt52 : residualMinor (52 : F) 1 = secondValue 52 := by
  apply value_of_factors secondLower52 secondUpper52
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower53 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    561, 1, 0, 0, 0, 0, 0, 0, 0;
    611, 666, 1, 0, 0, 0, 0, 0, 0;
    287, 744, 238, 1, 0, 0, 0, 0, 0;
    498, 357, 334, 763, 1, 0, 0, 0, 0;
    969, 528, 931, 579, 230, 1, 0, 0, 0;
    558, 892, 41, 80, 619, 996, 1, 0, 0;
    103, 670, 831, 140, 550, 659, 401, 1, 0;
    756, 590, 802, 266, 915, 170, 689, 18, 1]

private def firstUpper53 : Matrix (Fin 9) (Fin 9) F :=
  !![537, 146, 779, 316, 797, 644, 459, 180, 994;
    0, 896, 218, 379, 883, 657, 528, 1, 621;
    0, 0, 113, 972, 583, 609, 11, 589, 552;
    0, 0, 0, 955, 574, 386, 620, 652, 361;
    0, 0, 0, 0, 937, 4, 73, 110, 180;
    0, 0, 0, 0, 0, 287, 849, 837, 971;
    0, 0, 0, 0, 0, 0, 13, 568, 835;
    0, 0, 0, 0, 0, 0, 0, 848, 744;
    0, 0, 0, 0, 0, 0, 0, 0, 789]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt53 : residualMinor (53 : F) 0 = firstValue 53 := by
  apply value_of_factors firstLower53 firstUpper53
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower53 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    567, 1, 0, 0, 0, 0, 0, 0, 0;
    161, 282, 1, 0, 0, 0, 0, 0, 0;
    437, 856, 64, 1, 0, 0, 0, 0, 0;
    980, 1004, 645, 618, 1, 0, 0, 0, 0;
    334, 888, 597, 606, 419, 1, 0, 0, 0;
    227, 285, 304, 351, 878, 235, 1, 0, 0;
    334, 546, 855, 550, 441, 453, 945, 1, 0;
    941, 279, 971, 798, 100, 96, 812, 11, 1]

private def secondUpper53 : Matrix (Fin 9) (Fin 9) F :=
  !![539, 263, 223, 717, 935, 754, 664, 935, 69;
    0, 275, 24, 159, 593, 8, 601, 670, 506;
    0, 0, 442, 640, 108, 696, 554, 803, 940;
    0, 0, 0, 549, 1004, 168, 513, 228, 422;
    0, 0, 0, 0, 595, 698, 631, 549, 336;
    0, 0, 0, 0, 0, 707, 869, 719, 726;
    0, 0, 0, 0, 0, 0, 95, 293, 573;
    0, 0, 0, 0, 0, 0, 0, 855, 761;
    0, 0, 0, 0, 0, 0, 0, 0, 466]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt53 : residualMinor (53 : F) 1 = secondValue 53 := by
  apply value_of_factors secondLower53 secondUpper53
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower54 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    595, 1, 0, 0, 0, 0, 0, 0, 0;
    639, 560, 1, 0, 0, 0, 0, 0, 0;
    693, 808, 855, 1, 0, 0, 0, 0, 0;
    345, 642, 644, 952, 1, 0, 0, 0, 0;
    911, 940, 480, 202, 731, 1, 0, 0, 0;
    470, 543, 395, 167, 528, 19, 1, 0, 0;
    899, 546, 326, 963, 475, 343, 86, 1, 0;
    535, 593, 524, 560, 903, 33, 388, 664, 1]

private def firstUpper54 : Matrix (Fin 9) (Fin 9) F :=
  !![150, 519, 646, 712, 908, 684, 947, 831, 415;
    0, 39, 957, 681, 848, 355, 1, 961, 825;
    0, 0, 326, 261, 331, 484, 442, 475, 604;
    0, 0, 0, 777, 607, 909, 909, 795, 934;
    0, 0, 0, 0, 113, 819, 465, 60, 822;
    0, 0, 0, 0, 0, 252, 188, 697, 84;
    0, 0, 0, 0, 0, 0, 897, 209, 527;
    0, 0, 0, 0, 0, 0, 0, 46, 74;
    0, 0, 0, 0, 0, 0, 0, 0, 825]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt54 : residualMinor (54 : F) 0 = firstValue 54 := by
  apply value_of_factors firstLower54 firstUpper54
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower54 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    761, 1, 0, 0, 0, 0, 0, 0, 0;
    411, 180, 1, 0, 0, 0, 0, 0, 0;
    11, 619, 862, 1, 0, 0, 0, 0, 0;
    83, 498, 153, 181, 1, 0, 0, 0, 0;
    350, 837, 457, 915, 645, 1, 0, 0, 0;
    844, 75, 806, 517, 182, 117, 1, 0, 0;
    17, 323, 908, 984, 255, 459, 837, 1, 0;
    63, 78, 271, 84, 854, 422, 591, 527, 1]

private def secondUpper54 : Matrix (Fin 9) (Fin 9) F :=
  !![334, 270, 893, 555, 819, 140, 483, 662, 114;
    0, 456, 382, 957, 587, 113, 157, 705, 565;
    0, 0, 685, 336, 691, 503, 987, 686, 69;
    0, 0, 0, 92, 420, 532, 879, 829, 623;
    0, 0, 0, 0, 907, 136, 93, 777, 932;
    0, 0, 0, 0, 0, 625, 903, 232, 988;
    0, 0, 0, 0, 0, 0, 922, 565, 212;
    0, 0, 0, 0, 0, 0, 0, 482, 985;
    0, 0, 0, 0, 0, 0, 0, 0, 642]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt54 : residualMinor (54 : F) 1 = secondValue 54 := by
  apply value_of_factors secondLower54 secondUpper54
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower55 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    911, 1, 0, 0, 0, 0, 0, 0, 0;
    538, 363, 1, 0, 0, 0, 0, 0, 0;
    516, 377, 171, 1, 0, 0, 0, 0, 0;
    59, 574, 483, 812, 1, 0, 0, 0, 0;
    24, 857, 264, 504, 443, 1, 0, 0, 0;
    452, 152, 635, 220, 413, 490, 1, 0, 0;
    166, 212, 828, 289, 545, 992, 400, 1, 0;
    468, 761, 622, 590, 146, 205, 565, 736, 1]

private def firstUpper55 : Matrix (Fin 9) (Fin 9) F :=
  !![707, 277, 647, 108, 8, 732, 414, 634, 404;
    0, 471, 466, 777, 264, 133, 363, 902, 777;
    0, 0, 887, 817, 27, 547, 415, 978, 23;
    0, 0, 0, 374, 616, 782, 786, 383, 878;
    0, 0, 0, 0, 155, 736, 59, 964, 173;
    0, 0, 0, 0, 0, 57, 740, 585, 24;
    0, 0, 0, 0, 0, 0, 94, 580, 13;
    0, 0, 0, 0, 0, 0, 0, 706, 830;
    0, 0, 0, 0, 0, 0, 0, 0, 162]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt55 : residualMinor (55 : F) 0 = firstValue 55 := by
  apply value_of_factors firstLower55 firstUpper55
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower55 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    433, 1, 0, 0, 0, 0, 0, 0, 0;
    124, 600, 1, 0, 0, 0, 0, 0, 0;
    305, 550, 994, 1, 0, 0, 0, 0, 0;
    776, 948, 965, 237, 1, 0, 0, 0, 0;
    237, 269, 465, 651, 654, 1, 0, 0, 0;
    894, 658, 179, 293, 576, 372, 1, 0, 0;
    717, 192, 282, 318, 882, 497, 377, 1, 0;
    590, 308, 173, 421, 112, 30, 992, 364, 1]

private def secondUpper55 : Matrix (Fin 9) (Fin 9) F :=
  !![577, 944, 938, 551, 305, 549, 102, 184, 420;
    0, 461, 91, 833, 603, 443, 381, 358, 296;
    0, 0, 123, 882, 216, 803, 660, 28, 343;
    0, 0, 0, 879, 244, 24, 765, 26, 487;
    0, 0, 0, 0, 458, 298, 653, 794, 859;
    0, 0, 0, 0, 0, 550, 477, 238, 503;
    0, 0, 0, 0, 0, 0, 606, 122, 176;
    0, 0, 0, 0, 0, 0, 0, 789, 566;
    0, 0, 0, 0, 0, 0, 0, 0, 290]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt55 : residualMinor (55 : F) 1 = secondValue 55 := by
  apply value_of_factors secondLower55 secondUpper55
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 48 through 55. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((48 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt48, secondAt48⟩
  · exact ⟨firstAt49, secondAt49⟩
  · exact ⟨firstAt50, secondAt50⟩
  · exact ⟨firstAt51, secondAt51⟩
  · exact ⟨firstAt52, secondAt52⟩
  · exact ⟨firstAt53, secondAt53⟩
  · exact ⟨firstAt54, secondAt54⟩
  · exact ⟨firstAt55, secondAt55⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch48
