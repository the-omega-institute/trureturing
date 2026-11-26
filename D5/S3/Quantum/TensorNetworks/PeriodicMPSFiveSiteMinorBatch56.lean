/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch56
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch56
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch56

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower56 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    337, 1, 0, 0, 0, 0, 0, 0, 0;
    928, 87, 1, 0, 0, 0, 0, 0, 0;
    377, 433, 689, 1, 0, 0, 0, 0, 0;
    821, 444, 63, 308, 1, 0, 0, 0, 0;
    659, 383, 608, 871, 455, 1, 0, 0, 0;
    539, 667, 278, 704, 772, 869, 1, 0, 0;
    617, 449, 506, 125, 782, 4, 130, 1, 0;
    91, 623, 131, 246, 172, 282, 562, 557, 1]

private def firstUpper56 : Matrix (Fin 9) (Fin 9) F :=
  !![689, 752, 986, 949, 103, 634, 344, 612, 822;
    0, 515, 91, 820, 740, 67, 899, 442, 178;
    0, 0, 329, 370, 830, 596, 946, 597, 913;
    0, 0, 0, 53, 903, 196, 803, 636, 429;
    0, 0, 0, 0, 996, 837, 646, 830, 897;
    0, 0, 0, 0, 0, 616, 953, 854, 26;
    0, 0, 0, 0, 0, 0, 1003, 463, 4;
    0, 0, 0, 0, 0, 0, 0, 115, 336;
    0, 0, 0, 0, 0, 0, 0, 0, 694]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt56 : residualMinor (56 : F) 0 = firstValue 56 := by
  apply value_of_factors firstLower56 firstUpper56
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower56 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    46, 1, 0, 0, 0, 0, 0, 0, 0;
    316, 80, 1, 0, 0, 0, 0, 0, 0;
    580, 458, 491, 1, 0, 0, 0, 0, 0;
    857, 243, 583, 137, 1, 0, 0, 0, 0;
    105, 614, 506, 784, 495, 1, 0, 0, 0;
    445, 188, 380, 95, 228, 924, 1, 0, 0;
    192, 154, 289, 440, 452, 684, 72, 1, 0;
    152, 359, 449, 610, 412, 718, 123, 197, 1]

private def secondUpper56 : Matrix (Fin 9) (Fin 9) F :=
  !![50, 320, 341, 419, 211, 316, 422, 510, 632;
    0, 86, 870, 677, 520, 416, 551, 597, 915;
    0, 0, 247, 996, 50, 528, 997, 521, 794;
    0, 0, 0, 360, 56, 408, 260, 970, 392;
    0, 0, 0, 0, 960, 169, 837, 20, 873;
    0, 0, 0, 0, 0, 148, 555, 226, 824;
    0, 0, 0, 0, 0, 0, 875, 174, 345;
    0, 0, 0, 0, 0, 0, 0, 566, 457;
    0, 0, 0, 0, 0, 0, 0, 0, 566]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt56 : residualMinor (56 : F) 1 = secondValue 56 := by
  apply value_of_factors secondLower56 secondUpper56
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower57 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    540, 1, 0, 0, 0, 0, 0, 0, 0;
    136, 611, 1, 0, 0, 0, 0, 0, 0;
    386, 243, 132, 1, 0, 0, 0, 0, 0;
    590, 896, 569, 429, 1, 0, 0, 0, 0;
    923, 838, 86, 191, 351, 1, 0, 0, 0;
    884, 14, 844, 140, 259, 620, 1, 0, 0;
    390, 584, 192, 902, 428, 756, 628, 1, 0;
    50, 375, 961, 554, 664, 424, 892, 681, 1]

private def firstUpper57 : Matrix (Fin 9) (Fin 9) F :=
  !![18, 175, 771, 441, 971, 127, 155, 56, 112;
    0, 692, 546, 525, 430, 827, 23, 27, 879;
    0, 0, 894, 395, 207, 296, 505, 105, 856;
    0, 0, 0, 792, 973, 318, 116, 134, 150;
    0, 0, 0, 0, 476, 85, 486, 863, 865;
    0, 0, 0, 0, 0, 638, 41, 697, 726;
    0, 0, 0, 0, 0, 0, 637, 150, 583;
    0, 0, 0, 0, 0, 0, 0, 502, 165;
    0, 0, 0, 0, 0, 0, 0, 0, 130]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt57 : residualMinor (57 : F) 0 = firstValue 57 := by
  apply value_of_factors firstLower57 firstUpper57
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower57 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    293, 1, 0, 0, 0, 0, 0, 0, 0;
    57, 784, 1, 0, 0, 0, 0, 0, 0;
    224, 517, 735, 1, 0, 0, 0, 0, 0;
    315, 326, 741, 493, 1, 0, 0, 0, 0;
    626, 349, 524, 649, 431, 1, 0, 0, 0;
    2, 28, 189, 583, 669, 15, 1, 0, 0;
    990, 785, 598, 1006, 23, 59, 799, 1, 0;
    968, 314, 947, 617, 927, 705, 711, 482, 1]

private def secondUpper57 : Matrix (Fin 9) (Fin 9) F :=
  !![758, 828, 195, 793, 704, 481, 139, 857, 875;
    0, 911, 547, 262, 663, 113, 618, 137, 730;
    0, 0, 402, 376, 549, 229, 280, 140, 583;
    0, 0, 0, 420, 148, 298, 542, 363, 699;
    0, 0, 0, 0, 36, 407, 126, 781, 702;
    0, 0, 0, 0, 0, 692, 149, 994, 877;
    0, 0, 0, 0, 0, 0, 412, 752, 311;
    0, 0, 0, 0, 0, 0, 0, 449, 467;
    0, 0, 0, 0, 0, 0, 0, 0, 897]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt57 : residualMinor (57 : F) 1 = secondValue 57 := by
  apply value_of_factors secondLower57 secondUpper57
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower58 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    706, 1, 0, 0, 0, 0, 0, 0, 0;
    739, 118, 1, 0, 0, 0, 0, 0, 0;
    367, 351, 503, 1, 0, 0, 0, 0, 0;
    125, 141, 476, 221, 1, 0, 0, 0, 0;
    935, 283, 537, 686, 826, 1, 0, 0, 0;
    863, 761, 85, 79, 719, 857, 1, 0, 0;
    49, 186, 189, 169, 283, 149, 56, 1, 0;
    810, 76, 84, 514, 236, 440, 178, 266, 1]

private def firstUpper58 : Matrix (Fin 9) (Fin 9) F :=
  !![571, 307, 622, 321, 786, 364, 940, 834, 29;
    0, 120, 101, 345, 992, 291, 373, 477, 212;
    0, 0, 412, 171, 816, 614, 659, 74, 647;
    0, 0, 0, 191, 172, 11, 836, 274, 84;
    0, 0, 0, 0, 491, 133, 190, 849, 41;
    0, 0, 0, 0, 0, 141, 259, 693, 527;
    0, 0, 0, 0, 0, 0, 410, 103, 774;
    0, 0, 0, 0, 0, 0, 0, 529, 893;
    0, 0, 0, 0, 0, 0, 0, 0, 957]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt58 : residualMinor (58 : F) 0 = firstValue 58 := by
  apply value_of_factors firstLower58 firstUpper58
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower58 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    463, 1, 0, 0, 0, 0, 0, 0, 0;
    974, 784, 1, 0, 0, 0, 0, 0, 0;
    225, 732, 410, 1, 0, 0, 0, 0, 0;
    186, 818, 579, 244, 1, 0, 0, 0, 0;
    903, 513, 40, 772, 479, 1, 0, 0, 0;
    62, 784, 958, 281, 167, 670, 1, 0, 0;
    280, 850, 903, 452, 334, 771, 461, 1, 0;
    986, 469, 120, 33, 976, 969, 787, 182, 1]

private def secondUpper58 : Matrix (Fin 9) (Fin 9) F :=
  !![274, 595, 845, 556, 127, 566, 402, 280, 545;
    0, 908, 575, 822, 679, 262, 630, 546, 421;
    0, 0, 313, 208, 314, 297, 170, 154, 463;
    0, 0, 0, 369, 430, 760, 241, 324, 834;
    0, 0, 0, 0, 62, 1, 79, 768, 750;
    0, 0, 0, 0, 0, 721, 879, 223, 578;
    0, 0, 0, 0, 0, 0, 569, 375, 972;
    0, 0, 0, 0, 0, 0, 0, 309, 29;
    0, 0, 0, 0, 0, 0, 0, 0, 687]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt58 : residualMinor (58 : F) 1 = secondValue 58 := by
  apply value_of_factors secondLower58 secondUpper58
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower59 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    655, 1, 0, 0, 0, 0, 0, 0, 0;
    386, 300, 1, 0, 0, 0, 0, 0, 0;
    716, 489, 286, 1, 0, 0, 0, 0, 0;
    318, 281, 602, 555, 1, 0, 0, 0, 0;
    396, 745, 146, 525, 985, 1, 0, 0, 0;
    85, 959, 527, 15, 741, 885, 1, 0, 0;
    594, 199, 766, 475, 944, 240, 830, 1, 0;
    191, 137, 9, 723, 719, 617, 139, 420, 1]

private def firstUpper59 : Matrix (Fin 9) (Fin 9) F :=
  !![603, 685, 548, 334, 633, 231, 592, 936, 944;
    0, 11, 846, 496, 510, 454, 723, 47, 801;
    0, 0, 845, 357, 591, 653, 437, 745, 806;
    0, 0, 0, 467, 906, 370, 862, 419, 339;
    0, 0, 0, 0, 862, 331, 350, 213, 49;
    0, 0, 0, 0, 0, 194, 853, 66, 135;
    0, 0, 0, 0, 0, 0, 47, 337, 324;
    0, 0, 0, 0, 0, 0, 0, 200, 396;
    0, 0, 0, 0, 0, 0, 0, 0, 169]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt59 : residualMinor (59 : F) 0 = firstValue 59 := by
  apply value_of_factors firstLower59 firstUpper59
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower59 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    655, 1, 0, 0, 0, 0, 0, 0, 0;
    953, 386, 1, 0, 0, 0, 0, 0, 0;
    183, 984, 484, 1, 0, 0, 0, 0, 0;
    644, 401, 500, 131, 1, 0, 0, 0, 0;
    583, 934, 139, 480, 436, 1, 0, 0, 0;
    883, 593, 475, 65, 89, 691, 1, 0, 0;
    277, 750, 89, 20, 449, 354, 636, 1, 0;
    239, 638, 683, 548, 866, 890, 156, 695, 1]

private def secondUpper59 : Matrix (Fin 9) (Fin 9) F :=
  !![328, 496, 498, 685, 616, 410, 660, 878, 542;
    0, 708, 299, 643, 546, 253, 579, 704, 762;
    0, 0, 272, 640, 698, 980, 2, 197, 668;
    0, 0, 0, 750, 761, 226, 898, 268, 17;
    0, 0, 0, 0, 495, 485, 210, 669, 997;
    0, 0, 0, 0, 0, 14, 922, 173, 445;
    0, 0, 0, 0, 0, 0, 765, 921, 150;
    0, 0, 0, 0, 0, 0, 0, 575, 270;
    0, 0, 0, 0, 0, 0, 0, 0, 672]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt59 : residualMinor (59 : F) 1 = secondValue 59 := by
  apply value_of_factors secondLower59 secondUpper59
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower60 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    550, 1, 0, 0, 0, 0, 0, 0, 0;
    425, 811, 1, 0, 0, 0, 0, 0, 0;
    352, 511, 202, 1, 0, 0, 0, 0, 0;
    249, 600, 698, 607, 1, 0, 0, 0, 0;
    210, 338, 771, 503, 774, 1, 0, 0, 0;
    641, 622, 581, 703, 667, 747, 1, 0, 0;
    841, 290, 420, 470, 371, 357, 264, 1, 0;
    722, 928, 274, 851, 523, 12, 566, 355, 1]

private def firstUpper60 : Matrix (Fin 9) (Fin 9) F :=
  !![856, 830, 60, 632, 793, 770, 331, 508, 371;
    0, 524, 838, 878, 188, 400, 705, 997, 494;
    0, 0, 221, 455, 803, 220, 348, 582, 389;
    0, 0, 0, 296, 212, 977, 666, 198, 919;
    0, 0, 0, 0, 995, 342, 79, 562, 601;
    0, 0, 0, 0, 0, 843, 592, 581, 653;
    0, 0, 0, 0, 0, 0, 587, 337, 88;
    0, 0, 0, 0, 0, 0, 0, 939, 693;
    0, 0, 0, 0, 0, 0, 0, 0, 382]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt60 : residualMinor (60 : F) 0 = firstValue 60 := by
  apply value_of_factors firstLower60 firstUpper60
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower60 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    797, 1, 0, 0, 0, 0, 0, 0, 0;
    469, 36, 1, 0, 0, 0, 0, 0, 0;
    417, 947, 918, 1, 0, 0, 0, 0, 0;
    946, 303, 37, 317, 1, 0, 0, 0, 0;
    616, 727, 7, 809, 753, 1, 0, 0, 0;
    75, 973, 275, 552, 444, 1003, 1, 0, 0;
    467, 908, 463, 619, 980, 378, 560, 1, 0;
    378, 700, 940, 19, 369, 300, 127, 580, 1]

private def secondUpper60 : Matrix (Fin 9) (Fin 9) F :=
  !![712, 232, 322, 111, 927, 530, 471, 197, 148;
    0, 699, 193, 698, 219, 481, 87, 290, 823;
    0, 0, 495, 871, 226, 546, 391, 999, 563;
    0, 0, 0, 90, 560, 980, 805, 360, 584;
    0, 0, 0, 0, 401, 904, 422, 999, 846;
    0, 0, 0, 0, 0, 279, 861, 493, 913;
    0, 0, 0, 0, 0, 0, 931, 200, 913;
    0, 0, 0, 0, 0, 0, 0, 382, 779;
    0, 0, 0, 0, 0, 0, 0, 0, 945]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt60 : residualMinor (60 : F) 1 = secondValue 60 := by
  apply value_of_factors secondLower60 secondUpper60
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower61 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    898, 1, 0, 0, 0, 0, 0, 0, 0;
    578, 153, 1, 0, 0, 0, 0, 0, 0;
    610, 392, 775, 1, 0, 0, 0, 0, 0;
    226, 142, 788, 603, 1, 0, 0, 0, 0;
    709, 980, 630, 398, 493, 1, 0, 0, 0;
    410, 776, 820, 613, 265, 152, 1, 0, 0;
    543, 988, 374, 63, 801, 940, 788, 1, 0;
    729, 476, 391, 751, 827, 1008, 937, 189, 1]

private def firstUpper61 : Matrix (Fin 9) (Fin 9) F :=
  !![209, 68, 311, 686, 425, 946, 484, 234, 502;
    0, 546, 220, 194, 556, 449, 221, 208, 397;
    0, 0, 941, 456, 358, 167, 292, 428, 990;
    0, 0, 0, 263, 384, 508, 399, 373, 15;
    0, 0, 0, 0, 607, 394, 512, 950, 142;
    0, 0, 0, 0, 0, 117, 254, 639, 917;
    0, 0, 0, 0, 0, 0, 969, 579, 748;
    0, 0, 0, 0, 0, 0, 0, 1006, 632;
    0, 0, 0, 0, 0, 0, 0, 0, 127]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt61 : residualMinor (61 : F) 0 = firstValue 61 := by
  apply value_of_factors firstLower61 firstUpper61
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower61 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    733, 1, 0, 0, 0, 0, 0, 0, 0;
    484, 257, 1, 0, 0, 0, 0, 0, 0;
    938, 221, 411, 1, 0, 0, 0, 0, 0;
    520, 738, 762, 405, 1, 0, 0, 0, 0;
    446, 242, 341, 712, 596, 1, 0, 0, 0;
    609, 104, 692, 865, 889, 613, 1, 0, 0;
    181, 271, 265, 648, 822, 890, 660, 1, 0;
    582, 381, 156, 379, 354, 532, 533, 103, 1]

private def secondUpper61 : Matrix (Fin 9) (Fin 9) F :=
  !![584, 723, 474, 332, 269, 617, 462, 866, 720;
    0, 836, 668, 545, 382, 150, 352, 351, 117;
    0, 0, 941, 777, 797, 999, 794, 204, 581;
    0, 0, 0, 99, 924, 767, 132, 352, 527;
    0, 0, 0, 0, 307, 484, 345, 418, 643;
    0, 0, 0, 0, 0, 662, 964, 409, 322;
    0, 0, 0, 0, 0, 0, 576, 527, 121;
    0, 0, 0, 0, 0, 0, 0, 914, 980;
    0, 0, 0, 0, 0, 0, 0, 0, 814]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt61 : residualMinor (61 : F) 1 = secondValue 61 := by
  apply value_of_factors secondLower61 secondUpper61
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower62 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    417, 1, 0, 0, 0, 0, 0, 0, 0;
    986, 37, 1, 0, 0, 0, 0, 0, 0;
    764, 242, 985, 1, 0, 0, 0, 0, 0;
    998, 875, 799, 14, 1, 0, 0, 0, 0;
    960, 336, 751, 472, 694, 1, 0, 0, 0;
    39, 839, 939, 690, 925, 607, 1, 0, 0;
    251, 640, 441, 356, 642, 949, 359, 1, 0;
    388, 103, 610, 1000, 570, 469, 136, 386, 1]

private def firstUpper62 : Matrix (Fin 9) (Fin 9) F :=
  !![244, 333, 878, 173, 155, 678, 913, 170, 464;
    0, 499, 127, 493, 575, 44, 306, 262, 322;
    0, 0, 273, 173, 196, 475, 120, 676, 883;
    0, 0, 0, 858, 520, 449, 673, 508, 753;
    0, 0, 0, 0, 143, 291, 101, 1005, 441;
    0, 0, 0, 0, 0, 895, 298, 629, 224;
    0, 0, 0, 0, 0, 0, 603, 756, 767;
    0, 0, 0, 0, 0, 0, 0, 652, 432;
    0, 0, 0, 0, 0, 0, 0, 0, 719]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt62 : residualMinor (62 : F) 0 = firstValue 62 := by
  apply value_of_factors firstLower62 firstUpper62
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower62 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    699, 1, 0, 0, 0, 0, 0, 0, 0;
    932, 712, 1, 0, 0, 0, 0, 0, 0;
    165, 283, 365, 1, 0, 0, 0, 0, 0;
    943, 472, 27, 684, 1, 0, 0, 0, 0;
    21, 257, 980, 79, 628, 1, 0, 0, 0;
    770, 2, 507, 171, 660, 780, 1, 0, 0;
    88, 429, 717, 544, 970, 181, 258, 1, 0;
    979, 905, 606, 810, 586, 121, 590, 150, 1]

private def secondUpper62 : Matrix (Fin 9) (Fin 9) F :=
  !![278, 457, 366, 162, 76, 110, 279, 981, 903;
    0, 528, 438, 765, 987, 44, 350, 923, 519;
    0, 0, 777, 855, 71, 984, 850, 960, 792;
    0, 0, 0, 629, 186, 793, 243, 413, 577;
    0, 0, 0, 0, 792, 132, 928, 444, 232;
    0, 0, 0, 0, 0, 895, 331, 47, 915;
    0, 0, 0, 0, 0, 0, 311, 818, 189;
    0, 0, 0, 0, 0, 0, 0, 579, 71;
    0, 0, 0, 0, 0, 0, 0, 0, 953]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt62 : residualMinor (62 : F) 1 = secondValue 62 := by
  apply value_of_factors secondLower62 secondUpper62
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower63 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    359, 1, 0, 0, 0, 0, 0, 0, 0;
    530, 145, 1, 0, 0, 0, 0, 0, 0;
    917, 811, 78, 1, 0, 0, 0, 0, 0;
    299, 791, 541, 763, 1, 0, 0, 0, 0;
    838, 277, 896, 713, 257, 1, 0, 0, 0;
    572, 253, 340, 834, 491, 317, 1, 0, 0;
    242, 423, 78, 11, 105, 288, 443, 1, 0;
    157, 680, 266, 697, 476, 251, 470, 890, 1]

private def firstUpper63 : Matrix (Fin 9) (Fin 9) F :=
  !![634, 751, 841, 955, 469, 405, 508, 64, 670;
    0, 463, 474, 1006, 122, 104, 799, 372, 972;
    0, 0, 370, 52, 887, 865, 706, 512, 457;
    0, 0, 0, 962, 172, 840, 639, 679, 710;
    0, 0, 0, 0, 22, 226, 895, 137, 291;
    0, 0, 0, 0, 0, 848, 885, 648, 297;
    0, 0, 0, 0, 0, 0, 773, 396, 927;
    0, 0, 0, 0, 0, 0, 0, 418, 557;
    0, 0, 0, 0, 0, 0, 0, 0, 115]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt63 : residualMinor (63 : F) 0 = firstValue 63 := by
  apply value_of_factors firstLower63 firstUpper63
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower63 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    54, 1, 0, 0, 0, 0, 0, 0, 0;
    236, 141, 1, 0, 0, 0, 0, 0, 0;
    838, 150, 161, 1, 0, 0, 0, 0, 0;
    1005, 747, 489, 382, 1, 0, 0, 0, 0;
    791, 609, 648, 890, 16, 1, 0, 0, 0;
    786, 79, 419, 818, 993, 410, 1, 0, 0;
    459, 396, 400, 654, 8, 324, 309, 1, 0;
    268, 557, 497, 643, 748, 9, 955, 428, 1]

private def secondUpper63 : Matrix (Fin 9) (Fin 9) F :=
  !![790, 293, 951, 301, 683, 264, 52, 446, 134;
    0, 991, 807, 681, 441, 73, 761, 273, 178;
    0, 0, 32, 695, 391, 594, 861, 118, 860;
    0, 0, 0, 365, 845, 477, 400, 596, 227;
    0, 0, 0, 0, 111, 304, 648, 538, 784;
    0, 0, 0, 0, 0, 967, 445, 857, 797;
    0, 0, 0, 0, 0, 0, 276, 277, 334;
    0, 0, 0, 0, 0, 0, 0, 377, 553;
    0, 0, 0, 0, 0, 0, 0, 0, 515]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt63 : residualMinor (63 : F) 1 = secondValue 63 := by
  apply value_of_factors secondLower63 secondUpper63
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 56 through 63. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((56 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt56, secondAt56⟩
  · exact ⟨firstAt57, secondAt57⟩
  · exact ⟨firstAt58, secondAt58⟩
  · exact ⟨firstAt59, secondAt59⟩
  · exact ⟨firstAt60, secondAt60⟩
  · exact ⟨firstAt61, secondAt61⟩
  · exact ⟨firstAt62, secondAt62⟩
  · exact ⟨firstAt63, secondAt63⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch56
