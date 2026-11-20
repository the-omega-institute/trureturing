/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch88
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch88
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch88

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower88 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    474, 1, 0, 0, 0, 0, 0, 0, 0;
    488, 371, 1, 0, 0, 0, 0, 0, 0;
    887, 899, 845, 1, 0, 0, 0, 0, 0;
    958, 104, 990, 609, 1, 0, 0, 0, 0;
    657, 263, 122, 63, 1008, 1, 0, 0, 0;
    303, 359, 416, 502, 722, 360, 1, 0, 0;
    478, 212, 583, 675, 133, 246, 926, 1, 0;
    130, 695, 255, 833, 567, 890, 351, 34, 1]

private def firstUpper88 : Matrix (Fin 9) (Fin 9) F :=
  !![190, 644, 510, 719, 345, 984, 976, 699, 96;
    0, 785, 600, 238, 930, 386, 327, 970, 402;
    0, 0, 533, 763, 597, 673, 649, 610, 14;
    0, 0, 0, 927, 673, 487, 996, 471, 715;
    0, 0, 0, 0, 546, 401, 978, 2, 386;
    0, 0, 0, 0, 0, 802, 865, 237, 120;
    0, 0, 0, 0, 0, 0, 805, 669, 186;
    0, 0, 0, 0, 0, 0, 0, 555, 438;
    0, 0, 0, 0, 0, 0, 0, 0, 593]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt88 : residualMinor (88 : F) 0 = firstValue 88 := by
  apply value_of_factors firstLower88 firstUpper88
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower88 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    158, 1, 0, 0, 0, 0, 0, 0, 0;
    539, 613, 1, 0, 0, 0, 0, 0, 0;
    518, 690, 259, 1, 0, 0, 0, 0, 0;
    846, 73, 821, 498, 1, 0, 0, 0, 0;
    231, 297, 327, 614, 821, 1, 0, 0, 0;
    419, 665, 144, 678, 1001, 739, 1, 0, 0;
    38, 902, 447, 994, 966, 992, 364, 1, 0;
    946, 275, 233, 736, 79, 16, 860, 715, 1]

private def secondUpper88 : Matrix (Fin 9) (Fin 9) F :=
  !![684, 824, 126, 595, 760, 421, 470, 799, 927;
    0, 283, 452, 838, 993, 720, 226, 218, 340;
    0, 0, 898, 53, 138, 188, 550, 73, 503;
    0, 0, 0, 901, 888, 280, 832, 47, 479;
    0, 0, 0, 0, 288, 468, 694, 154, 720;
    0, 0, 0, 0, 0, 82, 949, 729, 721;
    0, 0, 0, 0, 0, 0, 553, 341, 529;
    0, 0, 0, 0, 0, 0, 0, 275, 45;
    0, 0, 0, 0, 0, 0, 0, 0, 989]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt88 : residualMinor (88 : F) 1 = secondValue 88 := by
  apply value_of_factors secondLower88 secondUpper88
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower89 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    154, 1, 0, 0, 0, 0, 0, 0, 0;
    864, 464, 1, 0, 0, 0, 0, 0, 0;
    173, 56, 964, 1, 0, 0, 0, 0, 0;
    804, 632, 657, 210, 1, 0, 0, 0, 0;
    108, 469, 803, 214, 618, 1, 0, 0, 0;
    95, 272, 252, 28, 572, 972, 1, 0, 0;
    512, 510, 861, 486, 974, 485, 535, 1, 0;
    755, 319, 967, 709, 155, 476, 748, 76, 1]

private def firstUpper89 : Matrix (Fin 9) (Fin 9) F :=
  !![866, 287, 27, 742, 891, 13, 837, 474, 960;
    0, 633, 836, 360, 890, 625, 155, 893, 338;
    0, 0, 543, 493, 334, 189, 506, 802, 106;
    0, 0, 0, 274, 390, 268, 512, 762, 638;
    0, 0, 0, 0, 105, 177, 740, 539, 179;
    0, 0, 0, 0, 0, 988, 278, 153, 1007;
    0, 0, 0, 0, 0, 0, 508, 851, 637;
    0, 0, 0, 0, 0, 0, 0, 795, 491;
    0, 0, 0, 0, 0, 0, 0, 0, 147]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt89 : residualMinor (89 : F) 0 = firstValue 89 := by
  apply value_of_factors firstLower89 firstUpper89
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower89 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    334, 1, 0, 0, 0, 0, 0, 0, 0;
    391, 832, 1, 0, 0, 0, 0, 0, 0;
    311, 840, 570, 1, 0, 0, 0, 0, 0;
    233, 484, 914, 100, 1, 0, 0, 0, 0;
    116, 481, 170, 621, 175, 1, 0, 0, 0;
    244, 613, 459, 621, 197, 399, 1, 0, 0;
    158, 58, 251, 514, 714, 661, 119, 1, 0;
    722, 428, 424, 489, 695, 119, 227, 685, 1]

private def secondUpper89 : Matrix (Fin 9) (Fin 9) F :=
  !![66, 268, 129, 751, 491, 868, 134, 108, 139;
    0, 724, 250, 9, 344, 280, 550, 484, 852;
    0, 0, 977, 974, 647, 494, 53, 390, 176;
    0, 0, 0, 290, 436, 43, 939, 283, 704;
    0, 0, 0, 0, 508, 356, 970, 954, 666;
    0, 0, 0, 0, 0, 844, 765, 490, 590;
    0, 0, 0, 0, 0, 0, 518, 824, 948;
    0, 0, 0, 0, 0, 0, 0, 972, 53;
    0, 0, 0, 0, 0, 0, 0, 0, 410]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt89 : residualMinor (89 : F) 1 = secondValue 89 := by
  apply value_of_factors secondLower89 secondUpper89
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower90 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    822, 1, 0, 0, 0, 0, 0, 0, 0;
    700, 967, 1, 0, 0, 0, 0, 0, 0;
    677, 410, 187, 1, 0, 0, 0, 0, 0;
    975, 985, 383, 395, 1, 0, 0, 0, 0;
    502, 884, 845, 48, 897, 1, 0, 0, 0;
    271, 287, 765, 84, 713, 714, 1, 0, 0;
    481, 434, 688, 499, 150, 628, 284, 1, 0;
    367, 773, 781, 451, 406, 577, 954, 630, 1]

private def firstUpper90 : Matrix (Fin 9) (Fin 9) F :=
  !![215, 454, 855, 187, 735, 243, 407, 980, 939;
    0, 954, 936, 564, 977, 624, 435, 17, 23;
    0, 0, 653, 11, 929, 772, 307, 872, 816;
    0, 0, 0, 996, 289, 668, 526, 560, 105;
    0, 0, 0, 0, 284, 420, 508, 376, 476;
    0, 0, 0, 0, 0, 776, 656, 245, 89;
    0, 0, 0, 0, 0, 0, 304, 939, 517;
    0, 0, 0, 0, 0, 0, 0, 880, 936;
    0, 0, 0, 0, 0, 0, 0, 0, 581]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt90 : residualMinor (90 : F) 0 = firstValue 90 := by
  apply value_of_factors firstLower90 firstUpper90
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower90 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    541, 1, 0, 0, 0, 0, 0, 0, 0;
    16, 589, 1, 0, 0, 0, 0, 0, 0;
    885, 729, 627, 1, 0, 0, 0, 0, 0;
    952, 145, 266, 317, 1, 0, 0, 0, 0;
    220, 312, 763, 803, 324, 1, 0, 0, 0;
    4, 450, 30, 410, 76, 435, 1, 0, 0;
    620, 20, 620, 289, 329, 939, 391, 1, 0;
    792, 946, 3, 711, 162, 942, 410, 514, 1]

private def secondUpper90 : Matrix (Fin 9) (Fin 9) F :=
  !![91, 269, 854, 496, 134, 152, 36, 211, 963;
    0, 579, 581, 968, 910, 85, 705, 261, 666;
    0, 0, 150, 338, 837, 348, 448, 337, 245;
    0, 0, 0, 217, 495, 361, 940, 564, 638;
    0, 0, 0, 0, 677, 145, 186, 551, 798;
    0, 0, 0, 0, 0, 608, 556, 552, 781;
    0, 0, 0, 0, 0, 0, 522, 885, 827;
    0, 0, 0, 0, 0, 0, 0, 821, 752;
    0, 0, 0, 0, 0, 0, 0, 0, 956]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt90 : residualMinor (90 : F) 1 = secondValue 90 := by
  apply value_of_factors secondLower90 secondUpper90
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower91 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    907, 1, 0, 0, 0, 0, 0, 0, 0;
    1000, 318, 1, 0, 0, 0, 0, 0, 0;
    627, 203, 305, 1, 0, 0, 0, 0, 0;
    992, 74, 724, 463, 1, 0, 0, 0, 0;
    151, 419, 813, 150, 818, 1, 0, 0, 0;
    235, 519, 531, 452, 911, 300, 1, 0, 0;
    785, 610, 1008, 175, 309, 111, 526, 1, 0;
    127, 185, 22, 654, 961, 837, 733, 589, 1]

private def firstUpper91 : Matrix (Fin 9) (Fin 9) F :=
  !![712, 827, 534, 41, 581, 804, 228, 2, 678;
    0, 894, 323, 576, 150, 964, 994, 845, 618;
    0, 0, 365, 44, 281, 410, 272, 452, 911;
    0, 0, 0, 504, 758, 856, 892, 758, 557;
    0, 0, 0, 0, 952, 905, 866, 365, 220;
    0, 0, 0, 0, 0, 818, 193, 701, 893;
    0, 0, 0, 0, 0, 0, 73, 660, 68;
    0, 0, 0, 0, 0, 0, 0, 613, 803;
    0, 0, 0, 0, 0, 0, 0, 0, 518]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt91 : residualMinor (91 : F) 0 = firstValue 91 := by
  apply value_of_factors firstLower91 firstUpper91
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower91 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    477, 1, 0, 0, 0, 0, 0, 0, 0;
    739, 188, 1, 0, 0, 0, 0, 0, 0;
    592, 15, 310, 1, 0, 0, 0, 0, 0;
    665, 133, 440, 888, 1, 0, 0, 0, 0;
    571, 631, 430, 649, 707, 1, 0, 0, 0;
    816, 151, 546, 277, 684, 282, 1, 0, 0;
    799, 511, 334, 653, 881, 38, 433, 1, 0;
    216, 834, 576, 985, 624, 652, 611, 454, 1]

private def secondUpper91 : Matrix (Fin 9) (Fin 9) F :=
  !![12, 112, 278, 249, 579, 211, 427, 570, 46;
    0, 340, 923, 719, 702, 938, 75, 172, 330;
    0, 0, 818, 884, 512, 750, 803, 225, 453;
    0, 0, 0, 792, 461, 174, 417, 519, 510;
    0, 0, 0, 0, 492, 142, 939, 236, 194;
    0, 0, 0, 0, 0, 704, 1006, 478, 756;
    0, 0, 0, 0, 0, 0, 202, 649, 417;
    0, 0, 0, 0, 0, 0, 0, 586, 287;
    0, 0, 0, 0, 0, 0, 0, 0, 288]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt91 : residualMinor (91 : F) 1 = secondValue 91 := by
  apply value_of_factors secondLower91 secondUpper91
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower92 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    307, 1, 0, 0, 0, 0, 0, 0, 0;
    418, 311, 1, 0, 0, 0, 0, 0, 0;
    829, 483, 577, 1, 0, 0, 0, 0, 0;
    1005, 886, 451, 807, 1, 0, 0, 0, 0;
    728, 324, 601, 966, 250, 1, 0, 0, 0;
    391, 588, 252, 318, 4, 663, 1, 0, 0;
    556, 673, 600, 322, 615, 933, 735, 1, 0;
    465, 541, 672, 458, 678, 78, 754, 477, 1]

private def firstUpper92 : Matrix (Fin 9) (Fin 9) F :=
  !![82, 827, 325, 371, 685, 201, 805, 411, 194;
    0, 901, 372, 208, 566, 707, 801, 675, 233;
    0, 0, 942, 433, 734, 94, 293, 653, 422;
    0, 0, 0, 798, 179, 692, 289, 771, 1001;
    0, 0, 0, 0, 43, 403, 842, 244, 787;
    0, 0, 0, 0, 0, 214, 904, 627, 713;
    0, 0, 0, 0, 0, 0, 680, 978, 989;
    0, 0, 0, 0, 0, 0, 0, 918, 301;
    0, 0, 0, 0, 0, 0, 0, 0, 260]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt92 : residualMinor (92 : F) 0 = firstValue 92 := by
  apply value_of_factors firstLower92 firstUpper92
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower92 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    947, 1, 0, 0, 0, 0, 0, 0, 0;
    651, 487, 1, 0, 0, 0, 0, 0, 0;
    315, 710, 253, 1, 0, 0, 0, 0, 0;
    959, 213, 628, 115, 1, 0, 0, 0, 0;
    84, 321, 460, 219, 931, 1, 0, 0, 0;
    291, 229, 353, 313, 172, 870, 1, 0, 0;
    660, 736, 792, 208, 997, 398, 833, 1, 0;
    400, 973, 518, 699, 681, 308, 109, 885, 1]

private def secondUpper92 : Matrix (Fin 9) (Fin 9) F :=
  !![206, 406, 485, 459, 945, 259, 702, 968, 854;
    0, 469, 56, 294, 48, 779, 868, 203, 740;
    0, 0, 287, 192, 85, 185, 804, 443, 447;
    0, 0, 0, 475, 553, 622, 127, 865, 842;
    0, 0, 0, 0, 343, 250, 782, 662, 767;
    0, 0, 0, 0, 0, 204, 512, 767, 433;
    0, 0, 0, 0, 0, 0, 106, 896, 519;
    0, 0, 0, 0, 0, 0, 0, 199, 437;
    0, 0, 0, 0, 0, 0, 0, 0, 168]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt92 : residualMinor (92 : F) 1 = secondValue 92 := by
  apply value_of_factors secondLower92 secondUpper92
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower93 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    183, 1, 0, 0, 0, 0, 0, 0, 0;
    592, 496, 1, 0, 0, 0, 0, 0, 0;
    92, 752, 188, 1, 0, 0, 0, 0, 0;
    40, 981, 41, 905, 1, 0, 0, 0, 0;
    866, 834, 106, 65, 874, 1, 0, 0, 0;
    26, 196, 351, 815, 672, 138, 1, 0, 0;
    403, 798, 990, 228, 148, 737, 604, 1, 0;
    549, 854, 449, 113, 11, 520, 97, 418, 1]

private def firstUpper93 : Matrix (Fin 9) (Fin 9) F :=
  !![806, 204, 370, 329, 16, 219, 750, 999, 549;
    0, 874, 81, 186, 537, 594, 437, 187, 372;
    0, 0, 149, 226, 946, 67, 314, 156, 879;
    0, 0, 0, 193, 567, 630, 244, 562, 94;
    0, 0, 0, 0, 290, 197, 537, 682, 907;
    0, 0, 0, 0, 0, 148, 656, 21, 961;
    0, 0, 0, 0, 0, 0, 75, 870, 572;
    0, 0, 0, 0, 0, 0, 0, 536, 32;
    0, 0, 0, 0, 0, 0, 0, 0, 381]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt93 : residualMinor (93 : F) 0 = firstValue 93 := by
  apply value_of_factors firstLower93 firstUpper93
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower93 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    756, 1, 0, 0, 0, 0, 0, 0, 0;
    933, 54, 1, 0, 0, 0, 0, 0, 0;
    464, 142, 602, 1, 0, 0, 0, 0, 0;
    705, 635, 153, 163, 1, 0, 0, 0, 0;
    290, 220, 992, 147, 369, 1, 0, 0, 0;
    518, 59, 139, 585, 584, 995, 1, 0, 0;
    145, 629, 713, 314, 715, 187, 602, 1, 0;
    164, 623, 211, 223, 913, 751, 588, 875, 1]

private def secondUpper93 : Matrix (Fin 9) (Fin 9) F :=
  !![448, 537, 445, 629, 764, 829, 777, 280, 281;
    0, 519, 774, 577, 2, 176, 289, 585, 402;
    0, 0, 148, 187, 747, 582, 230, 1003, 502;
    0, 0, 0, 905, 208, 552, 621, 576, 881;
    0, 0, 0, 0, 71, 767, 781, 566, 600;
    0, 0, 0, 0, 0, 604, 880, 315, 947;
    0, 0, 0, 0, 0, 0, 627, 932, 340;
    0, 0, 0, 0, 0, 0, 0, 206, 167;
    0, 0, 0, 0, 0, 0, 0, 0, 727]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt93 : residualMinor (93 : F) 1 = secondValue 93 := by
  apply value_of_factors secondLower93 secondUpper93
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 88 through 93. -/
theorem pointValues (t : Fin 6) :
    let q : F := ((88 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt88, secondAt88⟩
  · exact ⟨firstAt89, secondAt89⟩
  · exact ⟨firstAt90, secondAt90⟩
  · exact ⟨firstAt91, secondAt91⟩
  · exact ⟨firstAt92, secondAt92⟩
  · exact ⟨firstAt93, secondAt93⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch88
