/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch40
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch40
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the six-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteMinorEvaluation

/-! Residue-field point evaluations of the two six-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch40

open Matrix PeriodicMPSSixSiteLineBezout PeriodicMPSSixSiteLineMinors
  PeriodicMPSSixSiteMinorEvaluation

private def firstLower40 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    951, 1, 0, 0, 0, 0, 0, 0, 0;
    429, 877, 1, 0, 0, 0, 0, 0, 0;
    191, 78, 741, 1, 0, 0, 0, 0, 0;
    692, 765, 633, 138, 1, 0, 0, 0, 0;
    684, 375, 55, 644, 923, 1, 0, 0, 0;
    23, 406, 107, 725, 531, 547, 1, 0, 0;
    100, 56, 616, 504, 70, 557, 2, 1, 0;
    293, 404, 951, 107, 381, 130, 975, 833, 1]

private def firstUpper40 : Matrix (Fin 9) (Fin 9) F :=
  !![574, 201, 985, 503, 566, 699, 309, 315, 305;
    0, 978, 641, 177, 190, 43, 996, 225, 846;
    0, 0, 419, 242, 300, 705, 554, 755, 672;
    0, 0, 0, 982, 888, 754, 224, 200, 107;
    0, 0, 0, 0, 811, 693, 897, 229, 148;
    0, 0, 0, 0, 0, 594, 509, 452, 748;
    0, 0, 0, 0, 0, 0, 357, 741, 732;
    0, 0, 0, 0, 0, 0, 0, 349, 123;
    0, 0, 0, 0, 0, 0, 0, 0, 940]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt40 : residualMinor (40 : F) 0 = firstValue 40 := by
  apply value_of_factors firstLower40 firstUpper40
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower40 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    723, 1, 0, 0, 0, 0, 0, 0, 0;
    79, 95, 1, 0, 0, 0, 0, 0, 0;
    64, 345, 38, 1, 0, 0, 0, 0, 0;
    318, 900, 809, 514, 1, 0, 0, 0, 0;
    435, 45, 930, 574, 837, 1, 0, 0, 0;
    526, 704, 539, 976, 108, 333, 1, 0, 0;
    839, 604, 510, 170, 725, 28, 1005, 1, 0;
    148, 944, 56, 24, 1004, 230, 703, 921, 1]

private def secondUpper40 : Matrix (Fin 9) (Fin 9) F :=
  !![267, 11, 929, 446, 648, 812, 762, 318, 418;
    0, 538, 342, 686, 331, 23, 215, 255, 795;
    0, 0, 421, 442, 191, 533, 731, 339, 90;
    0, 0, 0, 101, 560, 699, 187, 562, 20;
    0, 0, 0, 0, 818, 232, 858, 88, 759;
    0, 0, 0, 0, 0, 571, 876, 262, 624;
    0, 0, 0, 0, 0, 0, 299, 486, 436;
    0, 0, 0, 0, 0, 0, 0, 81, 366;
    0, 0, 0, 0, 0, 0, 0, 0, 191]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt40 : residualMinor (40 : F) 1 = secondValue 40 := by
  apply value_of_factors secondLower40 secondUpper40
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower41 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    697, 1, 0, 0, 0, 0, 0, 0, 0;
    79, 172, 1, 0, 0, 0, 0, 0, 0;
    202, 438, 198, 1, 0, 0, 0, 0, 0;
    830, 954, 550, 508, 1, 0, 0, 0, 0;
    254, 53, 398, 235, 289, 1, 0, 0, 0;
    505, 985, 350, 620, 613, 9, 1, 0, 0;
    730, 67, 888, 652, 547, 67, 934, 1, 0;
    540, 606, 846, 18, 432, 934, 236, 787, 1]

private def firstUpper41 : Matrix (Fin 9) (Fin 9) F :=
  !![421, 615, 196, 933, 589, 671, 602, 276, 313;
    0, 812, 90, 256, 994, 77, 855, 584, 120;
    0, 0, 875, 461, 737, 110, 57, 932, 267;
    0, 0, 0, 645, 257, 225, 403, 547, 205;
    0, 0, 0, 0, 254, 937, 346, 915, 449;
    0, 0, 0, 0, 0, 41, 933, 952, 153;
    0, 0, 0, 0, 0, 0, 189, 300, 756;
    0, 0, 0, 0, 0, 0, 0, 690, 14;
    0, 0, 0, 0, 0, 0, 0, 0, 16]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt41 : residualMinor (41 : F) 0 = firstValue 41 := by
  apply value_of_factors firstLower41 firstUpper41
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower41 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    332, 1, 0, 0, 0, 0, 0, 0, 0;
    173, 412, 1, 0, 0, 0, 0, 0, 0;
    451, 710, 165, 1, 0, 0, 0, 0, 0;
    125, 777, 337, 649, 1, 0, 0, 0, 0;
    850, 796, 823, 400, 409, 1, 0, 0, 0;
    246, 286, 833, 489, 65, 341, 1, 0, 0;
    369, 526, 296, 413, 831, 128, 346, 1, 0;
    401, 619, 113, 760, 879, 646, 15, 838, 1]

private def secondUpper41 : Matrix (Fin 9) (Fin 9) F :=
  !![34, 83, 850, 135, 237, 356, 925, 259, 154;
    0, 329, 807, 337, 882, 458, 341, 14, 668;
    0, 0, 301, 397, 516, 726, 103, 970, 62;
    0, 0, 0, 623, 339, 446, 6, 965, 331;
    0, 0, 0, 0, 760, 795, 465, 1004, 33;
    0, 0, 0, 0, 0, 727, 700, 252, 31;
    0, 0, 0, 0, 0, 0, 440, 904, 188;
    0, 0, 0, 0, 0, 0, 0, 392, 461;
    0, 0, 0, 0, 0, 0, 0, 0, 206]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt41 : residualMinor (41 : F) 1 = secondValue 41 := by
  apply value_of_factors secondLower41 secondUpper41
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower42 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    378, 1, 0, 0, 0, 0, 0, 0, 0;
    918, 187, 1, 0, 0, 0, 0, 0, 0;
    17, 18, 696, 1, 0, 0, 0, 0, 0;
    914, 445, 619, 678, 1, 0, 0, 0, 0;
    286, 65, 769, 743, 757, 1, 0, 0, 0;
    76, 584, 487, 169, 346, 42, 1, 0, 0;
    542, 448, 755, 763, 425, 51, 783, 1, 0;
    30, 124, 512, 829, 82, 375, 16, 137, 1]

private def firstUpper42 : Matrix (Fin 9) (Fin 9) F :=
  !![430, 936, 651, 903, 211, 542, 410, 465, 929;
    0, 770, 361, 519, 376, 939, 830, 280, 478;
    0, 0, 978, 898, 713, 409, 204, 894, 572;
    0, 0, 0, 267, 84, 482, 484, 614, 696;
    0, 0, 0, 0, 353, 868, 379, 341, 883;
    0, 0, 0, 0, 0, 528, 912, 229, 386;
    0, 0, 0, 0, 0, 0, 532, 771, 918;
    0, 0, 0, 0, 0, 0, 0, 480, 647;
    0, 0, 0, 0, 0, 0, 0, 0, 509]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt42 : residualMinor (42 : F) 0 = firstValue 42 := by
  apply value_of_factors firstLower42 firstUpper42
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower42 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    146, 1, 0, 0, 0, 0, 0, 0, 0;
    286, 906, 1, 0, 0, 0, 0, 0, 0;
    950, 63, 240, 1, 0, 0, 0, 0, 0;
    820, 399, 64, 341, 1, 0, 0, 0, 0;
    373, 778, 763, 577, 341, 1, 0, 0, 0;
    77, 1008, 659, 685, 52, 734, 1, 0, 0;
    529, 121, 738, 291, 331, 947, 974, 1, 0;
    261, 897, 938, 328, 630, 976, 168, 695, 1]

private def secondUpper42 : Matrix (Fin 9) (Fin 9) F :=
  !![316, 342, 10, 793, 218, 347, 778, 418, 235;
    0, 937, 801, 59, 883, 776, 853, 1005, 504;
    0, 0, 95, 893, 714, 412, 608, 960, 211;
    0, 0, 0, 452, 959, 329, 531, 463, 519;
    0, 0, 0, 0, 439, 571, 607, 592, 748;
    0, 0, 0, 0, 0, 222, 939, 166, 806;
    0, 0, 0, 0, 0, 0, 792, 160, 603;
    0, 0, 0, 0, 0, 0, 0, 536, 452;
    0, 0, 0, 0, 0, 0, 0, 0, 463]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt42 : residualMinor (42 : F) 1 = secondValue 42 := by
  apply value_of_factors secondLower42 secondUpper42
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower43 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    38, 1, 0, 0, 0, 0, 0, 0, 0;
    751, 472, 1, 0, 0, 0, 0, 0, 0;
    227, 949, 219, 1, 0, 0, 0, 0, 0;
    666, 615, 960, 195, 1, 0, 0, 0, 0;
    473, 479, 641, 789, 59, 1, 0, 0, 0;
    329, 817, 524, 342, 673, 91, 1, 0, 0;
    739, 858, 815, 293, 627, 859, 735, 1, 0;
    673, 852, 493, 427, 529, 626, 715, 794, 1]

private def firstUpper43 : Matrix (Fin 9) (Fin 9) F :=
  !![811, 1008, 688, 926, 177, 384, 132, 871, 14;
    0, 827, 952, 264, 707, 135, 940, 366, 352;
    0, 0, 569, 575, 845, 13, 430, 773, 509;
    0, 0, 0, 708, 703, 315, 881, 493, 514;
    0, 0, 0, 0, 266, 670, 190, 186, 332;
    0, 0, 0, 0, 0, 560, 261, 199, 102;
    0, 0, 0, 0, 0, 0, 389, 530, 856;
    0, 0, 0, 0, 0, 0, 0, 119, 299;
    0, 0, 0, 0, 0, 0, 0, 0, 186]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt43 : residualMinor (43 : F) 0 = firstValue 43 := by
  apply value_of_factors firstLower43 firstUpper43
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower43 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    814, 1, 0, 0, 0, 0, 0, 0, 0;
    317, 330, 1, 0, 0, 0, 0, 0, 0;
    708, 554, 253, 1, 0, 0, 0, 0, 0;
    863, 897, 876, 464, 1, 0, 0, 0, 0;
    787, 79, 129, 456, 291, 1, 0, 0, 0;
    470, 452, 761, 396, 577, 785, 1, 0, 0;
    551, 174, 892, 854, 404, 207, 901, 1, 0;
    985, 917, 917, 513, 255, 459, 28, 232, 1]

private def secondUpper43 : Matrix (Fin 9) (Fin 9) F :=
  !![324, 533, 765, 9, 345, 611, 233, 704, 392;
    0, 797, 705, 883, 42, 684, 941, 223, 640;
    0, 0, 63, 677, 182, 313, 438, 154, 116;
    0, 0, 0, 247, 104, 735, 21, 418, 666;
    0, 0, 0, 0, 600, 254, 892, 620, 526;
    0, 0, 0, 0, 0, 853, 419, 746, 90;
    0, 0, 0, 0, 0, 0, 17, 476, 654;
    0, 0, 0, 0, 0, 0, 0, 717, 217;
    0, 0, 0, 0, 0, 0, 0, 0, 918]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt43 : residualMinor (43 : F) 1 = secondValue 43 := by
  apply value_of_factors secondLower43 secondUpper43
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower44 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    836, 1, 0, 0, 0, 0, 0, 0, 0;
    951, 361, 1, 0, 0, 0, 0, 0, 0;
    617, 1003, 790, 1, 0, 0, 0, 0, 0;
    520, 59, 404, 584, 1, 0, 0, 0, 0;
    1008, 164, 465, 63, 516, 1, 0, 0, 0;
    952, 211, 243, 509, 297, 613, 1, 0, 0;
    477, 789, 886, 782, 900, 893, 989, 1, 0;
    444, 9, 536, 769, 422, 767, 339, 656, 1]

private def firstUpper44 : Matrix (Fin 9) (Fin 9) F :=
  !![258, 1001, 751, 531, 761, 414, 249, 233, 278;
    0, 766, 821, 195, 820, 203, 539, 252, 165;
    0, 0, 710, 647, 435, 976, 372, 674, 1;
    0, 0, 0, 861, 96, 810, 189, 843, 954;
    0, 0, 0, 0, 498, 384, 830, 986, 333;
    0, 0, 0, 0, 0, 873, 952, 656, 635;
    0, 0, 0, 0, 0, 0, 121, 60, 919;
    0, 0, 0, 0, 0, 0, 0, 50, 798;
    0, 0, 0, 0, 0, 0, 0, 0, 832]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt44 : residualMinor (44 : F) 0 = firstValue 44 := by
  apply value_of_factors firstLower44 firstUpper44
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower44 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    430, 1, 0, 0, 0, 0, 0, 0, 0;
    198, 310, 1, 0, 0, 0, 0, 0, 0;
    57, 519, 590, 1, 0, 0, 0, 0, 0;
    595, 126, 811, 636, 1, 0, 0, 0, 0;
    510, 385, 997, 450, 720, 1, 0, 0, 0;
    156, 861, 188, 337, 495, 604, 1, 0, 0;
    74, 226, 162, 148, 167, 756, 918, 1, 0;
    37, 277, 951, 319, 169, 188, 953, 720, 1]

private def secondUpper44 : Matrix (Fin 9) (Fin 9) F :=
  !![291, 727, 549, 56, 464, 616, 52, 213, 885;
    0, 312, 86, 287, 599, 707, 687, 532, 346;
    0, 0, 118, 726, 989, 710, 630, 190, 85;
    0, 0, 0, 668, 532, 298, 816, 755, 74;
    0, 0, 0, 0, 698, 170, 838, 937, 773;
    0, 0, 0, 0, 0, 303, 174, 131, 566;
    0, 0, 0, 0, 0, 0, 929, 389, 344;
    0, 0, 0, 0, 0, 0, 0, 134, 401;
    0, 0, 0, 0, 0, 0, 0, 0, 870]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt44 : residualMinor (44 : F) 1 = secondValue 44 := by
  apply value_of_factors secondLower44 secondUpper44
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower45 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    542, 1, 0, 0, 0, 0, 0, 0, 0;
    361, 197, 1, 0, 0, 0, 0, 0, 0;
    23, 793, 418, 1, 0, 0, 0, 0, 0;
    16, 100, 493, 704, 1, 0, 0, 0, 0;
    921, 5, 1006, 489, 303, 1, 0, 0, 0;
    869, 269, 702, 589, 80, 135, 1, 0, 0;
    883, 74, 197, 446, 264, 79, 670, 1, 0;
    607, 66, 449, 447, 617, 510, 826, 741, 1]

private def firstUpper45 : Matrix (Fin 9) (Fin 9) F :=
  !![604, 902, 199, 264, 736, 509, 462, 989, 77;
    0, 353, 262, 192, 161, 293, 813, 920, 191;
    0, 0, 483, 817, 392, 243, 0, 369, 8;
    0, 0, 0, 392, 422, 423, 270, 9, 649;
    0, 0, 0, 0, 534, 303, 10, 268, 1;
    0, 0, 0, 0, 0, 871, 472, 1004, 859;
    0, 0, 0, 0, 0, 0, 572, 558, 677;
    0, 0, 0, 0, 0, 0, 0, 772, 230;
    0, 0, 0, 0, 0, 0, 0, 0, 698]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt45 : residualMinor (45 : F) 0 = firstValue 45 := by
  apply value_of_factors firstLower45 firstUpper45
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower45 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    970, 1, 0, 0, 0, 0, 0, 0, 0;
    816, 226, 1, 0, 0, 0, 0, 0, 0;
    687, 105, 201, 1, 0, 0, 0, 0, 0;
    729, 827, 929, 436, 1, 0, 0, 0, 0;
    442, 9, 372, 390, 794, 1, 0, 0, 0;
    965, 196, 672, 349, 850, 839, 1, 0, 0;
    626, 135, 774, 446, 966, 264, 167, 1, 0;
    349, 189, 597, 725, 448, 535, 773, 848, 1]

private def secondUpper45 : Matrix (Fin 9) (Fin 9) F :=
  !![739, 41, 239, 881, 995, 972, 625, 872, 227;
    0, 462, 397, 55, 981, 280, 135, 881, 328;
    0, 0, 630, 956, 749, 771, 341, 301, 809;
    0, 0, 0, 757, 367, 436, 236, 111, 984;
    0, 0, 0, 0, 1001, 246, 145, 501, 992;
    0, 0, 0, 0, 0, 549, 26, 76, 304;
    0, 0, 0, 0, 0, 0, 292, 952, 916;
    0, 0, 0, 0, 0, 0, 0, 76, 1003;
    0, 0, 0, 0, 0, 0, 0, 0, 497]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt45 : residualMinor (45 : F) 1 = secondValue 45 := by
  apply value_of_factors secondLower45 secondUpper45
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower46 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    705, 1, 0, 0, 0, 0, 0, 0, 0;
    1003, 517, 1, 0, 0, 0, 0, 0, 0;
    707, 792, 302, 1, 0, 0, 0, 0, 0;
    433, 555, 755, 383, 1, 0, 0, 0, 0;
    99, 113, 631, 261, 793, 1, 0, 0, 0;
    359, 958, 303, 185, 972, 971, 1, 0, 0;
    662, 389, 699, 277, 928, 765, 935, 1, 0;
    478, 598, 16, 608, 961, 375, 112, 610, 1]

private def firstUpper46 : Matrix (Fin 9) (Fin 9) F :=
  !![836, 681, 166, 894, 725, 673, 984, 586, 681;
    0, 796, 511, 458, 329, 876, 500, 662, 818;
    0, 0, 159, 253, 772, 380, 46, 857, 157;
    0, 0, 0, 164, 145, 582, 111, 997, 790;
    0, 0, 0, 0, 303, 1002, 584, 723, 845;
    0, 0, 0, 0, 0, 428, 656, 219, 727;
    0, 0, 0, 0, 0, 0, 312, 751, 751;
    0, 0, 0, 0, 0, 0, 0, 612, 51;
    0, 0, 0, 0, 0, 0, 0, 0, 116]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt46 : residualMinor (46 : F) 0 = firstValue 46 := by
  apply value_of_factors firstLower46 firstUpper46
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower46 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    121, 1, 0, 0, 0, 0, 0, 0, 0;
    857, 670, 1, 0, 0, 0, 0, 0, 0;
    733, 212, 950, 1, 0, 0, 0, 0, 0;
    23, 48, 962, 487, 1, 0, 0, 0, 0;
    176, 780, 703, 4, 519, 1, 0, 0, 0;
    185, 200, 309, 734, 737, 482, 1, 0, 0;
    71, 557, 839, 476, 456, 882, 57, 1, 0;
    850, 995, 491, 714, 207, 442, 110, 14, 1]

private def secondUpper46 : Matrix (Fin 9) (Fin 9) F :=
  !![629, 44, 327, 847, 828, 134, 498, 733, 83;
    0, 338, 281, 534, 603, 32, 310, 201, 686;
    0, 0, 677, 621, 360, 166, 567, 524, 225;
    0, 0, 0, 614, 302, 122, 72, 645, 756;
    0, 0, 0, 0, 544, 178, 999, 865, 440;
    0, 0, 0, 0, 0, 443, 966, 105, 929;
    0, 0, 0, 0, 0, 0, 262, 285, 100;
    0, 0, 0, 0, 0, 0, 0, 290, 301;
    0, 0, 0, 0, 0, 0, 0, 0, 83]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt46 : residualMinor (46 : F) 1 = secondValue 46 := by
  apply value_of_factors secondLower46 secondUpper46
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower47 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    819, 1, 0, 0, 0, 0, 0, 0, 0;
    671, 13, 1, 0, 0, 0, 0, 0, 0;
    812, 137, 212, 1, 0, 0, 0, 0, 0;
    156, 277, 210, 912, 1, 0, 0, 0, 0;
    616, 320, 515, 887, 405, 1, 0, 0, 0;
    690, 401, 149, 295, 30, 133, 1, 0, 0;
    865, 508, 579, 470, 149, 974, 308, 1, 0;
    759, 878, 269, 89, 92, 531, 370, 848, 1]

private def firstUpper47 : Matrix (Fin 9) (Fin 9) F :=
  !![571, 576, 354, 769, 803, 289, 1, 981, 722;
    0, 359, 687, 791, 729, 92, 380, 101, 319;
    0, 0, 431, 374, 288, 987, 613, 807, 497;
    0, 0, 0, 917, 725, 780, 487, 215, 905;
    0, 0, 0, 0, 229, 502, 86, 883, 821;
    0, 0, 0, 0, 0, 61, 931, 28, 648;
    0, 0, 0, 0, 0, 0, 643, 601, 112;
    0, 0, 0, 0, 0, 0, 0, 500, 406;
    0, 0, 0, 0, 0, 0, 0, 0, 124]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt47 : residualMinor (47 : F) 0 = firstValue 47 := by
  apply value_of_factors firstLower47 firstUpper47
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower47 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    986, 1, 0, 0, 0, 0, 0, 0, 0;
    366, 275, 1, 0, 0, 0, 0, 0, 0;
    115, 337, 856, 1, 0, 0, 0, 0, 0;
    461, 372, 648, 997, 1, 0, 0, 0, 0;
    30, 580, 72, 710, 320, 1, 0, 0, 0;
    612, 996, 499, 230, 913, 845, 1, 0, 0;
    549, 419, 823, 977, 739, 805, 929, 1, 0;
    579, 770, 825, 609, 129, 470, 408, 541, 1]

private def secondUpper47 : Matrix (Fin 9) (Fin 9) F :=
  !![93, 555, 612, 404, 508, 627, 562, 417, 707;
    0, 548, 980, 188, 94, 972, 1008, 886, 480;
    0, 0, 609, 176, 803, 2, 589, 750, 471;
    0, 0, 0, 605, 909, 420, 276, 234, 194;
    0, 0, 0, 0, 106, 762, 946, 511, 290;
    0, 0, 0, 0, 0, 917, 168, 363, 355;
    0, 0, 0, 0, 0, 0, 750, 421, 943;
    0, 0, 0, 0, 0, 0, 0, 836, 789;
    0, 0, 0, 0, 0, 0, 0, 0, 313]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt47 : residualMinor (47 : F) 1 = secondValue 47 := by
  apply value_of_factors secondLower47 secondUpper47
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 40 through 47. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((40 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt40, secondAt40⟩
  · exact ⟨firstAt41, secondAt41⟩
  · exact ⟨firstAt42, secondAt42⟩
  · exact ⟨firstAt43, secondAt43⟩
  · exact ⟨firstAt44, secondAt44⟩
  · exact ⟨firstAt45, secondAt45⟩
  · exact ⟨firstAt46, secondAt46⟩
  · exact ⟨firstAt47, secondAt47⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteMinorBatch40
