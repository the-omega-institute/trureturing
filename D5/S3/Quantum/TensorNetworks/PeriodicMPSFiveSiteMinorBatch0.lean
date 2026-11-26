/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch0
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch0
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch0

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower0 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    864, 1, 0, 0, 0, 0, 0, 0, 0;
    938, 611, 1, 0, 0, 0, 0, 0, 0;
    959, 50, 351, 1, 0, 0, 0, 0, 0;
    649, 466, 503, 958, 1, 0, 0, 0, 0;
    847, 159, 67, 28, 85, 1, 0, 0, 0;
    274, 296, 702, 208, 502, 443, 1, 0, 0;
    143, 502, 555, 820, 1008, 408, 816, 1, 0;
    549, 887, 314, 19, 355, 803, 242, 916, 1]

private def firstUpper0 : Matrix (Fin 9) (Fin 9) F :=
  !![683, 29, 955, 419, 36, 709, 978, 494, 695;
    0, 242, 604, 145, 319, 137, 595, 286, 878;
    0, 0, 426, 297, 189, 502, 790, 745, 688;
    0, 0, 0, 272, 322, 348, 880, 765, 979;
    0, 0, 0, 0, 466, 975, 994, 968, 223;
    0, 0, 0, 0, 0, 566, 666, 809, 71;
    0, 0, 0, 0, 0, 0, 743, 430, 950;
    0, 0, 0, 0, 0, 0, 0, 164, 652;
    0, 0, 0, 0, 0, 0, 0, 0, 287]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt0 : residualMinor (0 : F) 0 = firstValue 0 := by
  apply value_of_factors firstLower0 firstUpper0
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower0 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    455, 1, 0, 0, 0, 0, 0, 0, 0;
    251, 12, 1, 0, 0, 0, 0, 0, 0;
    603, 978, 761, 1, 0, 0, 0, 0, 0;
    909, 704, 80, 229, 1, 0, 0, 0, 0;
    612, 972, 635, 755, 256, 1, 0, 0, 0;
    209, 964, 553, 259, 874, 847, 1, 0, 0;
    657, 685, 365, 399, 225, 159, 988, 1, 0;
    305, 296, 884, 552, 603, 663, 184, 319, 1]

private def secondUpper0 : Matrix (Fin 9) (Fin 9) F :=
  !![14, 759, 246, 26, 938, 961, 254, 690, 714;
    0, 815, 431, 208, 161, 901, 510, 144, 22;
    0, 0, 659, 680, 577, 800, 16, 814, 578;
    0, 0, 0, 1006, 290, 634, 520, 757, 416;
    0, 0, 0, 0, 962, 218, 240, 86, 420;
    0, 0, 0, 0, 0, 421, 599, 32, 626;
    0, 0, 0, 0, 0, 0, 20, 1004, 69;
    0, 0, 0, 0, 0, 0, 0, 703, 493;
    0, 0, 0, 0, 0, 0, 0, 0, 494]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt0 : residualMinor (0 : F) 1 = secondValue 0 := by
  apply value_of_factors secondLower0 secondUpper0
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower1 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    49, 1, 0, 0, 0, 0, 0, 0, 0;
    933, 286, 1, 0, 0, 0, 0, 0, 0;
    392, 687, 644, 1, 0, 0, 0, 0, 0;
    339, 976, 383, 308, 1, 0, 0, 0, 0;
    655, 369, 745, 295, 926, 1, 0, 0, 0;
    333, 671, 682, 443, 964, 390, 1, 0, 0;
    871, 145, 575, 188, 399, 820, 654, 1, 0;
    383, 551, 79, 41, 232, 970, 843, 725, 1]

private def firstUpper1 : Matrix (Fin 9) (Fin 9) F :=
  !![329, 564, 821, 249, 566, 409, 966, 603, 732;
    0, 780, 451, 110, 356, 152, 987, 936, 38;
    0, 0, 943, 52, 705, 902, 717, 425, 248;
    0, 0, 0, 654, 658, 763, 594, 303, 42;
    0, 0, 0, 0, 676, 719, 53, 682, 352;
    0, 0, 0, 0, 0, 464, 486, 9, 841;
    0, 0, 0, 0, 0, 0, 825, 610, 81;
    0, 0, 0, 0, 0, 0, 0, 144, 365;
    0, 0, 0, 0, 0, 0, 0, 0, 220]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt1 : residualMinor (1 : F) 0 = firstValue 1 := by
  apply value_of_factors firstLower1 firstUpper1
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower1 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    142, 1, 0, 0, 0, 0, 0, 0, 0;
    778, 602, 1, 0, 0, 0, 0, 0, 0;
    447, 770, 488, 1, 0, 0, 0, 0, 0;
    368, 617, 923, 768, 1, 0, 0, 0, 0;
    256, 872, 652, 213, 857, 1, 0, 0, 0;
    173, 338, 729, 487, 345, 603, 1, 0, 0;
    1002, 665, 58, 816, 862, 967, 380, 1, 0;
    341, 597, 614, 207, 687, 250, 688, 218, 1]

private def secondUpper1 : Matrix (Fin 9) (Fin 9) F :=
  !![840, 984, 208, 823, 35, 145, 11, 706, 375;
    0, 687, 45, 381, 922, 612, 345, 861, 818;
    0, 0, 708, 582, 902, 232, 398, 245, 696;
    0, 0, 0, 641, 548, 377, 896, 813, 602;
    0, 0, 0, 0, 865, 150, 768, 555, 136;
    0, 0, 0, 0, 0, 894, 656, 495, 942;
    0, 0, 0, 0, 0, 0, 810, 962, 175;
    0, 0, 0, 0, 0, 0, 0, 249, 777;
    0, 0, 0, 0, 0, 0, 0, 0, 361]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt1 : residualMinor (1 : F) 1 = secondValue 1 := by
  apply value_of_factors secondLower1 secondUpper1
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower2 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    881, 1, 0, 0, 0, 0, 0, 0, 0;
    307, 333, 1, 0, 0, 0, 0, 0, 0;
    75, 774, 860, 1, 0, 0, 0, 0, 0;
    310, 793, 24, 223, 1, 0, 0, 0, 0;
    213, 537, 219, 88, 615, 1, 0, 0, 0;
    902, 284, 469, 974, 317, 124, 1, 0, 0;
    754, 380, 100, 89, 912, 512, 688, 1, 0;
    859, 469, 201, 90, 660, 882, 654, 257, 1]

private def firstUpper2 : Matrix (Fin 9) (Fin 9) F :=
  !![319, 366, 88, 607, 310, 802, 912, 952, 402;
    0, 835, 4, 83, 400, 499, 22, 559, 418;
    0, 0, 531, 501, 415, 388, 164, 148, 28;
    0, 0, 0, 654, 304, 935, 367, 44, 66;
    0, 0, 0, 0, 201, 107, 326, 419, 446;
    0, 0, 0, 0, 0, 50, 259, 20, 122;
    0, 0, 0, 0, 0, 0, 266, 332, 387;
    0, 0, 0, 0, 0, 0, 0, 10, 200;
    0, 0, 0, 0, 0, 0, 0, 0, 700]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt2 : residualMinor (2 : F) 0 = firstValue 2 := by
  apply value_of_factors firstLower2 firstUpper2
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower2 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    114, 1, 0, 0, 0, 0, 0, 0, 0;
    684, 758, 1, 0, 0, 0, 0, 0, 0;
    278, 971, 333, 1, 0, 0, 0, 0, 0;
    5, 701, 326, 548, 1, 0, 0, 0, 0;
    490, 120, 182, 781, 457, 1, 0, 0, 0;
    659, 977, 834, 320, 824, 108, 1, 0, 0;
    915, 420, 749, 488, 199, 531, 733, 1, 0;
    727, 745, 821, 40, 539, 944, 1007, 867, 1]

private def secondUpper2 : Matrix (Fin 9) (Fin 9) F :=
  !![377, 346, 56, 781, 822, 354, 660, 856, 285;
    0, 308, 518, 847, 200, 765, 765, 72, 219;
    0, 0, 522, 845, 266, 417, 806, 928, 576;
    0, 0, 0, 298, 167, 685, 782, 360, 86;
    0, 0, 0, 0, 208, 568, 954, 875, 353;
    0, 0, 0, 0, 0, 321, 535, 230, 331;
    0, 0, 0, 0, 0, 0, 129, 887, 980;
    0, 0, 0, 0, 0, 0, 0, 548, 10;
    0, 0, 0, 0, 0, 0, 0, 0, 827]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt2 : residualMinor (2 : F) 1 = secondValue 2 := by
  apply value_of_factors secondLower2 secondUpper2
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower3 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    454, 1, 0, 0, 0, 0, 0, 0, 0;
    81, 651, 1, 0, 0, 0, 0, 0, 0;
    171, 675, 739, 1, 0, 0, 0, 0, 0;
    511, 964, 622, 458, 1, 0, 0, 0, 0;
    805, 223, 213, 516, 274, 1, 0, 0, 0;
    698, 450, 778, 897, 330, 269, 1, 0, 0;
    43, 687, 720, 273, 336, 138, 110, 1, 0;
    153, 712, 217, 103, 728, 67, 521, 160, 1]

private def firstUpper3 : Matrix (Fin 9) (Fin 9) F :=
  !![608, 549, 332, 904, 92, 878, 744, 313, 283;
    0, 280, 281, 588, 587, 373, 288, 265, 691;
    0, 0, 923, 475, 397, 693, 832, 665, 178;
    0, 0, 0, 106, 13, 631, 40, 827, 1005;
    0, 0, 0, 0, 902, 707, 467, 408, 362;
    0, 0, 0, 0, 0, 656, 802, 525, 940;
    0, 0, 0, 0, 0, 0, 980, 852, 18;
    0, 0, 0, 0, 0, 0, 0, 827, 995;
    0, 0, 0, 0, 0, 0, 0, 0, 820]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt3 : residualMinor (3 : F) 0 = firstValue 3 := by
  apply value_of_factors firstLower3 firstUpper3
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower3 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    764, 1, 0, 0, 0, 0, 0, 0, 0;
    810, 178, 1, 0, 0, 0, 0, 0, 0;
    955, 113, 584, 1, 0, 0, 0, 0, 0;
    760, 479, 886, 852, 1, 0, 0, 0, 0;
    190, 229, 256, 195, 107, 1, 0, 0, 0;
    213, 391, 272, 618, 217, 551, 1, 0, 0;
    870, 692, 829, 910, 195, 475, 422, 1, 0;
    454, 347, 249, 445, 115, 128, 779, 852, 1]

private def secondUpper3 : Matrix (Fin 9) (Fin 9) F :=
  !![735, 516, 677, 858, 896, 370, 231, 970, 73;
    0, 598, 48, 679, 544, 270, 140, 633, 753;
    0, 0, 928, 858, 255, 171, 230, 405, 285;
    0, 0, 0, 845, 503, 104, 727, 815, 214;
    0, 0, 0, 0, 155, 507, 160, 492, 366;
    0, 0, 0, 0, 0, 349, 844, 152, 143;
    0, 0, 0, 0, 0, 0, 125, 690, 753;
    0, 0, 0, 0, 0, 0, 0, 928, 20;
    0, 0, 0, 0, 0, 0, 0, 0, 265]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt3 : residualMinor (3 : F) 1 = secondValue 3 := by
  apply value_of_factors secondLower3 secondUpper3
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower4 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    981, 1, 0, 0, 0, 0, 0, 0, 0;
    980, 608, 1, 0, 0, 0, 0, 0, 0;
    144, 852, 975, 1, 0, 0, 0, 0, 0;
    821, 547, 1000, 860, 1, 0, 0, 0, 0;
    481, 853, 525, 824, 174, 1, 0, 0, 0;
    765, 580, 985, 218, 881, 848, 1, 0, 0;
    548, 962, 150, 750, 148, 453, 900, 1, 0;
    213, 776, 835, 101, 651, 564, 716, 470, 1]

private def firstUpper4 : Matrix (Fin 9) (Fin 9) F :=
  !![152, 906, 885, 825, 622, 108, 406, 394, 19;
    0, 378, 680, 57, 390, 1004, 158, 606, 258;
    0, 0, 155, 509, 71, 666, 199, 333, 140;
    0, 0, 0, 989, 643, 601, 426, 423, 50;
    0, 0, 0, 0, 453, 396, 219, 772, 77;
    0, 0, 0, 0, 0, 696, 157, 477, 613;
    0, 0, 0, 0, 0, 0, 385, 298, 835;
    0, 0, 0, 0, 0, 0, 0, 61, 598;
    0, 0, 0, 0, 0, 0, 0, 0, 857]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt4 : residualMinor (4 : F) 0 = firstValue 4 := by
  apply value_of_factors firstLower4 firstUpper4
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower4 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    606, 1, 0, 0, 0, 0, 0, 0, 0;
    148, 222, 1, 0, 0, 0, 0, 0, 0;
    662, 284, 763, 1, 0, 0, 0, 0, 0;
    324, 674, 198, 575, 1, 0, 0, 0, 0;
    703, 661, 196, 35, 266, 1, 0, 0, 0;
    997, 206, 883, 167, 881, 718, 1, 0, 0;
    293, 363, 643, 708, 629, 140, 821, 1, 0;
    870, 112, 79, 320, 42, 769, 553, 587, 1]

private def secondUpper4 : Matrix (Fin 9) (Fin 9) F :=
  !![906, 302, 964, 250, 236, 917, 734, 652, 566;
    0, 861, 143, 14, 389, 255, 54, 80, 799;
    0, 0, 613, 393, 1003, 941, 193, 939, 243;
    0, 0, 0, 556, 543, 356, 359, 784, 910;
    0, 0, 0, 0, 510, 548, 322, 604, 33;
    0, 0, 0, 0, 0, 15, 875, 946, 490;
    0, 0, 0, 0, 0, 0, 87, 160, 273;
    0, 0, 0, 0, 0, 0, 0, 345, 287;
    0, 0, 0, 0, 0, 0, 0, 0, 803]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt4 : residualMinor (4 : F) 1 = secondValue 4 := by
  apply value_of_factors secondLower4 secondUpper4
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower5 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    13, 1, 0, 0, 0, 0, 0, 0, 0;
    880, 363, 1, 0, 0, 0, 0, 0, 0;
    833, 804, 306, 1, 0, 0, 0, 0, 0;
    544, 10, 907, 1, 1, 0, 0, 0, 0;
    255, 722, 690, 570, 480, 1, 0, 0, 0;
    101, 82, 333, 242, 162, 272, 1, 0, 0;
    262, 461, 924, 247, 144, 869, 633, 1, 0;
    936, 567, 456, 832, 302, 605, 217, 531, 1]

private def firstUpper5 : Matrix (Fin 9) (Fin 9) F :=
  !![960, 302, 906, 950, 105, 511, 180, 713, 215;
    0, 917, 52, 391, 381, 328, 102, 504, 997;
    0, 0, 274, 535, 962, 848, 828, 576, 820;
    0, 0, 0, 360, 45, 386, 643, 750, 751;
    0, 0, 0, 0, 849, 161, 759, 203, 626;
    0, 0, 0, 0, 0, 999, 961, 719, 847;
    0, 0, 0, 0, 0, 0, 875, 542, 452;
    0, 0, 0, 0, 0, 0, 0, 58, 192;
    0, 0, 0, 0, 0, 0, 0, 0, 745]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt5 : residualMinor (5 : F) 0 = firstValue 5 := by
  apply value_of_factors firstLower5 firstUpper5
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower5 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    709, 1, 0, 0, 0, 0, 0, 0, 0;
    680, 447, 1, 0, 0, 0, 0, 0, 0;
    492, 784, 123, 1, 0, 0, 0, 0, 0;
    949, 958, 759, 309, 1, 0, 0, 0, 0;
    534, 266, 675, 54, 620, 1, 0, 0, 0;
    630, 491, 898, 276, 457, 749, 1, 0, 0;
    730, 265, 601, 853, 557, 163, 211, 1, 0;
    520, 75, 746, 41, 185, 458, 162, 363, 1]

private def secondUpper5 : Matrix (Fin 9) (Fin 9) F :=
  !![642, 100, 1007, 716, 1005, 47, 515, 729, 764;
    0, 537, 131, 516, 546, 891, 547, 439, 922;
    0, 0, 465, 614, 413, 113, 100, 962, 670;
    0, 0, 0, 549, 430, 783, 294, 822, 758;
    0, 0, 0, 0, 28, 618, 765, 288, 177;
    0, 0, 0, 0, 0, 381, 507, 643, 452;
    0, 0, 0, 0, 0, 0, 585, 696, 559;
    0, 0, 0, 0, 0, 0, 0, 742, 277;
    0, 0, 0, 0, 0, 0, 0, 0, 309]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt5 : residualMinor (5 : F) 1 = secondValue 5 := by
  apply value_of_factors secondLower5 secondUpper5
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower6 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    916, 1, 0, 0, 0, 0, 0, 0, 0;
    590, 90, 1, 0, 0, 0, 0, 0, 0;
    115, 525, 571, 1, 0, 0, 0, 0, 0;
    790, 935, 250, 347, 1, 0, 0, 0, 0;
    846, 186, 127, 89, 695, 1, 0, 0, 0;
    560, 218, 650, 124, 570, 134, 1, 0, 0;
    590, 256, 636, 471, 986, 547, 382, 1, 0;
    686, 96, 656, 145, 625, 308, 255, 995, 1]

private def firstUpper6 : Matrix (Fin 9) (Fin 9) F :=
  !![702, 886, 537, 16, 275, 74, 219, 523, 770;
    0, 886, 940, 592, 552, 632, 320, 339, 251;
    0, 0, 298, 854, 321, 524, 921, 178, 979;
    0, 0, 0, 404, 632, 647, 675, 675, 997;
    0, 0, 0, 0, 941, 299, 797, 570, 506;
    0, 0, 0, 0, 0, 614, 21, 446, 358;
    0, 0, 0, 0, 0, 0, 829, 954, 173;
    0, 0, 0, 0, 0, 0, 0, 30, 774;
    0, 0, 0, 0, 0, 0, 0, 0, 108]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt6 : residualMinor (6 : F) 0 = firstValue 6 := by
  apply value_of_factors firstLower6 firstUpper6
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower6 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    926, 1, 0, 0, 0, 0, 0, 0, 0;
    264, 479, 1, 0, 0, 0, 0, 0, 0;
    201, 513, 794, 1, 0, 0, 0, 0, 0;
    445, 414, 397, 173, 1, 0, 0, 0, 0;
    224, 600, 203, 548, 926, 1, 0, 0, 0;
    170, 20, 3, 445, 116, 368, 1, 0, 0;
    606, 398, 596, 1001, 575, 513, 402, 1, 0;
    974, 360, 358, 753, 184, 608, 335, 988, 1]

private def secondUpper6 : Matrix (Fin 9) (Fin 9) F :=
  !![317, 92, 490, 234, 426, 678, 818, 462, 511;
    0, 790, 750, 364, 245, 583, 424, 136, 315;
    0, 0, 901, 990, 594, 1, 205, 796, 370;
    0, 0, 0, 814, 994, 192, 494, 838, 265;
    0, 0, 0, 0, 97, 687, 28, 1003, 785;
    0, 0, 0, 0, 0, 978, 103, 807, 388;
    0, 0, 0, 0, 0, 0, 311, 189, 278;
    0, 0, 0, 0, 0, 0, 0, 278, 246;
    0, 0, 0, 0, 0, 0, 0, 0, 123]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt6 : residualMinor (6 : F) 1 = secondValue 6 := by
  apply value_of_factors secondLower6 secondUpper6
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def firstLower7 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    698, 1, 0, 0, 0, 0, 0, 0, 0;
    778, 853, 1, 0, 0, 0, 0, 0, 0;
    106, 90, 864, 1, 0, 0, 0, 0, 0;
    88, 56, 143, 3, 1, 0, 0, 0, 0;
    851, 640, 365, 307, 223, 1, 0, 0, 0;
    73, 725, 940, 858, 190, 650, 1, 0, 0;
    466, 1004, 314, 789, 954, 447, 231, 1, 0;
    309, 252, 761, 423, 229, 619, 677, 73, 1]

private def firstUpper7 : Matrix (Fin 9) (Fin 9) F :=
  !![690, 525, 983, 197, 210, 381, 54, 133, 777;
    0, 479, 192, 203, 248, 210, 788, 23, 593;
    0, 0, 561, 968, 650, 213, 134, 165, 680;
    0, 0, 0, 310, 922, 935, 406, 285, 667;
    0, 0, 0, 0, 321, 962, 640, 917, 734;
    0, 0, 0, 0, 0, 453, 55, 377, 12;
    0, 0, 0, 0, 0, 0, 887, 293, 716;
    0, 0, 0, 0, 0, 0, 0, 296, 441;
    0, 0, 0, 0, 0, 0, 0, 0, 265]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem firstAt7 : residualMinor (7 : F) 0 = firstValue 7 := by
  apply value_of_factors firstLower7 firstUpper7
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

private def secondLower7 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    140, 1, 0, 0, 0, 0, 0, 0, 0;
    712, 987, 1, 0, 0, 0, 0, 0, 0;
    664, 483, 701, 1, 0, 0, 0, 0, 0;
    415, 164, 524, 37, 1, 0, 0, 0, 0;
    757, 681, 924, 473, 978, 1, 0, 0, 0;
    496, 705, 601, 264, 267, 787, 1, 0, 0;
    914, 695, 305, 58, 362, 543, 625, 1, 0;
    455, 48, 437, 11, 645, 890, 170, 273, 1]

private def secondUpper7 : Matrix (Fin 9) (Fin 9) F :=
  !![729, 53, 929, 940, 286, 468, 712, 450, 732;
    0, 305, 307, 55, 843, 846, 349, 596, 535;
    0, 0, 978, 365, 796, 726, 127, 617, 237;
    0, 0, 0, 503, 929, 741, 261, 505, 1003;
    0, 0, 0, 0, 161, 613, 183, 119, 881;
    0, 0, 0, 0, 0, 667, 116, 239, 207;
    0, 0, 0, 0, 0, 0, 326, 866, 823;
    0, 0, 0, 0, 0, 0, 0, 499, 621;
    0, 0, 0, 0, 0, 0, 0, 0, 507]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the entries and the diagonal product of the supplied factors.
private theorem secondAt7 : residualMinor (7 : F) 1 = secondValue 7 := by
  apply value_of_factors secondLower7 secondUpper7
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel
  · decide +kernel

/-- The checked point values for residues 0 through 7. -/
theorem pointValues (t : Fin 8) :
    let q : F := ((0 + (t : ℕ)) : ℕ)
    residualMinor q 0 = firstValue q ∧ residualMinor q 1 = secondValue q := by
  fin_cases t
  · exact ⟨firstAt0, secondAt0⟩
  · exact ⟨firstAt1, secondAt1⟩
  · exact ⟨firstAt2, secondAt2⟩
  · exact ⟨firstAt3, secondAt3⟩
  · exact ⟨firstAt4, secondAt4⟩
  · exact ⟨firstAt5, secondAt5⟩
  · exact ⟨firstAt6, secondAt6⟩
  · exact ⟨firstAt7, secondAt7⟩

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch0
