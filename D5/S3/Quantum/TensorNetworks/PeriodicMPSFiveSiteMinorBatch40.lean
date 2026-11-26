/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch40
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteMinorBatch40
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Triangular factor certificates for the five-site critical minor evaluations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorEvaluation

/-! Residue-field point evaluations of the two five-site critical minors. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch40

open Matrix PeriodicMPSFiveSiteLineBezout PeriodicMPSFiveSiteLineMinors
  PeriodicMPSFiveSiteMinorEvaluation

private def firstLower40 : Matrix (Fin 9) (Fin 9) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    110, 1, 0, 0, 0, 0, 0, 0, 0;
    662, 85, 1, 0, 0, 0, 0, 0, 0;
    615, 296, 735, 1, 0, 0, 0, 0, 0;
    514, 40, 658, 167, 1, 0, 0, 0, 0;
    784, 576, 600, 125, 665, 1, 0, 0, 0;
    199, 44, 465, 890, 599, 373, 1, 0, 0;
    263, 80, 154, 264, 495, 796, 424, 1, 0;
    912, 724, 926, 476, 347, 891, 174, 770, 1]

private def firstUpper40 : Matrix (Fin 9) (Fin 9) F :=
  !![383, 458, 866, 769, 785, 876, 383, 999, 672;
    0, 964, 990, 984, 3, 851, 118, 215, 525;
    0, 0, 551, 251, 86, 21, 432, 823, 703;
    0, 0, 0, 763, 128, 224, 379, 795, 311;
    0, 0, 0, 0, 527, 838, 47, 377, 387;
    0, 0, 0, 0, 0, 838, 80, 851, 316;
    0, 0, 0, 0, 0, 0, 776, 133, 199;
    0, 0, 0, 0, 0, 0, 0, 931, 883;
    0, 0, 0, 0, 0, 0, 0, 0, 465]

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
    869, 1, 0, 0, 0, 0, 0, 0, 0;
    565, 899, 1, 0, 0, 0, 0, 0, 0;
    356, 1, 598, 1, 0, 0, 0, 0, 0;
    562, 873, 535, 687, 1, 0, 0, 0, 0;
    281, 452, 965, 600, 62, 1, 0, 0, 0;
    451, 569, 112, 415, 935, 183, 1, 0, 0;
    875, 250, 48, 230, 396, 523, 46, 1, 0;
    345, 976, 445, 235, 355, 245, 855, 65, 1]

private def secondUpper40 : Matrix (Fin 9) (Fin 9) F :=
  !![507, 51, 471, 376, 725, 750, 759, 943, 380;
    0, 971, 750, 990, 179, 411, 185, 974, 511;
    0, 0, 148, 64, 924, 289, 819, 513, 750;
    0, 0, 0, 408, 528, 804, 760, 563, 941;
    0, 0, 0, 0, 687, 589, 749, 800, 297;
    0, 0, 0, 0, 0, 159, 362, 653, 951;
    0, 0, 0, 0, 0, 0, 520, 432, 495;
    0, 0, 0, 0, 0, 0, 0, 203, 717;
    0, 0, 0, 0, 0, 0, 0, 0, 554]

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
    398, 1, 0, 0, 0, 0, 0, 0, 0;
    839, 995, 1, 0, 0, 0, 0, 0, 0;
    276, 722, 767, 1, 0, 0, 0, 0, 0;
    217, 364, 822, 594, 1, 0, 0, 0, 0;
    83, 16, 274, 429, 722, 1, 0, 0, 0;
    919, 467, 82, 352, 542, 573, 1, 0, 0;
    484, 959, 589, 342, 365, 977, 143, 1, 0;
    862, 721, 705, 506, 271, 357, 242, 160, 1]

private def firstUpper41 : Matrix (Fin 9) (Fin 9) F :=
  !![699, 168, 969, 756, 897, 145, 60, 696, 75;
    0, 233, 723, 524, 50, 860, 10, 479, 830;
    0, 0, 530, 866, 950, 287, 299, 346, 578;
    0, 0, 0, 519, 473, 176, 425, 862, 414;
    0, 0, 0, 0, 883, 720, 917, 132, 265;
    0, 0, 0, 0, 0, 777, 42, 113, 397;
    0, 0, 0, 0, 0, 0, 887, 12, 386;
    0, 0, 0, 0, 0, 0, 0, 801, 917;
    0, 0, 0, 0, 0, 0, 0, 0, 107]

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
    636, 1, 0, 0, 0, 0, 0, 0, 0;
    215, 963, 1, 0, 0, 0, 0, 0, 0;
    539, 861, 102, 1, 0, 0, 0, 0, 0;
    289, 434, 963, 874, 1, 0, 0, 0, 0;
    58, 592, 444, 909, 843, 1, 0, 0, 0;
    9, 998, 249, 726, 227, 571, 1, 0, 0;
    627, 426, 742, 637, 564, 999, 770, 1, 0;
    4, 108, 587, 553, 73, 743, 594, 654, 1]

private def secondUpper41 : Matrix (Fin 9) (Fin 9) F :=
  !![26, 516, 323, 442, 998, 302, 326, 646, 233;
    0, 252, 346, 120, 812, 695, 192, 828, 545;
    0, 0, 183, 507, 485, 258, 340, 534, 624;
    0, 0, 0, 803, 719, 928, 930, 389, 611;
    0, 0, 0, 0, 416, 53, 178, 170, 463;
    0, 0, 0, 0, 0, 340, 656, 479, 319;
    0, 0, 0, 0, 0, 0, 1004, 824, 609;
    0, 0, 0, 0, 0, 0, 0, 554, 579;
    0, 0, 0, 0, 0, 0, 0, 0, 15]

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
    675, 1, 0, 0, 0, 0, 0, 0, 0;
    389, 717, 1, 0, 0, 0, 0, 0, 0;
    592, 331, 344, 1, 0, 0, 0, 0, 0;
    658, 657, 434, 941, 1, 0, 0, 0, 0;
    392, 311, 732, 993, 241, 1, 0, 0, 0;
    974, 1002, 318, 459, 393, 128, 1, 0, 0;
    425, 870, 748, 1004, 649, 550, 812, 1, 0;
    524, 994, 824, 210, 395, 6, 844, 965, 1]

private def firstUpper42 : Matrix (Fin 9) (Fin 9) F :=
  !![959, 701, 783, 683, 759, 303, 643, 423, 135;
    0, 937, 456, 64, 444, 599, 38, 980, 0;
    0, 0, 795, 664, 903, 11, 633, 604, 672;
    0, 0, 0, 59, 691, 706, 879, 625, 897;
    0, 0, 0, 0, 816, 599, 958, 616, 277;
    0, 0, 0, 0, 0, 11, 465, 948, 509;
    0, 0, 0, 0, 0, 0, 239, 867, 95;
    0, 0, 0, 0, 0, 0, 0, 939, 684;
    0, 0, 0, 0, 0, 0, 0, 0, 906]

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
    852, 1, 0, 0, 0, 0, 0, 0, 0;
    198, 154, 1, 0, 0, 0, 0, 0, 0;
    107, 177, 611, 1, 0, 0, 0, 0, 0;
    951, 775, 97, 60, 1, 0, 0, 0, 0;
    594, 853, 352, 708, 518, 1, 0, 0, 0;
    584, 474, 240, 205, 336, 961, 1, 0, 0;
    429, 31, 664, 500, 412, 50, 268, 1, 0;
    929, 663, 881, 321, 213, 149, 990, 758, 1]

private def secondUpper42 : Matrix (Fin 9) (Fin 9) F :=
  !![573, 152, 99, 997, 636, 708, 459, 130, 802;
    0, 539, 673, 110, 158, 463, 617, 179, 104;
    0, 0, 554, 20, 102, 887, 287, 242, 464;
    0, 0, 0, 27, 597, 306, 711, 486, 943;
    0, 0, 0, 0, 620, 988, 656, 77, 449;
    0, 0, 0, 0, 0, 626, 470, 922, 282;
    0, 0, 0, 0, 0, 0, 836, 845, 611;
    0, 0, 0, 0, 0, 0, 0, 25, 925;
    0, 0, 0, 0, 0, 0, 0, 0, 889]

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
    918, 1, 0, 0, 0, 0, 0, 0, 0;
    406, 455, 1, 0, 0, 0, 0, 0, 0;
    439, 774, 867, 1, 0, 0, 0, 0, 0;
    842, 187, 39, 241, 1, 0, 0, 0, 0;
    687, 904, 108, 235, 773, 1, 0, 0, 0;
    503, 391, 175, 455, 212, 105, 1, 0, 0;
    480, 25, 452, 301, 870, 102, 687, 1, 0;
    781, 82, 869, 525, 672, 615, 626, 471, 1]

private def firstUpper43 : Matrix (Fin 9) (Fin 9) F :=
  !![161, 66, 90, 410, 304, 899, 683, 975, 556;
    0, 509, 696, 816, 823, 693, 376, 684, 611;
    0, 0, 934, 218, 769, 29, 636, 567, 382;
    0, 0, 0, 827, 336, 424, 817, 735, 837;
    0, 0, 0, 0, 430, 990, 463, 372, 239;
    0, 0, 0, 0, 0, 480, 120, 861, 581;
    0, 0, 0, 0, 0, 0, 336, 132, 492;
    0, 0, 0, 0, 0, 0, 0, 425, 945;
    0, 0, 0, 0, 0, 0, 0, 0, 851]

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
    700, 1, 0, 0, 0, 0, 0, 0, 0;
    56, 83, 1, 0, 0, 0, 0, 0, 0;
    764, 46, 342, 1, 0, 0, 0, 0, 0;
    192, 601, 580, 277, 1, 0, 0, 0, 0;
    436, 450, 874, 380, 350, 1, 0, 0, 0;
    509, 692, 910, 900, 769, 175, 1, 0, 0;
    968, 785, 746, 145, 656, 315, 160, 1, 0;
    387, 403, 253, 9, 978, 728, 86, 347, 1]

private def secondUpper43 : Matrix (Fin 9) (Fin 9) F :=
  !![130, 85, 411, 563, 519, 107, 290, 693, 107;
    0, 588, 443, 249, 342, 379, 590, 980, 231;
    0, 0, 750, 434, 275, 156, 384, 251, 692;
    0, 0, 0, 730, 921, 912, 258, 353, 574;
    0, 0, 0, 0, 232, 872, 657, 452, 828;
    0, 0, 0, 0, 0, 428, 969, 727, 428;
    0, 0, 0, 0, 0, 0, 852, 265, 17;
    0, 0, 0, 0, 0, 0, 0, 693, 66;
    0, 0, 0, 0, 0, 0, 0, 0, 593]

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
    118, 1, 0, 0, 0, 0, 0, 0, 0;
    400, 548, 1, 0, 0, 0, 0, 0, 0;
    776, 705, 17, 1, 0, 0, 0, 0, 0;
    189, 877, 206, 37, 1, 0, 0, 0, 0;
    23, 679, 995, 237, 741, 1, 0, 0, 0;
    336, 704, 694, 677, 86, 888, 1, 0, 0;
    319, 1003, 975, 716, 685, 879, 468, 1, 0;
    533, 624, 530, 100, 947, 408, 491, 875, 1]

private def firstUpper44 : Matrix (Fin 9) (Fin 9) F :=
  !![578, 105, 787, 913, 895, 551, 81, 735, 566;
    0, 366, 754, 851, 1007, 498, 515, 541, 672;
    0, 0, 274, 544, 638, 651, 895, 369, 307;
    0, 0, 0, 762, 168, 630, 178, 43, 197;
    0, 0, 0, 0, 872, 735, 300, 644, 340;
    0, 0, 0, 0, 0, 464, 289, 379, 665;
    0, 0, 0, 0, 0, 0, 877, 1008, 320;
    0, 0, 0, 0, 0, 0, 0, 362, 820;
    0, 0, 0, 0, 0, 0, 0, 0, 758]

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
    357, 1, 0, 0, 0, 0, 0, 0, 0;
    725, 981, 1, 0, 0, 0, 0, 0, 0;
    298, 1008, 165, 1, 0, 0, 0, 0, 0;
    434, 842, 933, 16, 1, 0, 0, 0, 0;
    154, 132, 773, 390, 82, 1, 0, 0, 0;
    888, 236, 91, 362, 754, 697, 1, 0, 0;
    978, 730, 631, 804, 946, 910, 128, 1, 0;
    9, 670, 79, 966, 924, 805, 791, 630, 1]

private def secondUpper44 : Matrix (Fin 9) (Fin 9) F :=
  !![986, 31, 914, 633, 75, 88, 873, 376, 181;
    0, 680, 401, 657, 131, 803, 103, 462, 825;
    0, 0, 160, 71, 99, 607, 282, 221, 500;
    0, 0, 0, 789, 639, 865, 546, 812, 804;
    0, 0, 0, 0, 943, 866, 481, 968, 959;
    0, 0, 0, 0, 0, 647, 522, 464, 180;
    0, 0, 0, 0, 0, 0, 355, 210, 457;
    0, 0, 0, 0, 0, 0, 0, 908, 695;
    0, 0, 0, 0, 0, 0, 0, 0, 596]

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
    805, 1, 0, 0, 0, 0, 0, 0, 0;
    421, 96, 1, 0, 0, 0, 0, 0, 0;
    247, 993, 126, 1, 0, 0, 0, 0, 0;
    780, 403, 176, 242, 1, 0, 0, 0, 0;
    421, 484, 580, 341, 796, 1, 0, 0, 0;
    713, 786, 863, 646, 609, 33, 1, 0, 0;
    426, 931, 688, 582, 529, 776, 142, 1, 0;
    944, 353, 560, 95, 335, 423, 877, 898, 1]

private def firstUpper45 : Matrix (Fin 9) (Fin 9) F :=
  !![766, 745, 668, 172, 566, 628, 45, 981, 115;
    0, 109, 178, 275, 843, 830, 185, 803, 404;
    0, 0, 74, 553, 715, 837, 764, 215, 539;
    0, 0, 0, 888, 681, 220, 681, 197, 190;
    0, 0, 0, 0, 917, 808, 715, 540, 891;
    0, 0, 0, 0, 0, 427, 984, 218, 62;
    0, 0, 0, 0, 0, 0, 4, 130, 62;
    0, 0, 0, 0, 0, 0, 0, 496, 532;
    0, 0, 0, 0, 0, 0, 0, 0, 20]

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
    344, 1, 0, 0, 0, 0, 0, 0, 0;
    992, 175, 1, 0, 0, 0, 0, 0, 0;
    733, 170, 932, 1, 0, 0, 0, 0, 0;
    995, 145, 915, 335, 1, 0, 0, 0, 0;
    300, 454, 882, 112, 105, 1, 0, 0, 0;
    474, 919, 729, 659, 254, 519, 1, 0, 0;
    113, 75, 301, 167, 352, 217, 1006, 1, 0;
    372, 305, 683, 720, 376, 742, 645, 634, 1]

private def secondUpper45 : Matrix (Fin 9) (Fin 9) F :=
  !![200, 839, 227, 240, 347, 766, 756, 85, 186;
    0, 446, 735, 680, 99, 706, 344, 482, 743;
    0, 0, 76, 589, 758, 289, 211, 772, 226;
    0, 0, 0, 716, 234, 954, 102, 415, 185;
    0, 0, 0, 0, 719, 905, 836, 416, 171;
    0, 0, 0, 0, 0, 393, 557, 560, 293;
    0, 0, 0, 0, 0, 0, 624, 428, 528;
    0, 0, 0, 0, 0, 0, 0, 273, 317;
    0, 0, 0, 0, 0, 0, 0, 0, 109]

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
    308, 1, 0, 0, 0, 0, 0, 0, 0;
    604, 122, 1, 0, 0, 0, 0, 0, 0;
    43, 918, 849, 1, 0, 0, 0, 0, 0;
    700, 296, 610, 834, 1, 0, 0, 0, 0;
    254, 648, 466, 862, 95, 1, 0, 0, 0;
    155, 786, 871, 128, 617, 657, 1, 0, 0;
    165, 657, 580, 854, 51, 176, 266, 1, 0;
    107, 215, 94, 399, 664, 406, 902, 988, 1]

private def firstUpper46 : Matrix (Fin 9) (Fin 9) F :=
  !![525, 459, 683, 901, 194, 465, 603, 203, 705;
    0, 304, 457, 212, 864, 635, 949, 676, 401;
    0, 0, 1005, 384, 475, 147, 356, 257, 769;
    0, 0, 0, 163, 120, 876, 782, 637, 538;
    0, 0, 0, 0, 862, 298, 721, 827, 973;
    0, 0, 0, 0, 0, 355, 57, 323, 272;
    0, 0, 0, 0, 0, 0, 46, 418, 306;
    0, 0, 0, 0, 0, 0, 0, 437, 130;
    0, 0, 0, 0, 0, 0, 0, 0, 211]

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
    33, 1, 0, 0, 0, 0, 0, 0, 0;
    349, 22, 1, 0, 0, 0, 0, 0, 0;
    766, 845, 620, 1, 0, 0, 0, 0, 0;
    554, 669, 978, 519, 1, 0, 0, 0, 0;
    127, 34, 461, 4, 489, 1, 0, 0, 0;
    396, 945, 386, 66, 587, 144, 1, 0, 0;
    426, 355, 919, 104, 500, 984, 18, 1, 0;
    623, 912, 440, 146, 615, 29, 1005, 769, 1]

private def secondUpper46 : Matrix (Fin 9) (Fin 9) F :=
  !![135, 55, 430, 295, 102, 776, 944, 646, 356;
    0, 619, 885, 600, 746, 194, 135, 513, 966;
    0, 0, 78, 247, 528, 647, 606, 889, 72;
    0, 0, 0, 344, 524, 970, 355, 260, 984;
    0, 0, 0, 0, 327, 357, 240, 609, 416;
    0, 0, 0, 0, 0, 873, 735, 375, 902;
    0, 0, 0, 0, 0, 0, 967, 981, 51;
    0, 0, 0, 0, 0, 0, 0, 289, 336;
    0, 0, 0, 0, 0, 0, 0, 0, 326]

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
    351, 1, 0, 0, 0, 0, 0, 0, 0;
    943, 0, 1, 0, 0, 0, 0, 0, 0;
    863, 243, 973, 1, 0, 0, 0, 0, 0;
    867, 189, 437, 504, 1, 0, 0, 0, 0;
    803, 297, 79, 163, 159, 1, 0, 0, 0;
    620, 790, 890, 268, 785, 877, 1, 0, 0;
    873, 699, 600, 19, 720, 576, 585, 1, 0;
    708, 164, 1002, 361, 555, 120, 982, 829, 1]

private def firstUpper47 : Matrix (Fin 9) (Fin 9) F :=
  !![752, 569, 813, 596, 839, 995, 839, 774, 779;
    0, 135, 408, 552, 156, 238, 713, 537, 894;
    0, 0, 18, 882, 540, 670, 806, 430, 850;
    0, 0, 0, 605, 75, 474, 64, 484, 706;
    0, 0, 0, 0, 801, 141, 199, 712, 100;
    0, 0, 0, 0, 0, 44, 276, 623, 271;
    0, 0, 0, 0, 0, 0, 321, 403, 230;
    0, 0, 0, 0, 0, 0, 0, 28, 437;
    0, 0, 0, 0, 0, 0, 0, 0, 848]

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
    820, 1, 0, 0, 0, 0, 0, 0, 0;
    575, 673, 1, 0, 0, 0, 0, 0, 0;
    320, 16, 63, 1, 0, 0, 0, 0, 0;
    238, 911, 334, 1000, 1, 0, 0, 0, 0;
    892, 838, 99, 549, 94, 1, 0, 0, 0;
    638, 389, 389, 382, 573, 240, 1, 0, 0;
    962, 345, 48, 636, 654, 1004, 484, 1, 0;
    320, 410, 541, 411, 23, 149, 708, 557, 1]

private def secondUpper47 : Matrix (Fin 9) (Fin 9) F :=
  !![805, 172, 11, 686, 235, 542, 819, 906, 766;
    0, 292, 285, 378, 36, 898, 988, 494, 362;
    0, 0, 480, 840, 730, 753, 203, 1007, 921;
    0, 0, 0, 834, 299, 767, 539, 430, 785;
    0, 0, 0, 0, 368, 596, 114, 134, 326;
    0, 0, 0, 0, 0, 515, 259, 243, 52;
    0, 0, 0, 0, 0, 0, 328, 478, 807;
    0, 0, 0, 0, 0, 0, 0, 308, 59;
    0, 0, 0, 0, 0, 0, 0, 0, 36]

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

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteMinorBatch40
