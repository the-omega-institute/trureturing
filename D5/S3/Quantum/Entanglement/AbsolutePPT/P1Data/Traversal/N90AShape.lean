/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N90AShape
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N90AShape
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N90AShape.checked_walk
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N90A
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N90A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private def starts : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 11, 2, 13, 14, 13, 2, 17, 18, 17, 20, 17, 22, 23, 22, 25, 22, 17, 28, 29, 28, 31, 28, 33, 28, 17, 36, 17, 38, 39, 38, 17, 42, 43, 42, 45, 42, 17, 48, 49, 48, 51, 48, 53, 54, 53, 48, 17, 58, 17, 60, 61, 60, 17, 2, 65, 2, 67, 68, 67, 70, 67, 72, 73, 72, 67, 76, 67, 2, 1, 80, 1, 82, 83, 84, 83, 86, 83, 82, 89, 82, 1, 92, 93, 92, 95, 92, 97, 98, 97, 92, 101, 92, 103, 92, 105, 106, 105, 92, 109, 110, 111, 110, 109, 92, 115, 92, 117, 118, 117, 92, 121, 122, 121, 92, 125, 92, 127, 92, 1, 0, 131, 132, 133, 134, 135, 134, 133, 132, 131, 140, 141, 142, 141, 140, 131, 146, 147, 148, 149, 148, 151, 152, 153, 152, 151, 148, 147, 146, 159, 160, 161, 162, 163, 162, 161, 166, 161, 168, 169, 168, 171, 168, 161, 160, 159, 146, 131, 178, 179, 180, 181, 180, 179, 178, 185, 178, 187, 178, 189, 190, 189, 178, 193, 194, 195, 194, 193, 178, 199, 200, 201, 200, 199, 204, 199, 206, 207, 208, 207, 206, 211, 206, 213, 214, 213, 206, 217, 218, 219, 218, 217, 206, 199, 224, 199, 226, 227, 228, 229, 228, 227, 232, 227, 234, 227, 226, 237, 226, 199, 240, 241, 242, 241, 240, 199, 178, 247, 178, 249, 250, 251, 252, 251, 250, 255, 250, 257, 250, 249, 260, 261, 262, 261, 264, 261, 260, 249, 178, 131, 270, 271, 272, 273, 274, 275, 274, 273, 272, 271, 270, 281, 282, 283, 284, 285, 286, 287, 286, 285, 284, 291, 284, 283, 282, 281, 270, 297, 298, 299, 300, 301, 302, 303, 304, 303, 302, 301, 300, 299, 298, 311, 298, 313, 314, 315, 316, 317, 316, 315, 320, 315, 314, 313, 324, 325, 326, 325, 324, 313, 298, 297, 332, 333, 332, 335, 336, 337, 336, 335, 340, 341, 342, 341, 340, 335, 332, 347, 348, 349, 350, 349, 352, 349, 348, 355, 356, 355, 358, 355, 348, 361, 348, 363, 348, 347, 366, 367, 366, 369, 366, 371, 366, 373, 366, 347, 376, 347, 378, 347, 332, 297, 382, 383, 384, 385, 386, 385, 384, 389, 384, 383, 382, 393, 394, 395, 396, 395, 394, 399, 400, 399, 402, 399, 394, 405, 394, 393, 408, 409, 408, 393, 382, 297, 414, 415, 416, 415, 418, 419, 418, 415, 422, 415, 414, 425, 414, 427, 428, 429, 428, 431, 432, 431, 428, 435, 428, 427, 438, 427, 414, 297, 270, 443, 444, 445, 446, 447, 446, 449, 446, 445, 444, 453, 444, 455, 456, 455, 458, 459, 458, 461, 458, 455, 444, 443, 466, 467, 468, 467, 470, 471, 470, 473, 474, 473, 470, 467, 466, 479, 480, 481, 482, 483, 482, 485, 482, 481, 488, 481, 490, 481, 492, 481, 480, 495, 480, 497, 498, 497, 500, 497, 502, 497, 480, 505, 506, 505, 508, 505, 510, 505, 512, 505, 480, 479, 516, 479, 518, 519, 518, 521, 518, 523, 518, 525, 526, 525, 528, 525, 530, 525, 518, 479, 534, 535, 534, 537, 534, 539, 534, 541, 534, 543, 534, 545, 534, 479, 466, 549, 466, 551, 552, 553, 552, 551, 556, 551, 558, 551, 560, 551, 562, 563, 562, 565, 562, 567, 562, 569, 562, 571, 562, 551, 466, 575, 576, 575, 578, 575, 580, 575, 582, 575, 584, 575, 586, 575, 588, 575, 466, 443, 592, 593, 594, 595, 596, 595, 594, 599, 600, 599, 594, 593, 604, 593, 592, 607, 608, 609, 608, 611, 608, 613, 608, 607, 592, 617, 618, 619, 618, 621, 618, 623, 618, 625, 618, 617, 628, 629, 628, 617, 592, 443, 634, 635, 636, 635, 634, 639, 634, 641, 634, 643, 634, 645, 646, 645, 648, 649, 648, 651, 648, 645, 654, 645, 656, 645, 658, 645, 634, 443, 662, 663, 664, 663, 666, 663, 668, 663, 662, 671, 662, 673, 662, 675, 662, 677, 662, 679, 662, 681, 682, 681, 684, 681, 686, 681, 662, 689, 662, 443, 270, 693, 694, 695, 696, 695, 698, 699, 698, 701, 702, 701, 698, 695, 706, 707, 706, 709, 706, 711, 706, 695, 694, 715, 716, 717, 718, 719, 718, 717, 722, 717, 716, 715, 726, 727, 728, 729, 728, 727, 732, 727, 734, 727, 726, 737, 738, 737, 726, 715, 694, 693, 744, 745, 746, 745, 748, 749, 748, 751, 748, 745, 754, 755, 754, 745, 758, 745, 760, 761, 760, 745, 744, 693, 766, 767, 768, 767, 770, 767, 772, 767, 774, 767, 776, 767, 778, 767, 780, 767, 782, 783, 782, 785, 782, 787, 782, 767, 766, 791, 792, 791, 766, 693, 270, 797, 798, 797, 800, 801, 800, 797, 804, 797, 806, 797, 808, 797, 810, 811, 812, 811, 810, 815, 810, 817, 818, 817, 820, 817, 822, 817, 810, 825, 810, 827, 810, 829, 810, 797, 270, 833, 834, 835, 836, 835, 838, 839, 838, 835, 834, 833, 844, 833, 846, 847, 848, 847, 846, 851, 852, 853, 852, 851, 846, 833, 858, 859, 860, 861, 860, 859, 864, 859, 858, 867, 858, 869, 870, 869, 858, 833, 874, 875, 876, 877, 878, 877, 876, 875, 882, 883, 884, 883, 882, 887, 888, 887, 890, 887, 892, 887, 894, 887, 882, 875, 898, 875, 900, 901, 900, 903, 900, 905, 900, 875, 874, 909, 910, 911, 910, 909, 914, 909, 916, 909, 918, 909, 874, 921, 874, 923, 924, 923, 926, 923, 928, 923, 930, 931, 930, 933, 930, 935, 930, 923, 874, 939, 940, 939, 942, 939, 944, 939, 946, 939, 948, 939, 950, 939, 952, 939, 874, 833, 956, 833, 958, 959, 960, 959, 958, 963, 958, 965, 958, 967, 958, 969, 970, 969, 972, 969, 974, 969, 958, 833, 978, 979, 978, 981, 978, 983, 978, 985, 978, 987, 978, 833, 990, 833, 992, 993, 992, 833, 996, 833, 998, 833, 1000, 833, 1002, 1003, 1002, 1005, 1002, 1007, 1002, 833, 1010, 833, 270, 131, 1014, 1015, 1016, 1017, 1018, 1019, 1018, 1021, 1018, 1017, 1024, 1025, 1026, 1025, 1028, 1025, 1024, 1017, 1016, 1033, 1016, 1015, 1036, 1015, 1014, 1039, 1014, 1041, 1042, 1043, 1044, 1043, 1046, 1043, 1042, 1049, 1042, 1051, 1042, 1053, 1042, 1055, 1042, 1057, 1058, 1057, 1060, 1057, 1062, 1057, 1042, 1065, 1042, 1067, 1042, 1069, 1042, 1071, 1042, 1041, 1074, 1041, 1014, 131, 1078, 1079, 1080, 1079, 1078, 1083, 1084, 1085, 1086, 1085, 1084, 1089, 1084, 1091, 1084, 1083, 1078, 1095, 1096, 1095, 1078, 1099, 1100, 1099, 1078, 1103, 1078, 1105, 1106, 1107, 1106, 1109, 1106, 1105, 1112, 1113, 1114, 1113, 1112, 1117, 1112, 1119, 1112, 1105, 1122, 1105, 1124, 1105, 1126, 1105, 1078, 131, 1130, 1131, 1130, 1133, 1130, 1135, 1130, 1137, 1138, 1137, 1130, 1141, 1130, 131, 0]
private def start (i : Nat) : Nat := starts[i]?.getD i

private def Step (i : Nat) : Prop :=
  start i ≤ i ∧ match (node nodes i).rule with
  | .split _ _ l r => l < i ∧ r < i ∧ start l = start i ∧ start r = l+1 ∧ r+1 = i
  | _ => start i = i
private instance (i : Nat) : Decidable (Step i) := by
  unfold Step
  cases (node nodes i).rule <;> infer_instance

private theorem checked_shape_0 : ∀ k : Fin 16, Step (0+k.val) := by decide +kernel

private theorem checked_shape_16 : ∀ k : Fin 16, Step (16+k.val) := by decide +kernel

private theorem checked_shape_32 : ∀ k : Fin 16, Step (32+k.val) := by decide +kernel

private theorem checked_shape_48 : ∀ k : Fin 16, Step (48+k.val) := by decide +kernel

private theorem checked_shape_64 : ∀ k : Fin 16, Step (64+k.val) := by decide +kernel

private theorem checked_shape_80 : ∀ k : Fin 16, Step (80+k.val) := by decide +kernel

private theorem checked_shape_96 : ∀ k : Fin 16, Step (96+k.val) := by decide +kernel

private theorem checked_shape_112 : ∀ k : Fin 16, Step (112+k.val) := by decide +kernel

private theorem checked_shape_128 : ∀ k : Fin 16, Step (128+k.val) := by decide +kernel

private theorem checked_shape_144 : ∀ k : Fin 16, Step (144+k.val) := by decide +kernel

private theorem checked_shape_160 : ∀ k : Fin 16, Step (160+k.val) := by decide +kernel

private theorem checked_shape_176 : ∀ k : Fin 16, Step (176+k.val) := by decide +kernel

private theorem checked_shape_192 : ∀ k : Fin 16, Step (192+k.val) := by decide +kernel

private theorem checked_shape_208 : ∀ k : Fin 16, Step (208+k.val) := by decide +kernel

private theorem checked_shape_224 : ∀ k : Fin 16, Step (224+k.val) := by decide +kernel

private theorem checked_shape_240 : ∀ k : Fin 16, Step (240+k.val) := by decide +kernel

private theorem checked_shape_256 : ∀ k : Fin 16, Step (256+k.val) := by decide +kernel

private theorem checked_shape_272 : ∀ k : Fin 16, Step (272+k.val) := by decide +kernel

private theorem checked_shape_288 : ∀ k : Fin 16, Step (288+k.val) := by decide +kernel

private theorem checked_shape_304 : ∀ k : Fin 16, Step (304+k.val) := by decide +kernel

private theorem checked_shape_320 : ∀ k : Fin 16, Step (320+k.val) := by decide +kernel

private theorem checked_shape_336 : ∀ k : Fin 16, Step (336+k.val) := by decide +kernel

private theorem checked_shape_352 : ∀ k : Fin 16, Step (352+k.val) := by decide +kernel

private theorem checked_shape_368 : ∀ k : Fin 16, Step (368+k.val) := by decide +kernel

private theorem checked_shape_384 : ∀ k : Fin 16, Step (384+k.val) := by decide +kernel

private theorem checked_shape_400 : ∀ k : Fin 16, Step (400+k.val) := by decide +kernel

private theorem checked_shape_416 : ∀ k : Fin 16, Step (416+k.val) := by decide +kernel

private theorem checked_shape_432 : ∀ k : Fin 16, Step (432+k.val) := by decide +kernel

private theorem checked_shape_448 : ∀ k : Fin 16, Step (448+k.val) := by decide +kernel

private theorem checked_shape_464 : ∀ k : Fin 16, Step (464+k.val) := by decide +kernel

private theorem checked_shape_480 : ∀ k : Fin 16, Step (480+k.val) := by decide +kernel

private theorem checked_shape_496 : ∀ k : Fin 16, Step (496+k.val) := by decide +kernel

private theorem checked_shape_512 : ∀ k : Fin 16, Step (512+k.val) := by decide +kernel

private theorem checked_shape_528 : ∀ k : Fin 16, Step (528+k.val) := by decide +kernel

private theorem checked_shape_544 : ∀ k : Fin 16, Step (544+k.val) := by decide +kernel

private theorem checked_shape_560 : ∀ k : Fin 16, Step (560+k.val) := by decide +kernel

private theorem checked_shape_576 : ∀ k : Fin 16, Step (576+k.val) := by decide +kernel

private theorem checked_shape_592 : ∀ k : Fin 16, Step (592+k.val) := by decide +kernel

private theorem checked_shape_608 : ∀ k : Fin 16, Step (608+k.val) := by decide +kernel

private theorem checked_shape_624 : ∀ k : Fin 16, Step (624+k.val) := by decide +kernel

private theorem checked_shape_640 : ∀ k : Fin 16, Step (640+k.val) := by decide +kernel

private theorem checked_shape_656 : ∀ k : Fin 16, Step (656+k.val) := by decide +kernel

private theorem checked_shape_672 : ∀ k : Fin 16, Step (672+k.val) := by decide +kernel

private theorem checked_shape_688 : ∀ k : Fin 16, Step (688+k.val) := by decide +kernel

private theorem checked_shape_704 : ∀ k : Fin 16, Step (704+k.val) := by decide +kernel

private theorem checked_shape_720 : ∀ k : Fin 16, Step (720+k.val) := by decide +kernel

private theorem checked_shape_736 : ∀ k : Fin 16, Step (736+k.val) := by decide +kernel

private theorem checked_shape_752 : ∀ k : Fin 16, Step (752+k.val) := by decide +kernel

private theorem checked_shape_768 : ∀ k : Fin 16, Step (768+k.val) := by decide +kernel

private theorem checked_shape_784 : ∀ k : Fin 16, Step (784+k.val) := by decide +kernel

private theorem checked_shape_800 : ∀ k : Fin 16, Step (800+k.val) := by decide +kernel

private theorem checked_shape_816 : ∀ k : Fin 16, Step (816+k.val) := by decide +kernel

private theorem checked_shape_832 : ∀ k : Fin 16, Step (832+k.val) := by decide +kernel

private theorem checked_shape_848 : ∀ k : Fin 16, Step (848+k.val) := by decide +kernel

private theorem checked_shape_864 : ∀ k : Fin 16, Step (864+k.val) := by decide +kernel

private theorem checked_shape_880 : ∀ k : Fin 16, Step (880+k.val) := by decide +kernel

private theorem checked_shape_896 : ∀ k : Fin 16, Step (896+k.val) := by decide +kernel

private theorem checked_shape_912 : ∀ k : Fin 16, Step (912+k.val) := by decide +kernel

private theorem checked_shape_928 : ∀ k : Fin 16, Step (928+k.val) := by decide +kernel

private theorem checked_shape_944 : ∀ k : Fin 16, Step (944+k.val) := by decide +kernel

private theorem checked_shape_960 : ∀ k : Fin 16, Step (960+k.val) := by decide +kernel

private theorem checked_shape_976 : ∀ k : Fin 16, Step (976+k.val) := by decide +kernel

private theorem checked_shape_992 : ∀ k : Fin 16, Step (992+k.val) := by decide +kernel

private theorem checked_shape_1008 : ∀ k : Fin 16, Step (1008+k.val) := by decide +kernel

private theorem checked_shape_1024 : ∀ k : Fin 16, Step (1024+k.val) := by decide +kernel

private theorem checked_shape_1040 : ∀ k : Fin 16, Step (1040+k.val) := by decide +kernel

private theorem checked_shape_1056 : ∀ k : Fin 16, Step (1056+k.val) := by decide +kernel

private theorem checked_shape_1072 : ∀ k : Fin 16, Step (1072+k.val) := by decide +kernel

private theorem checked_shape_1088 : ∀ k : Fin 16, Step (1088+k.val) := by decide +kernel

private theorem checked_shape_1104 : ∀ k : Fin 16, Step (1104+k.val) := by decide +kernel

private theorem checked_shape_1120 : ∀ k : Fin 16, Step (1120+k.val) := by decide +kernel

private theorem checked_shape_1136 : ∀ k : Fin 9, Step (1136+k.val) := by decide +kernel

private theorem checked_steps : ∀ i : Fin nodes.size, Step i.val := by
  intro i
  have hi : i.val < 1145 := i.isLt
  by_cases hsplit_576 : i.val < 576
  · by_cases hsplit_288 : i.val < 288
    · by_cases hsplit_144 : i.val < 144
      · by_cases hsplit_64 : i.val < 64
        · by_cases hsplit_32 : i.val < 32
          · by_cases hsplit_16 : i.val < 16
            · have hlocal : i.val-0 < 16 := by omega
              have hh := checked_shape_0 ⟨i.val-0,hlocal⟩
              have heq : 0+(i.val-0)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-16 < 16 := by omega
              have hh := checked_shape_16 ⟨i.val-16,hlocal⟩
              have heq : 16+(i.val-16)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_48 : i.val < 48
            · have hlocal : i.val-32 < 16 := by omega
              have hh := checked_shape_32 ⟨i.val-32,hlocal⟩
              have heq : 32+(i.val-32)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-48 < 16 := by omega
              have hh := checked_shape_48 ⟨i.val-48,hlocal⟩
              have heq : 48+(i.val-48)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_96 : i.val < 96
          · by_cases hsplit_80 : i.val < 80
            · have hlocal : i.val-64 < 16 := by omega
              have hh := checked_shape_64 ⟨i.val-64,hlocal⟩
              have heq : 64+(i.val-64)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-80 < 16 := by omega
              have hh := checked_shape_80 ⟨i.val-80,hlocal⟩
              have heq : 80+(i.val-80)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_112 : i.val < 112
            · have hlocal : i.val-96 < 16 := by omega
              have hh := checked_shape_96 ⟨i.val-96,hlocal⟩
              have heq : 96+(i.val-96)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_128 : i.val < 128
              · have hlocal : i.val-112 < 16 := by omega
                have hh := checked_shape_112 ⟨i.val-112,hlocal⟩
                have heq : 112+(i.val-112)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-128 < 16 := by omega
                have hh := checked_shape_128 ⟨i.val-128,hlocal⟩
                have heq : 128+(i.val-128)=i.val := by omega
                simpa only [heq] using hh
      · by_cases hsplit_208 : i.val < 208
        · by_cases hsplit_176 : i.val < 176
          · by_cases hsplit_160 : i.val < 160
            · have hlocal : i.val-144 < 16 := by omega
              have hh := checked_shape_144 ⟨i.val-144,hlocal⟩
              have heq : 144+(i.val-144)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-160 < 16 := by omega
              have hh := checked_shape_160 ⟨i.val-160,hlocal⟩
              have heq : 160+(i.val-160)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_192 : i.val < 192
            · have hlocal : i.val-176 < 16 := by omega
              have hh := checked_shape_176 ⟨i.val-176,hlocal⟩
              have heq : 176+(i.val-176)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-192 < 16 := by omega
              have hh := checked_shape_192 ⟨i.val-192,hlocal⟩
              have heq : 192+(i.val-192)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_240 : i.val < 240
          · by_cases hsplit_224 : i.val < 224
            · have hlocal : i.val-208 < 16 := by omega
              have hh := checked_shape_208 ⟨i.val-208,hlocal⟩
              have heq : 208+(i.val-208)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-224 < 16 := by omega
              have hh := checked_shape_224 ⟨i.val-224,hlocal⟩
              have heq : 224+(i.val-224)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_256 : i.val < 256
            · have hlocal : i.val-240 < 16 := by omega
              have hh := checked_shape_240 ⟨i.val-240,hlocal⟩
              have heq : 240+(i.val-240)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_272 : i.val < 272
              · have hlocal : i.val-256 < 16 := by omega
                have hh := checked_shape_256 ⟨i.val-256,hlocal⟩
                have heq : 256+(i.val-256)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-272 < 16 := by omega
                have hh := checked_shape_272 ⟨i.val-272,hlocal⟩
                have heq : 272+(i.val-272)=i.val := by omega
                simpa only [heq] using hh
    · by_cases hsplit_432 : i.val < 432
      · by_cases hsplit_352 : i.val < 352
        · by_cases hsplit_320 : i.val < 320
          · by_cases hsplit_304 : i.val < 304
            · have hlocal : i.val-288 < 16 := by omega
              have hh := checked_shape_288 ⟨i.val-288,hlocal⟩
              have heq : 288+(i.val-288)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-304 < 16 := by omega
              have hh := checked_shape_304 ⟨i.val-304,hlocal⟩
              have heq : 304+(i.val-304)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_336 : i.val < 336
            · have hlocal : i.val-320 < 16 := by omega
              have hh := checked_shape_320 ⟨i.val-320,hlocal⟩
              have heq : 320+(i.val-320)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-336 < 16 := by omega
              have hh := checked_shape_336 ⟨i.val-336,hlocal⟩
              have heq : 336+(i.val-336)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_384 : i.val < 384
          · by_cases hsplit_368 : i.val < 368
            · have hlocal : i.val-352 < 16 := by omega
              have hh := checked_shape_352 ⟨i.val-352,hlocal⟩
              have heq : 352+(i.val-352)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-368 < 16 := by omega
              have hh := checked_shape_368 ⟨i.val-368,hlocal⟩
              have heq : 368+(i.val-368)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_400 : i.val < 400
            · have hlocal : i.val-384 < 16 := by omega
              have hh := checked_shape_384 ⟨i.val-384,hlocal⟩
              have heq : 384+(i.val-384)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_416 : i.val < 416
              · have hlocal : i.val-400 < 16 := by omega
                have hh := checked_shape_400 ⟨i.val-400,hlocal⟩
                have heq : 400+(i.val-400)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-416 < 16 := by omega
                have hh := checked_shape_416 ⟨i.val-416,hlocal⟩
                have heq : 416+(i.val-416)=i.val := by omega
                simpa only [heq] using hh
      · by_cases hsplit_496 : i.val < 496
        · by_cases hsplit_464 : i.val < 464
          · by_cases hsplit_448 : i.val < 448
            · have hlocal : i.val-432 < 16 := by omega
              have hh := checked_shape_432 ⟨i.val-432,hlocal⟩
              have heq : 432+(i.val-432)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-448 < 16 := by omega
              have hh := checked_shape_448 ⟨i.val-448,hlocal⟩
              have heq : 448+(i.val-448)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_480 : i.val < 480
            · have hlocal : i.val-464 < 16 := by omega
              have hh := checked_shape_464 ⟨i.val-464,hlocal⟩
              have heq : 464+(i.val-464)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-480 < 16 := by omega
              have hh := checked_shape_480 ⟨i.val-480,hlocal⟩
              have heq : 480+(i.val-480)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_528 : i.val < 528
          · by_cases hsplit_512 : i.val < 512
            · have hlocal : i.val-496 < 16 := by omega
              have hh := checked_shape_496 ⟨i.val-496,hlocal⟩
              have heq : 496+(i.val-496)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-512 < 16 := by omega
              have hh := checked_shape_512 ⟨i.val-512,hlocal⟩
              have heq : 512+(i.val-512)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_544 : i.val < 544
            · have hlocal : i.val-528 < 16 := by omega
              have hh := checked_shape_528 ⟨i.val-528,hlocal⟩
              have heq : 528+(i.val-528)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_560 : i.val < 560
              · have hlocal : i.val-544 < 16 := by omega
                have hh := checked_shape_544 ⟨i.val-544,hlocal⟩
                have heq : 544+(i.val-544)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-560 < 16 := by omega
                have hh := checked_shape_560 ⟨i.val-560,hlocal⟩
                have heq : 560+(i.val-560)=i.val := by omega
                simpa only [heq] using hh
  · by_cases hsplit_864 : i.val < 864
    · by_cases hsplit_720 : i.val < 720
      · by_cases hsplit_640 : i.val < 640
        · by_cases hsplit_608 : i.val < 608
          · by_cases hsplit_592 : i.val < 592
            · have hlocal : i.val-576 < 16 := by omega
              have hh := checked_shape_576 ⟨i.val-576,hlocal⟩
              have heq : 576+(i.val-576)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-592 < 16 := by omega
              have hh := checked_shape_592 ⟨i.val-592,hlocal⟩
              have heq : 592+(i.val-592)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_624 : i.val < 624
            · have hlocal : i.val-608 < 16 := by omega
              have hh := checked_shape_608 ⟨i.val-608,hlocal⟩
              have heq : 608+(i.val-608)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-624 < 16 := by omega
              have hh := checked_shape_624 ⟨i.val-624,hlocal⟩
              have heq : 624+(i.val-624)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_672 : i.val < 672
          · by_cases hsplit_656 : i.val < 656
            · have hlocal : i.val-640 < 16 := by omega
              have hh := checked_shape_640 ⟨i.val-640,hlocal⟩
              have heq : 640+(i.val-640)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-656 < 16 := by omega
              have hh := checked_shape_656 ⟨i.val-656,hlocal⟩
              have heq : 656+(i.val-656)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_688 : i.val < 688
            · have hlocal : i.val-672 < 16 := by omega
              have hh := checked_shape_672 ⟨i.val-672,hlocal⟩
              have heq : 672+(i.val-672)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_704 : i.val < 704
              · have hlocal : i.val-688 < 16 := by omega
                have hh := checked_shape_688 ⟨i.val-688,hlocal⟩
                have heq : 688+(i.val-688)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-704 < 16 := by omega
                have hh := checked_shape_704 ⟨i.val-704,hlocal⟩
                have heq : 704+(i.val-704)=i.val := by omega
                simpa only [heq] using hh
      · by_cases hsplit_784 : i.val < 784
        · by_cases hsplit_752 : i.val < 752
          · by_cases hsplit_736 : i.val < 736
            · have hlocal : i.val-720 < 16 := by omega
              have hh := checked_shape_720 ⟨i.val-720,hlocal⟩
              have heq : 720+(i.val-720)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-736 < 16 := by omega
              have hh := checked_shape_736 ⟨i.val-736,hlocal⟩
              have heq : 736+(i.val-736)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_768 : i.val < 768
            · have hlocal : i.val-752 < 16 := by omega
              have hh := checked_shape_752 ⟨i.val-752,hlocal⟩
              have heq : 752+(i.val-752)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-768 < 16 := by omega
              have hh := checked_shape_768 ⟨i.val-768,hlocal⟩
              have heq : 768+(i.val-768)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_816 : i.val < 816
          · by_cases hsplit_800 : i.val < 800
            · have hlocal : i.val-784 < 16 := by omega
              have hh := checked_shape_784 ⟨i.val-784,hlocal⟩
              have heq : 784+(i.val-784)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-800 < 16 := by omega
              have hh := checked_shape_800 ⟨i.val-800,hlocal⟩
              have heq : 800+(i.val-800)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_832 : i.val < 832
            · have hlocal : i.val-816 < 16 := by omega
              have hh := checked_shape_816 ⟨i.val-816,hlocal⟩
              have heq : 816+(i.val-816)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_848 : i.val < 848
              · have hlocal : i.val-832 < 16 := by omega
                have hh := checked_shape_832 ⟨i.val-832,hlocal⟩
                have heq : 832+(i.val-832)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-848 < 16 := by omega
                have hh := checked_shape_848 ⟨i.val-848,hlocal⟩
                have heq : 848+(i.val-848)=i.val := by omega
                simpa only [heq] using hh
    · by_cases hsplit_1008 : i.val < 1008
      · by_cases hsplit_928 : i.val < 928
        · by_cases hsplit_896 : i.val < 896
          · by_cases hsplit_880 : i.val < 880
            · have hlocal : i.val-864 < 16 := by omega
              have hh := checked_shape_864 ⟨i.val-864,hlocal⟩
              have heq : 864+(i.val-864)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-880 < 16 := by omega
              have hh := checked_shape_880 ⟨i.val-880,hlocal⟩
              have heq : 880+(i.val-880)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_912 : i.val < 912
            · have hlocal : i.val-896 < 16 := by omega
              have hh := checked_shape_896 ⟨i.val-896,hlocal⟩
              have heq : 896+(i.val-896)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-912 < 16 := by omega
              have hh := checked_shape_912 ⟨i.val-912,hlocal⟩
              have heq : 912+(i.val-912)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_960 : i.val < 960
          · by_cases hsplit_944 : i.val < 944
            · have hlocal : i.val-928 < 16 := by omega
              have hh := checked_shape_928 ⟨i.val-928,hlocal⟩
              have heq : 928+(i.val-928)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-944 < 16 := by omega
              have hh := checked_shape_944 ⟨i.val-944,hlocal⟩
              have heq : 944+(i.val-944)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_976 : i.val < 976
            · have hlocal : i.val-960 < 16 := by omega
              have hh := checked_shape_960 ⟨i.val-960,hlocal⟩
              have heq : 960+(i.val-960)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_992 : i.val < 992
              · have hlocal : i.val-976 < 16 := by omega
                have hh := checked_shape_976 ⟨i.val-976,hlocal⟩
                have heq : 976+(i.val-976)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-992 < 16 := by omega
                have hh := checked_shape_992 ⟨i.val-992,hlocal⟩
                have heq : 992+(i.val-992)=i.val := by omega
                simpa only [heq] using hh
      · by_cases hsplit_1072 : i.val < 1072
        · by_cases hsplit_1040 : i.val < 1040
          · by_cases hsplit_1024 : i.val < 1024
            · have hlocal : i.val-1008 < 16 := by omega
              have hh := checked_shape_1008 ⟨i.val-1008,hlocal⟩
              have heq : 1008+(i.val-1008)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-1024 < 16 := by omega
              have hh := checked_shape_1024 ⟨i.val-1024,hlocal⟩
              have heq : 1024+(i.val-1024)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_1056 : i.val < 1056
            · have hlocal : i.val-1040 < 16 := by omega
              have hh := checked_shape_1040 ⟨i.val-1040,hlocal⟩
              have heq : 1040+(i.val-1040)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-1056 < 16 := by omega
              have hh := checked_shape_1056 ⟨i.val-1056,hlocal⟩
              have heq : 1056+(i.val-1056)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_1104 : i.val < 1104
          · by_cases hsplit_1088 : i.val < 1088
            · have hlocal : i.val-1072 < 16 := by omega
              have hh := checked_shape_1072 ⟨i.val-1072,hlocal⟩
              have heq : 1072+(i.val-1072)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-1088 < 16 := by omega
              have hh := checked_shape_1088 ⟨i.val-1088,hlocal⟩
              have heq : 1088+(i.val-1088)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_1120 : i.val < 1120
            · have hlocal : i.val-1104 < 16 := by omega
              have hh := checked_shape_1104 ⟨i.val-1104,hlocal⟩
              have heq : 1104+(i.val-1104)=i.val := by omega
              simpa only [heq] using hh
            · by_cases hsplit_1136 : i.val < 1136
              · have hlocal : i.val-1120 < 16 := by omega
                have hh := checked_shape_1120 ⟨i.val-1120,hlocal⟩
                have heq : 1120+(i.val-1120)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1136 < 9 := by omega
                have hh := checked_shape_1136 ⟨i.val-1136,hlocal⟩
                have heq : 1136+(i.val-1136)=i.val := by omega
                simpa only [heq] using hh

theorem checked_walk : walk nodes nodes.size (nodes.size-1) = List.range nodes.size := by
  have traversal (fuel : Nat) : ∀ i, i < nodes.size → i < fuel →
      walk nodes fuel i = List.range' (start i) (i+1-start i) := by
    induction fuel with
    | zero => intro i hi hf; omega
    | succ fuel ih =>
      intro i hi hf
      have h := checked_steps ⟨i,hi⟩
      change Step i at h
      rcases h with ⟨hstart,h⟩
      cases he : (node nodes i).rule with
      | split axis cut l r =>
        simp only [he] at h
        obtain ⟨hl,hr,hsl,hsr,hiEq⟩ := h
        have hsl_le : start i ≤ l := by
          have hh : start l ≤ l := (checked_steps ⟨l,lt_trans hl hi⟩).1
          simpa only [hsl] using hh
        have hwl := ih l (lt_trans hl hi) (by omega)
        have hwr := ih r (lt_trans hr hi) (by omega)
        simp only [walk,he]
        rw [hwl,hwr,hsl,hsr]
        let m := l+1-start i
        let n := r+1-(l+1)
        change (List.range' (start i) m ++ List.range' (l+1) n) ++ [i] =
          List.range' (start i) (i+1-start i)
        have hm : start i+m = l+1 := by dsimp [m]; omega
        have hn : m+n+1 = i+1-start i := by dsimp [m,n]; omega
        have hlast : start i+(m+n) = i := by dsimp [m,n]; omega
        have happ : List.range' (start i) m ++ List.range' (l+1) n =
            List.range' (start i) (m+n) := by
          simpa only [hm] using (List.range'_append_1 (s := start i) (m := m) (n := n))
        rw [happ]
        have hc := (List.range'_1_concat (s := start i) (n := m+n)).symm
        rw [hn,hlast] at hc
        exact hc
      | localRegion | infeasible _ | boxTail | capInfeasible _ _ | bound _ _ _ _ =>
        have hs : start i = i := by simpa only [he] using h
        have hlen : i+1-start i = 1 := by omega
        calc
          walk nodes (fuel+1) i = [i] := by simp only [walk,he]
          _ = List.range' (start i) (i+1-start i) := by
            have ht : List.range' (start i) (i+1-start i) = List.range' i 1 :=
              congrArg₂ (fun (s n : Nat) => List.range' s n) hs hlen
            exact (show [i] = List.range' i 1 from rfl).trans ht.symm
  change walk nodes 1145 1144 = List.range 1145
  rw [List.range_eq_range']
  have hh := traversal 1145 1144 (by decide +kernel) (by decide +kernel)
  change walk nodes 1145 1144 = List.range' 0 1145 at hh
  exact hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N90A
