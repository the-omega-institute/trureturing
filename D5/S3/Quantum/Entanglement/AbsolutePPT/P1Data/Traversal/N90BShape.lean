/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N90BShape
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N90BShape
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N90BShape.checked_walk
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N90B
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N90B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private def starts : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 11, 2, 13, 14, 13, 2, 17, 18, 17, 20, 17, 22, 23, 22, 25, 22, 17, 28, 29, 28, 31, 28, 33, 28, 17, 36, 17, 38, 39, 38, 17, 42, 43, 42, 45, 42, 17, 48, 49, 48, 51, 48, 53, 54, 53, 48, 17, 58, 17, 60, 61, 60, 17, 2, 65, 2, 67, 68, 67, 70, 67, 72, 73, 72, 67, 76, 67, 2, 1, 80, 1, 82, 83, 84, 83, 86, 83, 82, 89, 82, 1, 92, 93, 92, 95, 92, 97, 98, 97, 92, 101, 92, 103, 92, 105, 106, 105, 92, 109, 110, 111, 110, 109, 92, 115, 92, 117, 118, 117, 92, 121, 122, 121, 92, 125, 92, 127, 92, 1, 0, 131, 132, 133, 134, 135, 134, 133, 132, 131, 140, 131, 142, 143, 144, 145, 144, 147, 148, 149, 148, 147, 144, 143, 142, 155, 156, 157, 158, 159, 158, 161, 158, 157, 156, 155, 142, 131, 168, 169, 170, 171, 170, 169, 168, 175, 168, 177, 168, 179, 180, 179, 168, 183, 184, 185, 184, 183, 168, 189, 190, 191, 190, 189, 194, 189, 196, 197, 198, 197, 196, 201, 196, 203, 204, 203, 196, 207, 208, 209, 208, 207, 196, 189, 214, 189, 216, 217, 218, 217, 220, 217, 222, 217, 216, 225, 216, 189, 228, 229, 230, 229, 228, 189, 168, 235, 168, 237, 238, 239, 240, 239, 238, 243, 238, 245, 238, 237, 248, 249, 250, 249, 252, 249, 248, 237, 168, 131, 258, 259, 260, 259, 258, 263, 264, 265, 266, 267, 268, 267, 266, 265, 264, 273, 264, 275, 276, 277, 278, 277, 280, 277, 276, 275, 284, 275, 264, 263, 288, 289, 288, 291, 292, 293, 292, 291, 296, 291, 288, 299, 300, 301, 302, 301, 304, 301, 300, 307, 308, 307, 310, 307, 300, 313, 300, 315, 300, 299, 318, 319, 318, 321, 318, 323, 318, 325, 318, 299, 328, 299, 330, 299, 288, 263, 334, 263, 336, 337, 338, 337, 340, 341, 340, 337, 344, 337, 336, 347, 336, 349, 350, 349, 336, 263, 258, 355, 356, 357, 358, 359, 358, 361, 358, 357, 356, 365, 356, 367, 368, 367, 370, 371, 370, 367, 356, 355, 376, 377, 378, 377, 380, 381, 380, 383, 384, 383, 380, 377, 376, 389, 390, 391, 392, 393, 392, 395, 392, 391, 398, 391, 400, 391, 402, 391, 390, 405, 390, 407, 408, 407, 410, 407, 412, 407, 390, 415, 416, 415, 418, 415, 420, 415, 422, 415, 390, 389, 426, 389, 428, 429, 428, 431, 428, 433, 428, 435, 436, 435, 438, 435, 440, 435, 428, 389, 444, 445, 444, 447, 444, 449, 444, 451, 444, 453, 444, 455, 444, 389, 376, 459, 376, 461, 462, 463, 462, 461, 466, 461, 468, 461, 470, 461, 472, 473, 472, 475, 472, 477, 472, 479, 472, 481, 472, 461, 376, 485, 486, 485, 488, 485, 490, 485, 492, 485, 494, 485, 496, 485, 498, 485, 376, 355, 502, 355, 504, 505, 506, 505, 504, 509, 504, 511, 504, 513, 504, 515, 516, 515, 518, 515, 520, 515, 522, 515, 524, 515, 504, 355, 528, 529, 530, 529, 532, 529, 534, 529, 528, 537, 528, 539, 528, 541, 528, 543, 528, 545, 528, 547, 528, 549, 528, 355, 258, 553, 258, 555, 556, 555, 558, 559, 558, 555, 562, 555, 564, 555, 566, 555, 568, 569, 568, 571, 568, 573, 568, 575, 568, 577, 568, 555, 258, 581, 582, 583, 584, 583, 586, 587, 586, 583, 582, 581, 592, 581, 594, 595, 596, 595, 594, 599, 594, 581, 602, 603, 604, 605, 604, 603, 608, 603, 602, 611, 602, 613, 614, 613, 602, 581, 618, 619, 620, 621, 622, 621, 620, 619, 626, 627, 628, 627, 626, 631, 632, 631, 634, 631, 636, 631, 638, 631, 626, 619, 642, 619, 644, 645, 644, 647, 644, 649, 644, 619, 618, 653, 654, 655, 654, 653, 658, 653, 660, 653, 662, 653, 618, 665, 618, 667, 668, 667, 670, 667, 672, 667, 674, 667, 618, 677, 678, 677, 680, 677, 682, 677, 684, 677, 686, 677, 688, 677, 690, 677, 618, 581, 694, 581, 696, 697, 696, 699, 696, 701, 696, 703, 696, 705, 696, 581, 708, 709, 708, 711, 708, 713, 708, 715, 708, 717, 708, 581, 720, 581, 722, 581, 724, 581, 726, 581, 728, 581, 730, 581, 732, 581, 258, 131, 736, 737, 738, 739, 740, 739, 738, 743, 738, 737, 746, 737, 736, 749, 736, 751, 736, 131, 754, 755, 756, 755, 754, 759, 760, 761, 762, 761, 760, 765, 760, 767, 760, 759, 754, 771, 772, 771, 754, 775, 776, 775, 754, 779, 754, 781, 782, 783, 782, 785, 782, 781, 788, 789, 790, 789, 788, 793, 788, 795, 788, 781, 798, 781, 800, 781, 802, 781, 754, 131, 806, 807, 806, 809, 806, 811, 806, 813, 806, 815, 806, 131, 0]
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

private theorem checked_shape_816 : ∀ k : Fin 3, Step (816+k.val) := by decide +kernel

private theorem checked_steps : ∀ i : Fin nodes.size, Step i.val := by
  intro i
  have hi : i.val < 819 := i.isLt
  by_cases hsplit_416 : i.val < 416
  · by_cases hsplit_208 : i.val < 208
    · by_cases hsplit_96 : i.val < 96
      · by_cases hsplit_48 : i.val < 48
        · by_cases hsplit_16 : i.val < 16
          · have hlocal : i.val-0 < 16 := by omega
            have hh := checked_shape_0 ⟨i.val-0,hlocal⟩
            have heq : 0+(i.val-0)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_32 : i.val < 32
            · have hlocal : i.val-16 < 16 := by omega
              have hh := checked_shape_16 ⟨i.val-16,hlocal⟩
              have heq : 16+(i.val-16)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-32 < 16 := by omega
              have hh := checked_shape_32 ⟨i.val-32,hlocal⟩
              have heq : 32+(i.val-32)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_64 : i.val < 64
          · have hlocal : i.val-48 < 16 := by omega
            have hh := checked_shape_48 ⟨i.val-48,hlocal⟩
            have heq : 48+(i.val-48)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_80 : i.val < 80
            · have hlocal : i.val-64 < 16 := by omega
              have hh := checked_shape_64 ⟨i.val-64,hlocal⟩
              have heq : 64+(i.val-64)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-80 < 16 := by omega
              have hh := checked_shape_80 ⟨i.val-80,hlocal⟩
              have heq : 80+(i.val-80)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_144 : i.val < 144
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
    · by_cases hsplit_304 : i.val < 304
      · by_cases hsplit_256 : i.val < 256
        · by_cases hsplit_224 : i.val < 224
          · have hlocal : i.val-208 < 16 := by omega
            have hh := checked_shape_208 ⟨i.val-208,hlocal⟩
            have heq : 208+(i.val-208)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_240 : i.val < 240
            · have hlocal : i.val-224 < 16 := by omega
              have hh := checked_shape_224 ⟨i.val-224,hlocal⟩
              have heq : 224+(i.val-224)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-240 < 16 := by omega
              have hh := checked_shape_240 ⟨i.val-240,hlocal⟩
              have heq : 240+(i.val-240)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_272 : i.val < 272
          · have hlocal : i.val-256 < 16 := by omega
            have hh := checked_shape_256 ⟨i.val-256,hlocal⟩
            have heq : 256+(i.val-256)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_288 : i.val < 288
            · have hlocal : i.val-272 < 16 := by omega
              have hh := checked_shape_272 ⟨i.val-272,hlocal⟩
              have heq : 272+(i.val-272)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-288 < 16 := by omega
              have hh := checked_shape_288 ⟨i.val-288,hlocal⟩
              have heq : 288+(i.val-288)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_352 : i.val < 352
        · by_cases hsplit_320 : i.val < 320
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
            · have hlocal : i.val-400 < 16 := by omega
              have hh := checked_shape_400 ⟨i.val-400,hlocal⟩
              have heq : 400+(i.val-400)=i.val := by omega
              simpa only [heq] using hh
  · by_cases hsplit_624 : i.val < 624
    · by_cases hsplit_512 : i.val < 512
      · by_cases hsplit_464 : i.val < 464
        · by_cases hsplit_432 : i.val < 432
          · have hlocal : i.val-416 < 16 := by omega
            have hh := checked_shape_416 ⟨i.val-416,hlocal⟩
            have heq : 416+(i.val-416)=i.val := by omega
            simpa only [heq] using hh
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
          · by_cases hsplit_496 : i.val < 496
            · have hlocal : i.val-480 < 16 := by omega
              have hh := checked_shape_480 ⟨i.val-480,hlocal⟩
              have heq : 480+(i.val-480)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-496 < 16 := by omega
              have hh := checked_shape_496 ⟨i.val-496,hlocal⟩
              have heq : 496+(i.val-496)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_560 : i.val < 560
        · by_cases hsplit_528 : i.val < 528
          · have hlocal : i.val-512 < 16 := by omega
            have hh := checked_shape_512 ⟨i.val-512,hlocal⟩
            have heq : 512+(i.val-512)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_544 : i.val < 544
            · have hlocal : i.val-528 < 16 := by omega
              have hh := checked_shape_528 ⟨i.val-528,hlocal⟩
              have heq : 528+(i.val-528)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-544 < 16 := by omega
              have hh := checked_shape_544 ⟨i.val-544,hlocal⟩
              have heq : 544+(i.val-544)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_592 : i.val < 592
          · by_cases hsplit_576 : i.val < 576
            · have hlocal : i.val-560 < 16 := by omega
              have hh := checked_shape_560 ⟨i.val-560,hlocal⟩
              have heq : 560+(i.val-560)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-576 < 16 := by omega
              have hh := checked_shape_576 ⟨i.val-576,hlocal⟩
              have heq : 576+(i.val-576)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_608 : i.val < 608
            · have hlocal : i.val-592 < 16 := by omega
              have hh := checked_shape_592 ⟨i.val-592,hlocal⟩
              have heq : 592+(i.val-592)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-608 < 16 := by omega
              have hh := checked_shape_608 ⟨i.val-608,hlocal⟩
              have heq : 608+(i.val-608)=i.val := by omega
              simpa only [heq] using hh
    · by_cases hsplit_720 : i.val < 720
      · by_cases hsplit_672 : i.val < 672
        · by_cases hsplit_640 : i.val < 640
          · have hlocal : i.val-624 < 16 := by omega
            have hh := checked_shape_624 ⟨i.val-624,hlocal⟩
            have heq : 624+(i.val-624)=i.val := by omega
            simpa only [heq] using hh
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
      · by_cases hsplit_768 : i.val < 768
        · by_cases hsplit_736 : i.val < 736
          · have hlocal : i.val-720 < 16 := by omega
            have hh := checked_shape_720 ⟨i.val-720,hlocal⟩
            have heq : 720+(i.val-720)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_752 : i.val < 752
            · have hlocal : i.val-736 < 16 := by omega
              have hh := checked_shape_736 ⟨i.val-736,hlocal⟩
              have heq : 736+(i.val-736)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-752 < 16 := by omega
              have hh := checked_shape_752 ⟨i.val-752,hlocal⟩
              have heq : 752+(i.val-752)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_800 : i.val < 800
          · by_cases hsplit_784 : i.val < 784
            · have hlocal : i.val-768 < 16 := by omega
              have hh := checked_shape_768 ⟨i.val-768,hlocal⟩
              have heq : 768+(i.val-768)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-784 < 16 := by omega
              have hh := checked_shape_784 ⟨i.val-784,hlocal⟩
              have heq : 784+(i.val-784)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_816 : i.val < 816
            · have hlocal : i.val-800 < 16 := by omega
              have hh := checked_shape_800 ⟨i.val-800,hlocal⟩
              have heq : 800+(i.val-800)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-816 < 3 := by omega
              have hh := checked_shape_816 ⟨i.val-816,hlocal⟩
              have heq : 816+(i.val-816)=i.val := by omega
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
  change walk nodes 819 818 = List.range 819
  rw [List.range_eq_range']
  have hh := traversal 819 818 (by decide +kernel) (by decide +kernel)
  change walk nodes 819 818 = List.range' 0 819 at hh
  exact hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N90B
