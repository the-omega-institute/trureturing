/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N85AShape
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N85AShape
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N85AShape.checked_walk
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N85A
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N85A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private def starts : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 11, 2, 13, 14, 13, 2, 17, 18, 17, 20, 17, 22, 23, 22, 25, 22, 17, 28, 29, 28, 31, 28, 33, 28, 17, 36, 17, 38, 39, 38, 17, 42, 43, 42, 45, 42, 17, 48, 49, 48, 51, 48, 53, 54, 53, 48, 17, 58, 17, 60, 61, 60, 17, 2, 65, 2, 67, 68, 67, 70, 67, 72, 73, 72, 67, 76, 67, 2, 1, 80, 1, 82, 83, 84, 83, 86, 83, 82, 89, 82, 1, 92, 93, 92, 95, 92, 97, 98, 97, 92, 101, 92, 103, 92, 105, 106, 105, 92, 109, 110, 111, 110, 109, 92, 115, 92, 117, 118, 117, 92, 121, 122, 121, 92, 125, 92, 127, 92, 1, 0, 131, 132, 133, 134, 135, 134, 133, 132, 131, 140, 131, 142, 143, 144, 145, 144, 147, 148, 149, 148, 147, 144, 143, 142, 155, 156, 157, 158, 157, 160, 161, 160, 163, 160, 157, 156, 155, 142, 131, 170, 171, 172, 173, 172, 171, 170, 177, 170, 179, 170, 181, 182, 181, 170, 185, 186, 185, 188, 185, 190, 191, 190, 185, 170, 195, 196, 197, 198, 197, 196, 201, 196, 195, 204, 195, 206, 207, 206, 195, 210, 211, 212, 211, 210, 195, 170, 217, 170, 219, 220, 221, 222, 221, 220, 225, 220, 227, 220, 219, 230, 231, 232, 231, 234, 231, 230, 219, 170, 131, 240, 241, 242, 243, 244, 245, 244, 243, 242, 241, 240, 251, 252, 253, 252, 255, 256, 257, 256, 255, 260, 255, 252, 251, 264, 265, 266, 267, 268, 267, 266, 265, 264, 273, 274, 275, 274, 277, 274, 279, 274, 273, 282, 283, 282, 285, 282, 287, 282, 273, 290, 273, 292, 273, 264, 251, 296, 297, 296, 299, 300, 301, 300, 303, 300, 299, 306, 307, 306, 299, 296, 251, 312, 313, 314, 315, 314, 313, 318, 313, 312, 321, 312, 323, 324, 325, 324, 327, 324, 329, 324, 323, 332, 323, 312, 251, 240, 337, 338, 339, 338, 341, 342, 341, 344, 345, 344, 341, 338, 337, 350, 351, 352, 351, 354, 351, 356, 351, 350, 359, 350, 361, 362, 361, 364, 365, 364, 367, 364, 369, 364, 361, 350, 373, 374, 373, 376, 373, 378, 373, 380, 373, 382, 373, 350, 337, 386, 387, 388, 387, 386, 391, 392, 393, 392, 395, 392, 397, 392, 391, 386, 401, 402, 401, 404, 405, 404, 401, 386, 337, 410, 411, 410, 413, 410, 415, 410, 417, 418, 417, 420, 421, 420, 417, 424, 417, 426, 417, 428, 417, 410, 337, 432, 433, 432, 435, 432, 437, 432, 439, 432, 441, 432, 443, 432, 445, 446, 445, 448, 445, 450, 445, 432, 453, 432, 337, 240, 457, 458, 459, 460, 461, 462, 461, 460, 459, 466, 467, 466, 469, 466, 471, 466, 459, 458, 475, 476, 475, 478, 479, 480, 479, 482, 479, 478, 485, 486, 485, 478, 475, 458, 457, 492, 493, 494, 493, 496, 497, 496, 493, 492, 457, 502, 503, 504, 503, 506, 503, 508, 503, 510, 503, 512, 503, 514, 503, 516, 517, 516, 519, 516, 521, 516, 503, 502, 525, 526, 525, 502, 457, 240, 531, 532, 533, 532, 531, 536, 531, 538, 531, 540, 531, 542, 543, 542, 545, 546, 545, 548, 545, 542, 551, 542, 553, 542, 555, 542, 531, 240, 559, 560, 561, 560, 559, 564, 559, 566, 567, 568, 567, 566, 571, 566, 573, 566, 575, 576, 575, 566, 559, 580, 559, 582, 583, 582, 585, 582, 559, 588, 589, 588, 559, 592, 559, 594, 595, 594, 559, 598, 559, 600, 559, 602, 559, 604, 605, 604, 559, 608, 559, 240, 131, 612, 613, 614, 615, 616, 617, 616, 615, 620, 621, 622, 621, 624, 621, 620, 615, 614, 629, 614, 613, 632, 613, 612, 635, 612, 637, 638, 639, 638, 641, 638, 643, 638, 645, 646, 645, 648, 645, 650, 645, 638, 653, 638, 655, 638, 657, 638, 659, 638, 637, 662, 637, 612, 131, 666, 667, 668, 669, 670, 669, 668, 673, 668, 675, 668, 667, 666, 679, 680, 679, 666, 683, 684, 683, 666, 687, 666, 689, 690, 691, 690, 693, 690, 689, 696, 697, 698, 697, 696, 701, 696, 703, 696, 689, 706, 689, 708, 689, 710, 689, 666, 131, 714, 715, 716, 715, 714, 719, 714, 721, 714, 723, 714, 725, 714, 727, 728, 727, 714, 731, 714, 733, 734, 733, 714, 737, 714, 131, 0]
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

private theorem checked_shape_736 : ∀ k : Fin 5, Step (736+k.val) := by decide +kernel

private theorem checked_steps : ∀ i : Fin nodes.size, Step i.val := by
  intro i
  have hi : i.val < 741 := i.isLt
  by_cases hsplit_368 : i.val < 368
  · by_cases hsplit_176 : i.val < 176
    · by_cases hsplit_80 : i.val < 80
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
          · by_cases hsplit_64 : i.val < 64
            · have hlocal : i.val-48 < 16 := by omega
              have hh := checked_shape_48 ⟨i.val-48,hlocal⟩
              have heq : 48+(i.val-48)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-64 < 16 := by omega
              have hh := checked_shape_64 ⟨i.val-64,hlocal⟩
              have heq : 64+(i.val-64)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_128 : i.val < 128
        · by_cases hsplit_96 : i.val < 96
          · have hlocal : i.val-80 < 16 := by omega
            have hh := checked_shape_80 ⟨i.val-80,hlocal⟩
            have heq : 80+(i.val-80)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_112 : i.val < 112
            · have hlocal : i.val-96 < 16 := by omega
              have hh := checked_shape_96 ⟨i.val-96,hlocal⟩
              have heq : 96+(i.val-96)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-112 < 16 := by omega
              have hh := checked_shape_112 ⟨i.val-112,hlocal⟩
              have heq : 112+(i.val-112)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_144 : i.val < 144
          · have hlocal : i.val-128 < 16 := by omega
            have hh := checked_shape_128 ⟨i.val-128,hlocal⟩
            have heq : 128+(i.val-128)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_160 : i.val < 160
            · have hlocal : i.val-144 < 16 := by omega
              have hh := checked_shape_144 ⟨i.val-144,hlocal⟩
              have heq : 144+(i.val-144)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-160 < 16 := by omega
              have hh := checked_shape_160 ⟨i.val-160,hlocal⟩
              have heq : 160+(i.val-160)=i.val := by omega
              simpa only [heq] using hh
    · by_cases hsplit_272 : i.val < 272
      · by_cases hsplit_224 : i.val < 224
        · by_cases hsplit_192 : i.val < 192
          · have hlocal : i.val-176 < 16 := by omega
            have hh := checked_shape_176 ⟨i.val-176,hlocal⟩
            have heq : 176+(i.val-176)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_208 : i.val < 208
            · have hlocal : i.val-192 < 16 := by omega
              have hh := checked_shape_192 ⟨i.val-192,hlocal⟩
              have heq : 192+(i.val-192)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-208 < 16 := by omega
              have hh := checked_shape_208 ⟨i.val-208,hlocal⟩
              have heq : 208+(i.val-208)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_240 : i.val < 240
          · have hlocal : i.val-224 < 16 := by omega
            have hh := checked_shape_224 ⟨i.val-224,hlocal⟩
            have heq : 224+(i.val-224)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_256 : i.val < 256
            · have hlocal : i.val-240 < 16 := by omega
              have hh := checked_shape_240 ⟨i.val-240,hlocal⟩
              have heq : 240+(i.val-240)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-256 < 16 := by omega
              have hh := checked_shape_256 ⟨i.val-256,hlocal⟩
              have heq : 256+(i.val-256)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_320 : i.val < 320
        · by_cases hsplit_288 : i.val < 288
          · have hlocal : i.val-272 < 16 := by omega
            have hh := checked_shape_272 ⟨i.val-272,hlocal⟩
            have heq : 272+(i.val-272)=i.val := by omega
            simpa only [heq] using hh
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
          · by_cases hsplit_352 : i.val < 352
            · have hlocal : i.val-336 < 16 := by omega
              have hh := checked_shape_336 ⟨i.val-336,hlocal⟩
              have heq : 336+(i.val-336)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-352 < 16 := by omega
              have hh := checked_shape_352 ⟨i.val-352,hlocal⟩
              have heq : 352+(i.val-352)=i.val := by omega
              simpa only [heq] using hh
  · by_cases hsplit_560 : i.val < 560
    · by_cases hsplit_464 : i.val < 464
      · by_cases hsplit_416 : i.val < 416
        · by_cases hsplit_384 : i.val < 384
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
      · by_cases hsplit_512 : i.val < 512
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
    · by_cases hsplit_656 : i.val < 656
      · by_cases hsplit_608 : i.val < 608
        · by_cases hsplit_576 : i.val < 576
          · have hlocal : i.val-560 < 16 := by omega
            have hh := checked_shape_560 ⟨i.val-560,hlocal⟩
            have heq : 560+(i.val-560)=i.val := by omega
            simpa only [heq] using hh
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
          · by_cases hsplit_640 : i.val < 640
            · have hlocal : i.val-624 < 16 := by omega
              have hh := checked_shape_624 ⟨i.val-624,hlocal⟩
              have heq : 624+(i.val-624)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-640 < 16 := by omega
              have hh := checked_shape_640 ⟨i.val-640,hlocal⟩
              have heq : 640+(i.val-640)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_704 : i.val < 704
        · by_cases hsplit_672 : i.val < 672
          · have hlocal : i.val-656 < 16 := by omega
            have hh := checked_shape_656 ⟨i.val-656,hlocal⟩
            have heq : 656+(i.val-656)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_688 : i.val < 688
            · have hlocal : i.val-672 < 16 := by omega
              have hh := checked_shape_672 ⟨i.val-672,hlocal⟩
              have heq : 672+(i.val-672)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-688 < 16 := by omega
              have hh := checked_shape_688 ⟨i.val-688,hlocal⟩
              have heq : 688+(i.val-688)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_720 : i.val < 720
          · have hlocal : i.val-704 < 16 := by omega
            have hh := checked_shape_704 ⟨i.val-704,hlocal⟩
            have heq : 704+(i.val-704)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_736 : i.val < 736
            · have hlocal : i.val-720 < 16 := by omega
              have hh := checked_shape_720 ⟨i.val-720,hlocal⟩
              have heq : 720+(i.val-720)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-736 < 5 := by omega
              have hh := checked_shape_736 ⟨i.val-736,hlocal⟩
              have heq : 736+(i.val-736)=i.val := by omega
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
  change walk nodes 741 740 = List.range 741
  rw [List.range_eq_range']
  have hh := traversal 741 740 (by decide +kernel) (by decide +kernel)
  change walk nodes 741 740 = List.range' 0 741 at hh
  exact hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N85A
