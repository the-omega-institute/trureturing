/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N85BShape
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N85BShape
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N85BShape.checked_walk
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N85B
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N85B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private def starts : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 11, 2, 13, 14, 13, 2, 17, 18, 17, 20, 17, 22, 23, 22, 25, 22, 17, 28, 29, 28, 31, 28, 33, 28, 17, 36, 17, 38, 39, 38, 17, 42, 43, 42, 45, 42, 17, 48, 49, 48, 51, 48, 53, 54, 53, 48, 17, 58, 17, 60, 61, 60, 17, 2, 65, 2, 67, 68, 67, 70, 67, 72, 73, 72, 67, 76, 67, 2, 1, 80, 1, 82, 83, 84, 83, 86, 83, 82, 89, 82, 1, 92, 93, 92, 95, 92, 97, 98, 97, 92, 101, 92, 103, 92, 105, 106, 105, 92, 109, 110, 111, 110, 109, 92, 115, 92, 117, 118, 117, 92, 121, 122, 121, 92, 125, 92, 127, 92, 1, 0, 131, 132, 133, 134, 135, 134, 133, 132, 131, 140, 131, 142, 143, 144, 145, 144, 147, 148, 149, 148, 147, 144, 143, 142, 155, 156, 157, 158, 159, 158, 161, 158, 157, 156, 155, 142, 131, 168, 169, 170, 171, 170, 169, 168, 175, 168, 177, 168, 179, 180, 179, 168, 183, 184, 183, 186, 183, 188, 189, 188, 183, 168, 193, 194, 195, 196, 195, 194, 199, 194, 193, 202, 193, 204, 205, 204, 193, 208, 209, 210, 209, 208, 193, 168, 215, 168, 217, 218, 219, 220, 219, 218, 223, 218, 225, 218, 217, 228, 229, 230, 229, 232, 229, 228, 217, 168, 131, 238, 239, 240, 241, 240, 243, 244, 245, 244, 243, 248, 243, 240, 239, 252, 253, 254, 253, 252, 257, 258, 259, 258, 261, 258, 263, 258, 257, 266, 267, 266, 269, 266, 271, 266, 257, 274, 257, 276, 257, 252, 239, 280, 239, 282, 283, 284, 283, 286, 283, 282, 289, 282, 291, 292, 291, 282, 239, 238, 297, 298, 299, 298, 301, 302, 301, 304, 305, 304, 301, 298, 297, 310, 311, 312, 311, 314, 311, 316, 311, 310, 319, 310, 321, 322, 321, 324, 325, 324, 327, 324, 321, 310, 331, 332, 331, 334, 331, 336, 331, 338, 331, 340, 331, 310, 297, 344, 297, 346, 347, 346, 349, 346, 351, 346, 353, 354, 353, 356, 353, 358, 353, 360, 353, 346, 297, 364, 365, 364, 367, 364, 369, 364, 371, 364, 373, 364, 375, 364, 377, 364, 379, 364, 297, 238, 383, 238, 385, 386, 387, 386, 385, 390, 385, 392, 385, 394, 385, 396, 397, 396, 399, 396, 401, 396, 403, 396, 405, 396, 385, 238, 409, 410, 411, 410, 409, 414, 409, 416, 417, 418, 417, 416, 421, 416, 423, 416, 425, 426, 425, 416, 409, 430, 409, 432, 433, 432, 435, 432, 409, 438, 439, 438, 409, 442, 409, 444, 409, 446, 409, 448, 409, 450, 409, 452, 409, 454, 409, 238, 131, 458, 459, 460, 461, 462, 461, 460, 465, 460, 459, 468, 459, 458, 471, 458, 473, 458, 131, 476, 477, 478, 479, 478, 481, 478, 477, 476, 485, 486, 485, 476, 489, 490, 489, 476, 493, 476, 495, 496, 497, 496, 499, 496, 495, 502, 503, 504, 503, 502, 507, 502, 509, 502, 495, 512, 495, 514, 495, 516, 495, 476, 131, 520, 521, 522, 521, 520, 525, 520, 527, 520, 529, 520, 531, 520, 533, 534, 533, 520, 537, 520, 539, 520, 541, 520, 131, 0]
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

private theorem checked_shape_544 : ∀ k : Fin 1, Step (544+k.val) := by decide +kernel

private theorem checked_steps : ∀ i : Fin nodes.size, Step i.val := by
  intro i
  have hi : i.val < 545 := i.isLt
  by_cases hsplit_272 : i.val < 272
  · by_cases hsplit_128 : i.val < 128
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
          · have hlocal : i.val-112 < 16 := by omega
            have hh := checked_shape_112 ⟨i.val-112,hlocal⟩
            have heq : 112+(i.val-112)=i.val := by omega
            simpa only [heq] using hh
    · by_cases hsplit_192 : i.val < 192
      · by_cases hsplit_160 : i.val < 160
        · by_cases hsplit_144 : i.val < 144
          · have hlocal : i.val-128 < 16 := by omega
            have hh := checked_shape_128 ⟨i.val-128,hlocal⟩
            have heq : 128+(i.val-128)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-144 < 16 := by omega
            have hh := checked_shape_144 ⟨i.val-144,hlocal⟩
            have heq : 144+(i.val-144)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_176 : i.val < 176
          · have hlocal : i.val-160 < 16 := by omega
            have hh := checked_shape_160 ⟨i.val-160,hlocal⟩
            have heq : 160+(i.val-160)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-176 < 16 := by omega
            have hh := checked_shape_176 ⟨i.val-176,hlocal⟩
            have heq : 176+(i.val-176)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_224 : i.val < 224
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
  · by_cases hsplit_416 : i.val < 416
    · by_cases hsplit_336 : i.val < 336
      · by_cases hsplit_304 : i.val < 304
        · by_cases hsplit_288 : i.val < 288
          · have hlocal : i.val-272 < 16 := by omega
            have hh := checked_shape_272 ⟨i.val-272,hlocal⟩
            have heq : 272+(i.val-272)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-288 < 16 := by omega
            have hh := checked_shape_288 ⟨i.val-288,hlocal⟩
            have heq : 288+(i.val-288)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_320 : i.val < 320
          · have hlocal : i.val-304 < 16 := by omega
            have hh := checked_shape_304 ⟨i.val-304,hlocal⟩
            have heq : 304+(i.val-304)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-320 < 16 := by omega
            have hh := checked_shape_320 ⟨i.val-320,hlocal⟩
            have heq : 320+(i.val-320)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_368 : i.val < 368
        · by_cases hsplit_352 : i.val < 352
          · have hlocal : i.val-336 < 16 := by omega
            have hh := checked_shape_336 ⟨i.val-336,hlocal⟩
            have heq : 336+(i.val-336)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-352 < 16 := by omega
            have hh := checked_shape_352 ⟨i.val-352,hlocal⟩
            have heq : 352+(i.val-352)=i.val := by omega
            simpa only [heq] using hh
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
    · by_cases hsplit_480 : i.val < 480
      · by_cases hsplit_448 : i.val < 448
        · by_cases hsplit_432 : i.val < 432
          · have hlocal : i.val-416 < 16 := by omega
            have hh := checked_shape_416 ⟨i.val-416,hlocal⟩
            have heq : 416+(i.val-416)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-432 < 16 := by omega
            have hh := checked_shape_432 ⟨i.val-432,hlocal⟩
            have heq : 432+(i.val-432)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_464 : i.val < 464
          · have hlocal : i.val-448 < 16 := by omega
            have hh := checked_shape_448 ⟨i.val-448,hlocal⟩
            have heq : 448+(i.val-448)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-464 < 16 := by omega
            have hh := checked_shape_464 ⟨i.val-464,hlocal⟩
            have heq : 464+(i.val-464)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_512 : i.val < 512
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
            · have hlocal : i.val-544 < 1 := by omega
              have hh := checked_shape_544 ⟨i.val-544,hlocal⟩
              have heq : 544+(i.val-544)=i.val := by omega
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
  change walk nodes 545 544 = List.range 545
  rw [List.range_eq_range']
  have hh := traversal 545 544 (by decide +kernel) (by decide +kernel)
  change walk nodes 545 544 = List.range' 0 545 at hh
  exact hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N85B
