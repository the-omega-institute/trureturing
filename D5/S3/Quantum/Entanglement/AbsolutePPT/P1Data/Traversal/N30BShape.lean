/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30BShape
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30BShape
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N30BShape.checked_walk
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30B
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private def starts : Array Nat := #[0, 1, 2, 3, 4, 5, 4, 3, 2, 9, 10, 11, 12, 11, 10, 9, 2, 17, 2, 19, 20, 21, 20, 23, 24, 23, 20, 19, 28, 29, 30, 29, 32, 29, 28, 19, 36, 19, 2, 39, 40, 39, 42, 39, 44, 45, 44, 47, 44, 39, 50, 39, 52, 39, 54, 55, 54, 39, 58, 59, 58, 61, 62, 61, 58, 39, 66, 67, 66, 69, 66, 71, 66, 39, 74, 39, 76, 77, 76, 79, 76, 39, 82, 83, 82, 85, 82, 87, 82, 89, 82, 91, 82, 93, 94, 93, 82, 39, 98, 99, 98, 101, 102, 101, 98, 105, 106, 105, 98, 39, 110, 39, 112, 113, 112, 115, 112, 117, 112, 119, 112, 121, 112, 39, 2, 125, 2, 127, 128, 127, 130, 131, 132, 131, 134, 131, 130, 127, 138, 139, 140, 141, 140, 139, 144, 145, 144, 147, 144, 139, 150, 151, 150, 153, 150, 139, 138, 157, 138, 127, 160, 161, 162, 163, 164, 165, 164, 163, 162, 169, 170, 169, 172, 169, 162, 175, 162, 161, 160, 127, 2, 1, 182, 183, 182, 185, 182, 1, 188, 189, 190, 191, 190, 189, 188, 195, 196, 197, 198, 197, 196, 201, 202, 201, 196, 205, 196, 207, 208, 209, 208, 211, 208, 207, 196, 215, 216, 215, 218, 215, 220, 215, 222, 215, 224, 225, 224, 227, 224, 229, 224, 215, 232, 215, 196, 195, 236, 195, 188, 239, 240, 241, 242, 241, 240, 245, 240, 239, 248, 249, 250, 249, 248, 253, 254, 255, 256, 255, 258, 255, 260, 255, 254, 253, 264, 265, 266, 265, 264, 253, 270, 271, 270, 273, 274, 273, 276, 273, 270, 279, 270, 253, 248, 239, 284, 285, 286, 285, 288, 285, 290, 285, 284, 293, 284, 295, 284, 297, 284, 239, 188, 1, 302, 303, 302, 305, 302, 307, 302, 309, 302, 311, 302, 313, 314, 313, 302, 317, 318, 319, 318, 317, 302, 323, 302, 325, 326, 327, 326, 329, 326, 331, 326, 333, 326, 325, 336, 325, 338, 325, 340, 341, 342, 341, 344, 341, 340, 347, 340, 325, 302, 351, 352, 351, 302, 355, 302, 357, 302, 1, 0, 361, 362, 363, 362, 365, 362, 367, 368, 367, 370, 367, 372, 367, 362, 375, 376, 377, 376, 375, 362, 381, 382, 383, 382, 381, 386, 381, 362, 389, 362, 391, 392, 391, 394, 391, 396, 391, 398, 391, 400, 401, 400, 403, 400, 391, 362, 361, 408, 409, 408, 411, 408, 413, 414, 413, 408, 417, 418, 417, 408, 361, 422, 423, 424, 423, 422, 427, 422, 429, 422, 361, 432, 433, 434, 435, 434, 433, 432, 439, 440, 441, 440, 443, 440, 439, 432, 447, 448, 447, 450, 447, 432, 453, 432, 455, 456, 457, 456, 459, 456, 455, 462, 463, 464, 463, 462, 467, 468, 467, 462, 471, 462, 455, 474, 475, 474, 477, 474, 455, 480, 481, 480, 455, 484, 455, 432, 361, 488, 489, 488, 491, 488, 493, 488, 495, 488, 497, 488, 361, 0]
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

private theorem checked_shape_496 : ∀ k : Fin 5, Step (496+k.val) := by decide +kernel

private theorem checked_steps : ∀ i : Fin nodes.size, Step i.val := by
  intro i
  have hi : i.val < 501 := i.isLt
  by_cases hsplit_256 : i.val < 256
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
          · have hlocal : i.val-240 < 16 := by omega
            have hh := checked_shape_240 ⟨i.val-240,hlocal⟩
            have heq : 240+(i.val-240)=i.val := by omega
            simpa only [heq] using hh
  · by_cases hsplit_384 : i.val < 384
    · by_cases hsplit_320 : i.val < 320
      · by_cases hsplit_288 : i.val < 288
        · by_cases hsplit_272 : i.val < 272
          · have hlocal : i.val-256 < 16 := by omega
            have hh := checked_shape_256 ⟨i.val-256,hlocal⟩
            have heq : 256+(i.val-256)=i.val := by omega
            simpa only [heq] using hh
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
      · by_cases hsplit_352 : i.val < 352
        · by_cases hsplit_336 : i.val < 336
          · have hlocal : i.val-320 < 16 := by omega
            have hh := checked_shape_320 ⟨i.val-320,hlocal⟩
            have heq : 320+(i.val-320)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-336 < 16 := by omega
            have hh := checked_shape_336 ⟨i.val-336,hlocal⟩
            have heq : 336+(i.val-336)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_368 : i.val < 368
          · have hlocal : i.val-352 < 16 := by omega
            have hh := checked_shape_352 ⟨i.val-352,hlocal⟩
            have heq : 352+(i.val-352)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-368 < 16 := by omega
            have hh := checked_shape_368 ⟨i.val-368,hlocal⟩
            have heq : 368+(i.val-368)=i.val := by omega
            simpa only [heq] using hh
    · by_cases hsplit_448 : i.val < 448
      · by_cases hsplit_416 : i.val < 416
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
          · have hlocal : i.val-432 < 16 := by omega
            have hh := checked_shape_432 ⟨i.val-432,hlocal⟩
            have heq : 432+(i.val-432)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_480 : i.val < 480
        · by_cases hsplit_464 : i.val < 464
          · have hlocal : i.val-448 < 16 := by omega
            have hh := checked_shape_448 ⟨i.val-448,hlocal⟩
            have heq : 448+(i.val-448)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-464 < 16 := by omega
            have hh := checked_shape_464 ⟨i.val-464,hlocal⟩
            have heq : 464+(i.val-464)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_496 : i.val < 496
          · have hlocal : i.val-480 < 16 := by omega
            have hh := checked_shape_480 ⟨i.val-480,hlocal⟩
            have heq : 480+(i.val-480)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-496 < 5 := by omega
            have hh := checked_shape_496 ⟨i.val-496,hlocal⟩
            have heq : 496+(i.val-496)=i.val := by omega
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
  change walk nodes 501 500 = List.range 501
  rw [List.range_eq_range']
  have hh := traversal 501 500 (by decide +kernel) (by decide +kernel)
  change walk nodes 501 500 = List.range' 0 501 at hh
  exact hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30B
