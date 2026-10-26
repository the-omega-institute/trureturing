/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N80A
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N80A
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N80A.accepted
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N80A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N80AShape
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N80A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem checked_nodes_0 : ∀ k : Fin 16, NodeOK 80 false nodes (0+k.val) := by decide +kernel

private theorem checked_nodes_16 : ∀ k : Fin 16, NodeOK 80 false nodes (16+k.val) := by decide +kernel

private theorem checked_nodes_32 : ∀ k : Fin 16, NodeOK 80 false nodes (32+k.val) := by decide +kernel

private theorem checked_nodes_48 : ∀ k : Fin 16, NodeOK 80 false nodes (48+k.val) := by decide +kernel

private theorem checked_nodes_64 : ∀ k : Fin 16, NodeOK 80 false nodes (64+k.val) := by decide +kernel

private theorem checked_nodes_80 : ∀ k : Fin 16, NodeOK 80 false nodes (80+k.val) := by decide +kernel

private theorem checked_nodes_96 : ∀ k : Fin 16, NodeOK 80 false nodes (96+k.val) := by decide +kernel

private theorem checked_nodes_112 : ∀ k : Fin 16, NodeOK 80 false nodes (112+k.val) := by decide +kernel

private theorem checked_nodes_128 : ∀ k : Fin 16, NodeOK 80 false nodes (128+k.val) := by decide +kernel

private theorem checked_nodes_144 : ∀ k : Fin 16, NodeOK 80 false nodes (144+k.val) := by decide +kernel

private theorem checked_nodes_160 : ∀ k : Fin 16, NodeOK 80 false nodes (160+k.val) := by decide +kernel

private theorem checked_nodes_176 : ∀ k : Fin 16, NodeOK 80 false nodes (176+k.val) := by decide +kernel

private theorem checked_nodes_192 : ∀ k : Fin 16, NodeOK 80 false nodes (192+k.val) := by decide +kernel

private theorem checked_nodes_208 : ∀ k : Fin 16, NodeOK 80 false nodes (208+k.val) := by decide +kernel

private theorem checked_nodes_224 : ∀ k : Fin 16, NodeOK 80 false nodes (224+k.val) := by decide +kernel

private theorem checked_nodes_240 : ∀ k : Fin 16, NodeOK 80 false nodes (240+k.val) := by decide +kernel

private theorem checked_nodes_256 : ∀ k : Fin 16, NodeOK 80 false nodes (256+k.val) := by decide +kernel

private theorem checked_nodes_272 : ∀ k : Fin 16, NodeOK 80 false nodes (272+k.val) := by decide +kernel

private theorem checked_nodes_288 : ∀ k : Fin 16, NodeOK 80 false nodes (288+k.val) := by decide +kernel

private theorem checked_nodes_304 : ∀ k : Fin 16, NodeOK 80 false nodes (304+k.val) := by decide +kernel

private theorem checked_nodes_320 : ∀ k : Fin 16, NodeOK 80 false nodes (320+k.val) := by decide +kernel

private theorem checked_nodes_336 : ∀ k : Fin 16, NodeOK 80 false nodes (336+k.val) := by decide +kernel

private theorem checked_nodes_352 : ∀ k : Fin 16, NodeOK 80 false nodes (352+k.val) := by decide +kernel

private theorem checked_nodes_368 : ∀ k : Fin 16, NodeOK 80 false nodes (368+k.val) := by decide +kernel

private theorem checked_nodes_384 : ∀ k : Fin 16, NodeOK 80 false nodes (384+k.val) := by decide +kernel

private theorem checked_nodes_400 : ∀ k : Fin 16, NodeOK 80 false nodes (400+k.val) := by decide +kernel

private theorem checked_nodes_416 : ∀ k : Fin 16, NodeOK 80 false nodes (416+k.val) := by decide +kernel

private theorem checked_nodes_432 : ∀ k : Fin 16, NodeOK 80 false nodes (432+k.val) := by decide +kernel

private theorem checked_nodes_448 : ∀ k : Fin 16, NodeOK 80 false nodes (448+k.val) := by decide +kernel

private theorem checked_nodes_464 : ∀ k : Fin 16, NodeOK 80 false nodes (464+k.val) := by decide +kernel

private theorem checked_nodes_480 : ∀ k : Fin 16, NodeOK 80 false nodes (480+k.val) := by decide +kernel

private theorem checked_nodes_496 : ∀ k : Fin 16, NodeOK 80 false nodes (496+k.val) := by decide +kernel

private theorem checked_nodes_512 : ∀ k : Fin 16, NodeOK 80 false nodes (512+k.val) := by decide +kernel

private theorem checked_nodes_528 : ∀ k : Fin 1, NodeOK 80 false nodes (528+k.val) := by decide +kernel

private theorem checked_root : ∀ k, (node nodes (nodes.size-1)).box k = rootBox k := by decide +kernel

theorem accepted : check 80 false nodes=true := by
  apply decide_eq_true
  refine ⟨by decide +kernel, ?_, checked_walk, checked_root⟩
  intro i
  have hi : i.val < 529 := i.isLt
  by_cases hsplit_272 : i.val < 272
  · by_cases hsplit_128 : i.val < 128
    · by_cases hsplit_64 : i.val < 64
      · by_cases hsplit_32 : i.val < 32
        · by_cases hsplit_16 : i.val < 16
          · have hlocal : i.val-0 < 16 := by omega
            have hh := checked_nodes_0 ⟨i.val-0,hlocal⟩
            have heq : 0+(i.val-0)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-16 < 16 := by omega
            have hh := checked_nodes_16 ⟨i.val-16,hlocal⟩
            have heq : 16+(i.val-16)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_48 : i.val < 48
          · have hlocal : i.val-32 < 16 := by omega
            have hh := checked_nodes_32 ⟨i.val-32,hlocal⟩
            have heq : 32+(i.val-32)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-48 < 16 := by omega
            have hh := checked_nodes_48 ⟨i.val-48,hlocal⟩
            have heq : 48+(i.val-48)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_96 : i.val < 96
        · by_cases hsplit_80 : i.val < 80
          · have hlocal : i.val-64 < 16 := by omega
            have hh := checked_nodes_64 ⟨i.val-64,hlocal⟩
            have heq : 64+(i.val-64)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-80 < 16 := by omega
            have hh := checked_nodes_80 ⟨i.val-80,hlocal⟩
            have heq : 80+(i.val-80)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_112 : i.val < 112
          · have hlocal : i.val-96 < 16 := by omega
            have hh := checked_nodes_96 ⟨i.val-96,hlocal⟩
            have heq : 96+(i.val-96)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-112 < 16 := by omega
            have hh := checked_nodes_112 ⟨i.val-112,hlocal⟩
            have heq : 112+(i.val-112)=i.val := by omega
            simpa only [heq] using hh
    · by_cases hsplit_192 : i.val < 192
      · by_cases hsplit_160 : i.val < 160
        · by_cases hsplit_144 : i.val < 144
          · have hlocal : i.val-128 < 16 := by omega
            have hh := checked_nodes_128 ⟨i.val-128,hlocal⟩
            have heq : 128+(i.val-128)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-144 < 16 := by omega
            have hh := checked_nodes_144 ⟨i.val-144,hlocal⟩
            have heq : 144+(i.val-144)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_176 : i.val < 176
          · have hlocal : i.val-160 < 16 := by omega
            have hh := checked_nodes_160 ⟨i.val-160,hlocal⟩
            have heq : 160+(i.val-160)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-176 < 16 := by omega
            have hh := checked_nodes_176 ⟨i.val-176,hlocal⟩
            have heq : 176+(i.val-176)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_224 : i.val < 224
        · by_cases hsplit_208 : i.val < 208
          · have hlocal : i.val-192 < 16 := by omega
            have hh := checked_nodes_192 ⟨i.val-192,hlocal⟩
            have heq : 192+(i.val-192)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-208 < 16 := by omega
            have hh := checked_nodes_208 ⟨i.val-208,hlocal⟩
            have heq : 208+(i.val-208)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_240 : i.val < 240
          · have hlocal : i.val-224 < 16 := by omega
            have hh := checked_nodes_224 ⟨i.val-224,hlocal⟩
            have heq : 224+(i.val-224)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_256 : i.val < 256
            · have hlocal : i.val-240 < 16 := by omega
              have hh := checked_nodes_240 ⟨i.val-240,hlocal⟩
              have heq : 240+(i.val-240)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-256 < 16 := by omega
              have hh := checked_nodes_256 ⟨i.val-256,hlocal⟩
              have heq : 256+(i.val-256)=i.val := by omega
              simpa only [heq] using hh
  · by_cases hsplit_400 : i.val < 400
    · by_cases hsplit_336 : i.val < 336
      · by_cases hsplit_304 : i.val < 304
        · by_cases hsplit_288 : i.val < 288
          · have hlocal : i.val-272 < 16 := by omega
            have hh := checked_nodes_272 ⟨i.val-272,hlocal⟩
            have heq : 272+(i.val-272)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-288 < 16 := by omega
            have hh := checked_nodes_288 ⟨i.val-288,hlocal⟩
            have heq : 288+(i.val-288)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_320 : i.val < 320
          · have hlocal : i.val-304 < 16 := by omega
            have hh := checked_nodes_304 ⟨i.val-304,hlocal⟩
            have heq : 304+(i.val-304)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-320 < 16 := by omega
            have hh := checked_nodes_320 ⟨i.val-320,hlocal⟩
            have heq : 320+(i.val-320)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_368 : i.val < 368
        · by_cases hsplit_352 : i.val < 352
          · have hlocal : i.val-336 < 16 := by omega
            have hh := checked_nodes_336 ⟨i.val-336,hlocal⟩
            have heq : 336+(i.val-336)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-352 < 16 := by omega
            have hh := checked_nodes_352 ⟨i.val-352,hlocal⟩
            have heq : 352+(i.val-352)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_384 : i.val < 384
          · have hlocal : i.val-368 < 16 := by omega
            have hh := checked_nodes_368 ⟨i.val-368,hlocal⟩
            have heq : 368+(i.val-368)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-384 < 16 := by omega
            have hh := checked_nodes_384 ⟨i.val-384,hlocal⟩
            have heq : 384+(i.val-384)=i.val := by omega
            simpa only [heq] using hh
    · by_cases hsplit_464 : i.val < 464
      · by_cases hsplit_432 : i.val < 432
        · by_cases hsplit_416 : i.val < 416
          · have hlocal : i.val-400 < 16 := by omega
            have hh := checked_nodes_400 ⟨i.val-400,hlocal⟩
            have heq : 400+(i.val-400)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-416 < 16 := by omega
            have hh := checked_nodes_416 ⟨i.val-416,hlocal⟩
            have heq : 416+(i.val-416)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_448 : i.val < 448
          · have hlocal : i.val-432 < 16 := by omega
            have hh := checked_nodes_432 ⟨i.val-432,hlocal⟩
            have heq : 432+(i.val-432)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-448 < 16 := by omega
            have hh := checked_nodes_448 ⟨i.val-448,hlocal⟩
            have heq : 448+(i.val-448)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_496 : i.val < 496
        · by_cases hsplit_480 : i.val < 480
          · have hlocal : i.val-464 < 16 := by omega
            have hh := checked_nodes_464 ⟨i.val-464,hlocal⟩
            have heq : 464+(i.val-464)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-480 < 16 := by omega
            have hh := checked_nodes_480 ⟨i.val-480,hlocal⟩
            have heq : 480+(i.val-480)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_512 : i.val < 512
          · have hlocal : i.val-496 < 16 := by omega
            have hh := checked_nodes_496 ⟨i.val-496,hlocal⟩
            have heq : 496+(i.val-496)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_528 : i.val < 528
            · have hlocal : i.val-512 < 16 := by omega
              have hh := checked_nodes_512 ⟨i.val-512,hlocal⟩
              have heq : 512+(i.val-512)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-528 < 1 := by omega
              have hh := checked_nodes_528 ⟨i.val-528,hlocal⟩
              have heq : 528+(i.val-528)=i.val := by omega
              simpa only [heq] using hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N80A
