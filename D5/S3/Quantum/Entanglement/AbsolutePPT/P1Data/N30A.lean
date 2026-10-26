/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N30A
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N30A
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N30A.accepted
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N30APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N30APart01
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N30APart02
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N30AWalk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem checked_root : ∀ k, (node nodes (nodes.size-1)).box k = rootBox k := by decide +kernel

theorem accepted : check 30 false nodes=true := by
  apply decide_eq_true
  refine ⟨by decide +kernel, ?_, checked_walk, checked_root⟩
  intro i
  have hi : i.val < 567 := i.isLt

  by_cases hsplit_288 : i.val < 288
  · by_cases hsplit_144 : i.val < 144
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
          · by_cases hsplit_128 : i.val < 128
            · have hlocal : i.val-112 < 16 := by omega
              have hh := checked_nodes_112 ⟨i.val-112,hlocal⟩
              have heq : 112+(i.val-112)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-128 < 16 := by omega
              have hh := checked_nodes_128 ⟨i.val-128,hlocal⟩
              have heq : 128+(i.val-128)=i.val := by omega
              simpa only [heq] using hh
    · by_cases hsplit_208 : i.val < 208
      · by_cases hsplit_176 : i.val < 176
        · by_cases hsplit_160 : i.val < 160
          · have hlocal : i.val-144 < 16 := by omega
            have hh := checked_nodes_144 ⟨i.val-144,hlocal⟩
            have heq : 144+(i.val-144)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-160 < 16 := by omega
            have hh := checked_nodes_160 ⟨i.val-160,hlocal⟩
            have heq : 160+(i.val-160)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_192 : i.val < 192
          · have hlocal : i.val-176 < 16 := by omega
            have hh := checked_nodes_176 ⟨i.val-176,hlocal⟩
            have heq : 176+(i.val-176)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-192 < 16 := by omega
            have hh := checked_nodes_192 ⟨i.val-192,hlocal⟩
            have heq : 192+(i.val-192)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_240 : i.val < 240
        · by_cases hsplit_224 : i.val < 224
          · have hlocal : i.val-208 < 16 := by omega
            have hh := checked_nodes_208 ⟨i.val-208,hlocal⟩
            have heq : 208+(i.val-208)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-224 < 16 := by omega
            have hh := checked_nodes_224 ⟨i.val-224,hlocal⟩
            have heq : 224+(i.val-224)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_256 : i.val < 256
          · have hlocal : i.val-240 < 16 := by omega
            have hh := checked_nodes_240 ⟨i.val-240,hlocal⟩
            have heq : 240+(i.val-240)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_272 : i.val < 272
            · have hlocal : i.val-256 < 16 := by omega
              have hh := checked_nodes_256 ⟨i.val-256,hlocal⟩
              have heq : 256+(i.val-256)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-272 < 16 := by omega
              have hh := checked_nodes_272 ⟨i.val-272,hlocal⟩
              have heq : 272+(i.val-272)=i.val := by omega
              simpa only [heq] using hh
  · by_cases hsplit_432 : i.val < 432
    · by_cases hsplit_352 : i.val < 352
      · by_cases hsplit_320 : i.val < 320
        · by_cases hsplit_304 : i.val < 304
          · have hlocal : i.val-288 < 16 := by omega
            have hh := checked_nodes_288 ⟨i.val-288,hlocal⟩
            have heq : 288+(i.val-288)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-304 < 16 := by omega
            have hh := checked_nodes_304 ⟨i.val-304,hlocal⟩
            have heq : 304+(i.val-304)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_336 : i.val < 336
          · have hlocal : i.val-320 < 16 := by omega
            have hh := checked_nodes_320 ⟨i.val-320,hlocal⟩
            have heq : 320+(i.val-320)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-336 < 16 := by omega
            have hh := checked_nodes_336 ⟨i.val-336,hlocal⟩
            have heq : 336+(i.val-336)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_384 : i.val < 384
        · by_cases hsplit_368 : i.val < 368
          · have hlocal : i.val-352 < 16 := by omega
            have hh := checked_nodes_352 ⟨i.val-352,hlocal⟩
            have heq : 352+(i.val-352)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-368 < 16 := by omega
            have hh := checked_nodes_368 ⟨i.val-368,hlocal⟩
            have heq : 368+(i.val-368)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_400 : i.val < 400
          · have hlocal : i.val-384 < 16 := by omega
            have hh := checked_nodes_384 ⟨i.val-384,hlocal⟩
            have heq : 384+(i.val-384)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_416 : i.val < 416
            · have hlocal : i.val-400 < 16 := by omega
              have hh := checked_nodes_400 ⟨i.val-400,hlocal⟩
              have heq : 400+(i.val-400)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-416 < 16 := by omega
              have hh := checked_nodes_416 ⟨i.val-416,hlocal⟩
              have heq : 416+(i.val-416)=i.val := by omega
              simpa only [heq] using hh
    · by_cases hsplit_496 : i.val < 496
      · by_cases hsplit_464 : i.val < 464
        · by_cases hsplit_448 : i.val < 448
          · have hlocal : i.val-432 < 16 := by omega
            have hh := checked_nodes_432 ⟨i.val-432,hlocal⟩
            have heq : 432+(i.val-432)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-448 < 16 := by omega
            have hh := checked_nodes_448 ⟨i.val-448,hlocal⟩
            have heq : 448+(i.val-448)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_480 : i.val < 480
          · have hlocal : i.val-464 < 16 := by omega
            have hh := checked_nodes_464 ⟨i.val-464,hlocal⟩
            have heq : 464+(i.val-464)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-480 < 16 := by omega
            have hh := checked_nodes_480 ⟨i.val-480,hlocal⟩
            have heq : 480+(i.val-480)=i.val := by omega
            simpa only [heq] using hh
      · by_cases hsplit_528 : i.val < 528
        · by_cases hsplit_512 : i.val < 512
          · have hlocal : i.val-496 < 16 := by omega
            have hh := checked_nodes_496 ⟨i.val-496,hlocal⟩
            have heq : 496+(i.val-496)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-512 < 16 := by omega
            have hh := checked_nodes_512 ⟨i.val-512,hlocal⟩
            have heq : 512+(i.val-512)=i.val := by omega
            simpa only [heq] using hh
        · by_cases hsplit_544 : i.val < 544
          · have hlocal : i.val-528 < 16 := by omega
            have hh := checked_nodes_528 ⟨i.val-528,hlocal⟩
            have heq : 528+(i.val-528)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_560 : i.val < 560
            · have hlocal : i.val-544 < 16 := by omega
              have hh := checked_nodes_544 ⟨i.val-544,hlocal⟩
              have heq : 544+(i.val-544)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-560 < 7 := by omega
              have hh := checked_nodes_560 ⟨i.val-560,hlocal⟩
              have heq : 560+(i.val-560)=i.val := by omega
              simpa only [heq] using hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
