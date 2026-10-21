/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25B
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25B
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25B.accepted
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25BPart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25BPart01
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25BPart02
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25BPart03
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BWalk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem checked_root : ∀ k, (node nodes (nodes.size-1)).box k = rootBox k := by decide +kernel

theorem accepted : check 25 true nodes=true := by
  apply decide_eq_true
  refine ⟨by decide +kernel, ?_, checked_walk, checked_root⟩
  intro i
  have hi : i.val < 883 := i.isLt

  by_cases hsplit_448 : i.val < 448
  · by_cases hsplit_224 : i.val < 224
    · by_cases hsplit_112 : i.val < 112
      · by_cases hsplit_48 : i.val < 48
        · by_cases hsplit_16 : i.val < 16
          · have hlocal : i.val-0 < 16 := by omega
            have hh := checked_nodes_0 ⟨i.val-0,hlocal⟩
            have heq : 0+(i.val-0)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_32 : i.val < 32
            · have hlocal : i.val-16 < 16 := by omega
              have hh := checked_nodes_16 ⟨i.val-16,hlocal⟩
              have heq : 16+(i.val-16)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-32 < 16 := by omega
              have hh := checked_nodes_32 ⟨i.val-32,hlocal⟩
              have heq : 32+(i.val-32)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_80 : i.val < 80
          · by_cases hsplit_64 : i.val < 64
            · have hlocal : i.val-48 < 16 := by omega
              have hh := checked_nodes_48 ⟨i.val-48,hlocal⟩
              have heq : 48+(i.val-48)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-64 < 16 := by omega
              have hh := checked_nodes_64 ⟨i.val-64,hlocal⟩
              have heq : 64+(i.val-64)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_96 : i.val < 96
            · have hlocal : i.val-80 < 16 := by omega
              have hh := checked_nodes_80 ⟨i.val-80,hlocal⟩
              have heq : 80+(i.val-80)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-96 < 16 := by omega
              have hh := checked_nodes_96 ⟨i.val-96,hlocal⟩
              have heq : 96+(i.val-96)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_160 : i.val < 160
        · by_cases hsplit_128 : i.val < 128
          · have hlocal : i.val-112 < 16 := by omega
            have hh := checked_nodes_112 ⟨i.val-112,hlocal⟩
            have heq : 112+(i.val-112)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_144 : i.val < 144
            · have hlocal : i.val-128 < 16 := by omega
              have hh := checked_nodes_128 ⟨i.val-128,hlocal⟩
              have heq : 128+(i.val-128)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-144 < 16 := by omega
              have hh := checked_nodes_144 ⟨i.val-144,hlocal⟩
              have heq : 144+(i.val-144)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_192 : i.val < 192
          · by_cases hsplit_176 : i.val < 176
            · have hlocal : i.val-160 < 16 := by omega
              have hh := checked_nodes_160 ⟨i.val-160,hlocal⟩
              have heq : 160+(i.val-160)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-176 < 16 := by omega
              have hh := checked_nodes_176 ⟨i.val-176,hlocal⟩
              have heq : 176+(i.val-176)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_208 : i.val < 208
            · have hlocal : i.val-192 < 16 := by omega
              have hh := checked_nodes_192 ⟨i.val-192,hlocal⟩
              have heq : 192+(i.val-192)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-208 < 16 := by omega
              have hh := checked_nodes_208 ⟨i.val-208,hlocal⟩
              have heq : 208+(i.val-208)=i.val := by omega
              simpa only [heq] using hh
    · by_cases hsplit_336 : i.val < 336
      · by_cases hsplit_272 : i.val < 272
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
      · by_cases hsplit_384 : i.val < 384
        · by_cases hsplit_352 : i.val < 352
          · have hlocal : i.val-336 < 16 := by omega
            have hh := checked_nodes_336 ⟨i.val-336,hlocal⟩
            have heq : 336+(i.val-336)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_368 : i.val < 368
            · have hlocal : i.val-352 < 16 := by omega
              have hh := checked_nodes_352 ⟨i.val-352,hlocal⟩
              have heq : 352+(i.val-352)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-368 < 16 := by omega
              have hh := checked_nodes_368 ⟨i.val-368,hlocal⟩
              have heq : 368+(i.val-368)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_416 : i.val < 416
          · by_cases hsplit_400 : i.val < 400
            · have hlocal : i.val-384 < 16 := by omega
              have hh := checked_nodes_384 ⟨i.val-384,hlocal⟩
              have heq : 384+(i.val-384)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-400 < 16 := by omega
              have hh := checked_nodes_400 ⟨i.val-400,hlocal⟩
              have heq : 400+(i.val-400)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_432 : i.val < 432
            · have hlocal : i.val-416 < 16 := by omega
              have hh := checked_nodes_416 ⟨i.val-416,hlocal⟩
              have heq : 416+(i.val-416)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-432 < 16 := by omega
              have hh := checked_nodes_432 ⟨i.val-432,hlocal⟩
              have heq : 432+(i.val-432)=i.val := by omega
              simpa only [heq] using hh
  · by_cases hsplit_672 : i.val < 672
    · by_cases hsplit_560 : i.val < 560
      · by_cases hsplit_496 : i.val < 496
        · by_cases hsplit_464 : i.val < 464
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
            · have hlocal : i.val-544 < 16 := by omega
              have hh := checked_nodes_544 ⟨i.val-544,hlocal⟩
              have heq : 544+(i.val-544)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_608 : i.val < 608
        · by_cases hsplit_576 : i.val < 576
          · have hlocal : i.val-560 < 16 := by omega
            have hh := checked_nodes_560 ⟨i.val-560,hlocal⟩
            have heq : 560+(i.val-560)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_592 : i.val < 592
            · have hlocal : i.val-576 < 16 := by omega
              have hh := checked_nodes_576 ⟨i.val-576,hlocal⟩
              have heq : 576+(i.val-576)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-592 < 16 := by omega
              have hh := checked_nodes_592 ⟨i.val-592,hlocal⟩
              have heq : 592+(i.val-592)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_640 : i.val < 640
          · by_cases hsplit_624 : i.val < 624
            · have hlocal : i.val-608 < 16 := by omega
              have hh := checked_nodes_608 ⟨i.val-608,hlocal⟩
              have heq : 608+(i.val-608)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-624 < 16 := by omega
              have hh := checked_nodes_624 ⟨i.val-624,hlocal⟩
              have heq : 624+(i.val-624)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_656 : i.val < 656
            · have hlocal : i.val-640 < 16 := by omega
              have hh := checked_nodes_640 ⟨i.val-640,hlocal⟩
              have heq : 640+(i.val-640)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-656 < 16 := by omega
              have hh := checked_nodes_656 ⟨i.val-656,hlocal⟩
              have heq : 656+(i.val-656)=i.val := by omega
              simpa only [heq] using hh
    · by_cases hsplit_784 : i.val < 784
      · by_cases hsplit_720 : i.val < 720
        · by_cases hsplit_688 : i.val < 688
          · have hlocal : i.val-672 < 16 := by omega
            have hh := checked_nodes_672 ⟨i.val-672,hlocal⟩
            have heq : 672+(i.val-672)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_704 : i.val < 704
            · have hlocal : i.val-688 < 16 := by omega
              have hh := checked_nodes_688 ⟨i.val-688,hlocal⟩
              have heq : 688+(i.val-688)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-704 < 16 := by omega
              have hh := checked_nodes_704 ⟨i.val-704,hlocal⟩
              have heq : 704+(i.val-704)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_752 : i.val < 752
          · by_cases hsplit_736 : i.val < 736
            · have hlocal : i.val-720 < 16 := by omega
              have hh := checked_nodes_720 ⟨i.val-720,hlocal⟩
              have heq : 720+(i.val-720)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-736 < 16 := by omega
              have hh := checked_nodes_736 ⟨i.val-736,hlocal⟩
              have heq : 736+(i.val-736)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_768 : i.val < 768
            · have hlocal : i.val-752 < 16 := by omega
              have hh := checked_nodes_752 ⟨i.val-752,hlocal⟩
              have heq : 752+(i.val-752)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-768 < 16 := by omega
              have hh := checked_nodes_768 ⟨i.val-768,hlocal⟩
              have heq : 768+(i.val-768)=i.val := by omega
              simpa only [heq] using hh
      · by_cases hsplit_832 : i.val < 832
        · by_cases hsplit_800 : i.val < 800
          · have hlocal : i.val-784 < 16 := by omega
            have hh := checked_nodes_784 ⟨i.val-784,hlocal⟩
            have heq : 784+(i.val-784)=i.val := by omega
            simpa only [heq] using hh
          · by_cases hsplit_816 : i.val < 816
            · have hlocal : i.val-800 < 16 := by omega
              have hh := checked_nodes_800 ⟨i.val-800,hlocal⟩
              have heq : 800+(i.val-800)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-816 < 16 := by omega
              have hh := checked_nodes_816 ⟨i.val-816,hlocal⟩
              have heq : 816+(i.val-816)=i.val := by omega
              simpa only [heq] using hh
        · by_cases hsplit_864 : i.val < 864
          · by_cases hsplit_848 : i.val < 848
            · have hlocal : i.val-832 < 16 := by omega
              have hh := checked_nodes_832 ⟨i.val-832,hlocal⟩
              have heq : 832+(i.val-832)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-848 < 16 := by omega
              have hh := checked_nodes_848 ⟨i.val-848,hlocal⟩
              have heq : 848+(i.val-848)=i.val := by omega
              simpa only [heq] using hh
          · by_cases hsplit_880 : i.val < 880
            · have hlocal : i.val-864 < 16 := by omega
              have hh := checked_nodes_864 ⟨i.val-864,hlocal⟩
              have heq : 864+(i.val-864)=i.val := by omega
              simpa only [heq] using hh
            · have hlocal : i.val-880 < 3 := by omega
              have hh := checked_nodes_880 ⟨i.val-880,hlocal⟩
              have heq : 880+(i.val-880)=i.val := by omega
              simpa only [heq] using hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
