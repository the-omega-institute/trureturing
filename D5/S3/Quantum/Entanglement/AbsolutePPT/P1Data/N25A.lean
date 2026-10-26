/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25A
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25A
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25A.accepted
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart00
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart01
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart02
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart03
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart04
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart05
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart06
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart07
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart08
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Checks.N25APart09
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25AWalk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem checked_root : ∀ k, (node nodes (nodes.size-1)).box k = rootBox k := by decide +kernel

theorem accepted : check 25 false nodes=true := by
  apply decide_eq_true
  refine ⟨by decide +kernel, ?_, checked_walk, checked_root⟩
  intro i
  have hi : i.val < 2441 := i.isLt

  by_cases hsplit_1216 : i.val < 1216
  · by_cases hsplit_608 : i.val < 608
    · by_cases hsplit_304 : i.val < 304
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
        · by_cases hsplit_224 : i.val < 224
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
              · by_cases hsplit_208 : i.val < 208
                · have hlocal : i.val-192 < 16 := by omega
                  have hh := checked_nodes_192 ⟨i.val-192,hlocal⟩
                  have heq : 192+(i.val-192)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-208 < 16 := by omega
                  have hh := checked_nodes_208 ⟨i.val-208,hlocal⟩
                  have heq : 208+(i.val-208)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_256 : i.val < 256
            · by_cases hsplit_240 : i.val < 240
              · have hlocal : i.val-224 < 16 := by omega
                have hh := checked_nodes_224 ⟨i.val-224,hlocal⟩
                have heq : 224+(i.val-224)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-240 < 16 := by omega
                have hh := checked_nodes_240 ⟨i.val-240,hlocal⟩
                have heq : 240+(i.val-240)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_272 : i.val < 272
              · have hlocal : i.val-256 < 16 := by omega
                have hh := checked_nodes_256 ⟨i.val-256,hlocal⟩
                have heq : 256+(i.val-256)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_288 : i.val < 288
                · have hlocal : i.val-272 < 16 := by omega
                  have hh := checked_nodes_272 ⟨i.val-272,hlocal⟩
                  have heq : 272+(i.val-272)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-288 < 16 := by omega
                  have hh := checked_nodes_288 ⟨i.val-288,hlocal⟩
                  have heq : 288+(i.val-288)=i.val := by omega
                  simpa only [heq] using hh
      · by_cases hsplit_448 : i.val < 448
        · by_cases hsplit_368 : i.val < 368
          · by_cases hsplit_336 : i.val < 336
            · by_cases hsplit_320 : i.val < 320
              · have hlocal : i.val-304 < 16 := by omega
                have hh := checked_nodes_304 ⟨i.val-304,hlocal⟩
                have heq : 304+(i.val-304)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-320 < 16 := by omega
                have hh := checked_nodes_320 ⟨i.val-320,hlocal⟩
                have heq : 320+(i.val-320)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_352 : i.val < 352
              · have hlocal : i.val-336 < 16 := by omega
                have hh := checked_nodes_336 ⟨i.val-336,hlocal⟩
                have heq : 336+(i.val-336)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-352 < 16 := by omega
                have hh := checked_nodes_352 ⟨i.val-352,hlocal⟩
                have heq : 352+(i.val-352)=i.val := by omega
                simpa only [heq] using hh
          · by_cases hsplit_400 : i.val < 400
            · by_cases hsplit_384 : i.val < 384
              · have hlocal : i.val-368 < 16 := by omega
                have hh := checked_nodes_368 ⟨i.val-368,hlocal⟩
                have heq : 368+(i.val-368)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-384 < 16 := by omega
                have hh := checked_nodes_384 ⟨i.val-384,hlocal⟩
                have heq : 384+(i.val-384)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_416 : i.val < 416
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
        · by_cases hsplit_528 : i.val < 528
          · by_cases hsplit_480 : i.val < 480
            · by_cases hsplit_464 : i.val < 464
              · have hlocal : i.val-448 < 16 := by omega
                have hh := checked_nodes_448 ⟨i.val-448,hlocal⟩
                have heq : 448+(i.val-448)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-464 < 16 := by omega
                have hh := checked_nodes_464 ⟨i.val-464,hlocal⟩
                have heq : 464+(i.val-464)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_496 : i.val < 496
              · have hlocal : i.val-480 < 16 := by omega
                have hh := checked_nodes_480 ⟨i.val-480,hlocal⟩
                have heq : 480+(i.val-480)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_512 : i.val < 512
                · have hlocal : i.val-496 < 16 := by omega
                  have hh := checked_nodes_496 ⟨i.val-496,hlocal⟩
                  have heq : 496+(i.val-496)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-512 < 16 := by omega
                  have hh := checked_nodes_512 ⟨i.val-512,hlocal⟩
                  have heq : 512+(i.val-512)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_560 : i.val < 560
            · by_cases hsplit_544 : i.val < 544
              · have hlocal : i.val-528 < 16 := by omega
                have hh := checked_nodes_528 ⟨i.val-528,hlocal⟩
                have heq : 528+(i.val-528)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-544 < 16 := by omega
                have hh := checked_nodes_544 ⟨i.val-544,hlocal⟩
                have heq : 544+(i.val-544)=i.val := by omega
                simpa only [heq] using hh
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
    · by_cases hsplit_912 : i.val < 912
      · by_cases hsplit_752 : i.val < 752
        · by_cases hsplit_672 : i.val < 672
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
          · by_cases hsplit_704 : i.val < 704
            · by_cases hsplit_688 : i.val < 688
              · have hlocal : i.val-672 < 16 := by omega
                have hh := checked_nodes_672 ⟨i.val-672,hlocal⟩
                have heq : 672+(i.val-672)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-688 < 16 := by omega
                have hh := checked_nodes_688 ⟨i.val-688,hlocal⟩
                have heq : 688+(i.val-688)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_720 : i.val < 720
              · have hlocal : i.val-704 < 16 := by omega
                have hh := checked_nodes_704 ⟨i.val-704,hlocal⟩
                have heq : 704+(i.val-704)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_736 : i.val < 736
                · have hlocal : i.val-720 < 16 := by omega
                  have hh := checked_nodes_720 ⟨i.val-720,hlocal⟩
                  have heq : 720+(i.val-720)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-736 < 16 := by omega
                  have hh := checked_nodes_736 ⟨i.val-736,hlocal⟩
                  have heq : 736+(i.val-736)=i.val := by omega
                  simpa only [heq] using hh
        · by_cases hsplit_832 : i.val < 832
          · by_cases hsplit_784 : i.val < 784
            · by_cases hsplit_768 : i.val < 768
              · have hlocal : i.val-752 < 16 := by omega
                have hh := checked_nodes_752 ⟨i.val-752,hlocal⟩
                have heq : 752+(i.val-752)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-768 < 16 := by omega
                have hh := checked_nodes_768 ⟨i.val-768,hlocal⟩
                have heq : 768+(i.val-768)=i.val := by omega
                simpa only [heq] using hh
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
              · by_cases hsplit_896 : i.val < 896
                · have hlocal : i.val-880 < 16 := by omega
                  have hh := checked_nodes_880 ⟨i.val-880,hlocal⟩
                  have heq : 880+(i.val-880)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-896 < 16 := by omega
                  have hh := checked_nodes_896 ⟨i.val-896,hlocal⟩
                  have heq : 896+(i.val-896)=i.val := by omega
                  simpa only [heq] using hh
      · by_cases hsplit_1056 : i.val < 1056
        · by_cases hsplit_976 : i.val < 976
          · by_cases hsplit_944 : i.val < 944
            · by_cases hsplit_928 : i.val < 928
              · have hlocal : i.val-912 < 16 := by omega
                have hh := checked_nodes_912 ⟨i.val-912,hlocal⟩
                have heq : 912+(i.val-912)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-928 < 16 := by omega
                have hh := checked_nodes_928 ⟨i.val-928,hlocal⟩
                have heq : 928+(i.val-928)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_960 : i.val < 960
              · have hlocal : i.val-944 < 16 := by omega
                have hh := checked_nodes_944 ⟨i.val-944,hlocal⟩
                have heq : 944+(i.val-944)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-960 < 16 := by omega
                have hh := checked_nodes_960 ⟨i.val-960,hlocal⟩
                have heq : 960+(i.val-960)=i.val := by omega
                simpa only [heq] using hh
          · by_cases hsplit_1008 : i.val < 1008
            · by_cases hsplit_992 : i.val < 992
              · have hlocal : i.val-976 < 16 := by omega
                have hh := checked_nodes_976 ⟨i.val-976,hlocal⟩
                have heq : 976+(i.val-976)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-992 < 16 := by omega
                have hh := checked_nodes_992 ⟨i.val-992,hlocal⟩
                have heq : 992+(i.val-992)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1024 : i.val < 1024
              · have hlocal : i.val-1008 < 16 := by omega
                have hh := checked_nodes_1008 ⟨i.val-1008,hlocal⟩
                have heq : 1008+(i.val-1008)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1040 : i.val < 1040
                · have hlocal : i.val-1024 < 16 := by omega
                  have hh := checked_nodes_1024 ⟨i.val-1024,hlocal⟩
                  have heq : 1024+(i.val-1024)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1040 < 16 := by omega
                  have hh := checked_nodes_1040 ⟨i.val-1040,hlocal⟩
                  have heq : 1040+(i.val-1040)=i.val := by omega
                  simpa only [heq] using hh
        · by_cases hsplit_1136 : i.val < 1136
          · by_cases hsplit_1088 : i.val < 1088
            · by_cases hsplit_1072 : i.val < 1072
              · have hlocal : i.val-1056 < 16 := by omega
                have hh := checked_nodes_1056 ⟨i.val-1056,hlocal⟩
                have heq : 1056+(i.val-1056)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1072 < 16 := by omega
                have hh := checked_nodes_1072 ⟨i.val-1072,hlocal⟩
                have heq : 1072+(i.val-1072)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1104 : i.val < 1104
              · have hlocal : i.val-1088 < 16 := by omega
                have hh := checked_nodes_1088 ⟨i.val-1088,hlocal⟩
                have heq : 1088+(i.val-1088)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1120 : i.val < 1120
                · have hlocal : i.val-1104 < 16 := by omega
                  have hh := checked_nodes_1104 ⟨i.val-1104,hlocal⟩
                  have heq : 1104+(i.val-1104)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1120 < 16 := by omega
                  have hh := checked_nodes_1120 ⟨i.val-1120,hlocal⟩
                  have heq : 1120+(i.val-1120)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_1168 : i.val < 1168
            · by_cases hsplit_1152 : i.val < 1152
              · have hlocal : i.val-1136 < 16 := by omega
                have hh := checked_nodes_1136 ⟨i.val-1136,hlocal⟩
                have heq : 1136+(i.val-1136)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1152 < 16 := by omega
                have hh := checked_nodes_1152 ⟨i.val-1152,hlocal⟩
                have heq : 1152+(i.val-1152)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1184 : i.val < 1184
              · have hlocal : i.val-1168 < 16 := by omega
                have hh := checked_nodes_1168 ⟨i.val-1168,hlocal⟩
                have heq : 1168+(i.val-1168)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1200 : i.val < 1200
                · have hlocal : i.val-1184 < 16 := by omega
                  have hh := checked_nodes_1184 ⟨i.val-1184,hlocal⟩
                  have heq : 1184+(i.val-1184)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1200 < 16 := by omega
                  have hh := checked_nodes_1200 ⟨i.val-1200,hlocal⟩
                  have heq : 1200+(i.val-1200)=i.val := by omega
                  simpa only [heq] using hh
  · by_cases hsplit_1824 : i.val < 1824
    · by_cases hsplit_1520 : i.val < 1520
      · by_cases hsplit_1360 : i.val < 1360
        · by_cases hsplit_1280 : i.val < 1280
          · by_cases hsplit_1248 : i.val < 1248
            · by_cases hsplit_1232 : i.val < 1232
              · have hlocal : i.val-1216 < 16 := by omega
                have hh := checked_nodes_1216 ⟨i.val-1216,hlocal⟩
                have heq : 1216+(i.val-1216)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1232 < 16 := by omega
                have hh := checked_nodes_1232 ⟨i.val-1232,hlocal⟩
                have heq : 1232+(i.val-1232)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1264 : i.val < 1264
              · have hlocal : i.val-1248 < 16 := by omega
                have hh := checked_nodes_1248 ⟨i.val-1248,hlocal⟩
                have heq : 1248+(i.val-1248)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1264 < 16 := by omega
                have hh := checked_nodes_1264 ⟨i.val-1264,hlocal⟩
                have heq : 1264+(i.val-1264)=i.val := by omega
                simpa only [heq] using hh
          · by_cases hsplit_1312 : i.val < 1312
            · by_cases hsplit_1296 : i.val < 1296
              · have hlocal : i.val-1280 < 16 := by omega
                have hh := checked_nodes_1280 ⟨i.val-1280,hlocal⟩
                have heq : 1280+(i.val-1280)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1296 < 16 := by omega
                have hh := checked_nodes_1296 ⟨i.val-1296,hlocal⟩
                have heq : 1296+(i.val-1296)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1328 : i.val < 1328
              · have hlocal : i.val-1312 < 16 := by omega
                have hh := checked_nodes_1312 ⟨i.val-1312,hlocal⟩
                have heq : 1312+(i.val-1312)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1344 : i.val < 1344
                · have hlocal : i.val-1328 < 16 := by omega
                  have hh := checked_nodes_1328 ⟨i.val-1328,hlocal⟩
                  have heq : 1328+(i.val-1328)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1344 < 16 := by omega
                  have hh := checked_nodes_1344 ⟨i.val-1344,hlocal⟩
                  have heq : 1344+(i.val-1344)=i.val := by omega
                  simpa only [heq] using hh
        · by_cases hsplit_1440 : i.val < 1440
          · by_cases hsplit_1392 : i.val < 1392
            · by_cases hsplit_1376 : i.val < 1376
              · have hlocal : i.val-1360 < 16 := by omega
                have hh := checked_nodes_1360 ⟨i.val-1360,hlocal⟩
                have heq : 1360+(i.val-1360)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1376 < 16 := by omega
                have hh := checked_nodes_1376 ⟨i.val-1376,hlocal⟩
                have heq : 1376+(i.val-1376)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1408 : i.val < 1408
              · have hlocal : i.val-1392 < 16 := by omega
                have hh := checked_nodes_1392 ⟨i.val-1392,hlocal⟩
                have heq : 1392+(i.val-1392)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1424 : i.val < 1424
                · have hlocal : i.val-1408 < 16 := by omega
                  have hh := checked_nodes_1408 ⟨i.val-1408,hlocal⟩
                  have heq : 1408+(i.val-1408)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1424 < 16 := by omega
                  have hh := checked_nodes_1424 ⟨i.val-1424,hlocal⟩
                  have heq : 1424+(i.val-1424)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_1472 : i.val < 1472
            · by_cases hsplit_1456 : i.val < 1456
              · have hlocal : i.val-1440 < 16 := by omega
                have hh := checked_nodes_1440 ⟨i.val-1440,hlocal⟩
                have heq : 1440+(i.val-1440)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1456 < 16 := by omega
                have hh := checked_nodes_1456 ⟨i.val-1456,hlocal⟩
                have heq : 1456+(i.val-1456)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1488 : i.val < 1488
              · have hlocal : i.val-1472 < 16 := by omega
                have hh := checked_nodes_1472 ⟨i.val-1472,hlocal⟩
                have heq : 1472+(i.val-1472)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1504 : i.val < 1504
                · have hlocal : i.val-1488 < 16 := by omega
                  have hh := checked_nodes_1488 ⟨i.val-1488,hlocal⟩
                  have heq : 1488+(i.val-1488)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1504 < 16 := by omega
                  have hh := checked_nodes_1504 ⟨i.val-1504,hlocal⟩
                  have heq : 1504+(i.val-1504)=i.val := by omega
                  simpa only [heq] using hh
      · by_cases hsplit_1664 : i.val < 1664
        · by_cases hsplit_1584 : i.val < 1584
          · by_cases hsplit_1552 : i.val < 1552
            · by_cases hsplit_1536 : i.val < 1536
              · have hlocal : i.val-1520 < 16 := by omega
                have hh := checked_nodes_1520 ⟨i.val-1520,hlocal⟩
                have heq : 1520+(i.val-1520)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1536 < 16 := by omega
                have hh := checked_nodes_1536 ⟨i.val-1536,hlocal⟩
                have heq : 1536+(i.val-1536)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1568 : i.val < 1568
              · have hlocal : i.val-1552 < 16 := by omega
                have hh := checked_nodes_1552 ⟨i.val-1552,hlocal⟩
                have heq : 1552+(i.val-1552)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1568 < 16 := by omega
                have hh := checked_nodes_1568 ⟨i.val-1568,hlocal⟩
                have heq : 1568+(i.val-1568)=i.val := by omega
                simpa only [heq] using hh
          · by_cases hsplit_1616 : i.val < 1616
            · by_cases hsplit_1600 : i.val < 1600
              · have hlocal : i.val-1584 < 16 := by omega
                have hh := checked_nodes_1584 ⟨i.val-1584,hlocal⟩
                have heq : 1584+(i.val-1584)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1600 < 16 := by omega
                have hh := checked_nodes_1600 ⟨i.val-1600,hlocal⟩
                have heq : 1600+(i.val-1600)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1632 : i.val < 1632
              · have hlocal : i.val-1616 < 16 := by omega
                have hh := checked_nodes_1616 ⟨i.val-1616,hlocal⟩
                have heq : 1616+(i.val-1616)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1648 : i.val < 1648
                · have hlocal : i.val-1632 < 16 := by omega
                  have hh := checked_nodes_1632 ⟨i.val-1632,hlocal⟩
                  have heq : 1632+(i.val-1632)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1648 < 16 := by omega
                  have hh := checked_nodes_1648 ⟨i.val-1648,hlocal⟩
                  have heq : 1648+(i.val-1648)=i.val := by omega
                  simpa only [heq] using hh
        · by_cases hsplit_1744 : i.val < 1744
          · by_cases hsplit_1696 : i.val < 1696
            · by_cases hsplit_1680 : i.val < 1680
              · have hlocal : i.val-1664 < 16 := by omega
                have hh := checked_nodes_1664 ⟨i.val-1664,hlocal⟩
                have heq : 1664+(i.val-1664)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1680 < 16 := by omega
                have hh := checked_nodes_1680 ⟨i.val-1680,hlocal⟩
                have heq : 1680+(i.val-1680)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1712 : i.val < 1712
              · have hlocal : i.val-1696 < 16 := by omega
                have hh := checked_nodes_1696 ⟨i.val-1696,hlocal⟩
                have heq : 1696+(i.val-1696)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1728 : i.val < 1728
                · have hlocal : i.val-1712 < 16 := by omega
                  have hh := checked_nodes_1712 ⟨i.val-1712,hlocal⟩
                  have heq : 1712+(i.val-1712)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1728 < 16 := by omega
                  have hh := checked_nodes_1728 ⟨i.val-1728,hlocal⟩
                  have heq : 1728+(i.val-1728)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_1776 : i.val < 1776
            · by_cases hsplit_1760 : i.val < 1760
              · have hlocal : i.val-1744 < 16 := by omega
                have hh := checked_nodes_1744 ⟨i.val-1744,hlocal⟩
                have heq : 1744+(i.val-1744)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1760 < 16 := by omega
                have hh := checked_nodes_1760 ⟨i.val-1760,hlocal⟩
                have heq : 1760+(i.val-1760)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1792 : i.val < 1792
              · have hlocal : i.val-1776 < 16 := by omega
                have hh := checked_nodes_1776 ⟨i.val-1776,hlocal⟩
                have heq : 1776+(i.val-1776)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1808 : i.val < 1808
                · have hlocal : i.val-1792 < 16 := by omega
                  have hh := checked_nodes_1792 ⟨i.val-1792,hlocal⟩
                  have heq : 1792+(i.val-1792)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1808 < 16 := by omega
                  have hh := checked_nodes_1808 ⟨i.val-1808,hlocal⟩
                  have heq : 1808+(i.val-1808)=i.val := by omega
                  simpa only [heq] using hh
    · by_cases hsplit_2128 : i.val < 2128
      · by_cases hsplit_1968 : i.val < 1968
        · by_cases hsplit_1888 : i.val < 1888
          · by_cases hsplit_1856 : i.val < 1856
            · by_cases hsplit_1840 : i.val < 1840
              · have hlocal : i.val-1824 < 16 := by omega
                have hh := checked_nodes_1824 ⟨i.val-1824,hlocal⟩
                have heq : 1824+(i.val-1824)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1840 < 16 := by omega
                have hh := checked_nodes_1840 ⟨i.val-1840,hlocal⟩
                have heq : 1840+(i.val-1840)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1872 : i.val < 1872
              · have hlocal : i.val-1856 < 16 := by omega
                have hh := checked_nodes_1856 ⟨i.val-1856,hlocal⟩
                have heq : 1856+(i.val-1856)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1872 < 16 := by omega
                have hh := checked_nodes_1872 ⟨i.val-1872,hlocal⟩
                have heq : 1872+(i.val-1872)=i.val := by omega
                simpa only [heq] using hh
          · by_cases hsplit_1920 : i.val < 1920
            · by_cases hsplit_1904 : i.val < 1904
              · have hlocal : i.val-1888 < 16 := by omega
                have hh := checked_nodes_1888 ⟨i.val-1888,hlocal⟩
                have heq : 1888+(i.val-1888)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1904 < 16 := by omega
                have hh := checked_nodes_1904 ⟨i.val-1904,hlocal⟩
                have heq : 1904+(i.val-1904)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_1936 : i.val < 1936
              · have hlocal : i.val-1920 < 16 := by omega
                have hh := checked_nodes_1920 ⟨i.val-1920,hlocal⟩
                have heq : 1920+(i.val-1920)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_1952 : i.val < 1952
                · have hlocal : i.val-1936 < 16 := by omega
                  have hh := checked_nodes_1936 ⟨i.val-1936,hlocal⟩
                  have heq : 1936+(i.val-1936)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-1952 < 16 := by omega
                  have hh := checked_nodes_1952 ⟨i.val-1952,hlocal⟩
                  have heq : 1952+(i.val-1952)=i.val := by omega
                  simpa only [heq] using hh
        · by_cases hsplit_2048 : i.val < 2048
          · by_cases hsplit_2000 : i.val < 2000
            · by_cases hsplit_1984 : i.val < 1984
              · have hlocal : i.val-1968 < 16 := by omega
                have hh := checked_nodes_1968 ⟨i.val-1968,hlocal⟩
                have heq : 1968+(i.val-1968)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-1984 < 16 := by omega
                have hh := checked_nodes_1984 ⟨i.val-1984,hlocal⟩
                have heq : 1984+(i.val-1984)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_2016 : i.val < 2016
              · have hlocal : i.val-2000 < 16 := by omega
                have hh := checked_nodes_2000 ⟨i.val-2000,hlocal⟩
                have heq : 2000+(i.val-2000)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_2032 : i.val < 2032
                · have hlocal : i.val-2016 < 16 := by omega
                  have hh := checked_nodes_2016 ⟨i.val-2016,hlocal⟩
                  have heq : 2016+(i.val-2016)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-2032 < 16 := by omega
                  have hh := checked_nodes_2032 ⟨i.val-2032,hlocal⟩
                  have heq : 2032+(i.val-2032)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_2080 : i.val < 2080
            · by_cases hsplit_2064 : i.val < 2064
              · have hlocal : i.val-2048 < 16 := by omega
                have hh := checked_nodes_2048 ⟨i.val-2048,hlocal⟩
                have heq : 2048+(i.val-2048)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-2064 < 16 := by omega
                have hh := checked_nodes_2064 ⟨i.val-2064,hlocal⟩
                have heq : 2064+(i.val-2064)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_2096 : i.val < 2096
              · have hlocal : i.val-2080 < 16 := by omega
                have hh := checked_nodes_2080 ⟨i.val-2080,hlocal⟩
                have heq : 2080+(i.val-2080)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_2112 : i.val < 2112
                · have hlocal : i.val-2096 < 16 := by omega
                  have hh := checked_nodes_2096 ⟨i.val-2096,hlocal⟩
                  have heq : 2096+(i.val-2096)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-2112 < 16 := by omega
                  have hh := checked_nodes_2112 ⟨i.val-2112,hlocal⟩
                  have heq : 2112+(i.val-2112)=i.val := by omega
                  simpa only [heq] using hh
      · by_cases hsplit_2288 : i.val < 2288
        · by_cases hsplit_2208 : i.val < 2208
          · by_cases hsplit_2160 : i.val < 2160
            · by_cases hsplit_2144 : i.val < 2144
              · have hlocal : i.val-2128 < 16 := by omega
                have hh := checked_nodes_2128 ⟨i.val-2128,hlocal⟩
                have heq : 2128+(i.val-2128)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-2144 < 16 := by omega
                have hh := checked_nodes_2144 ⟨i.val-2144,hlocal⟩
                have heq : 2144+(i.val-2144)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_2176 : i.val < 2176
              · have hlocal : i.val-2160 < 16 := by omega
                have hh := checked_nodes_2160 ⟨i.val-2160,hlocal⟩
                have heq : 2160+(i.val-2160)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_2192 : i.val < 2192
                · have hlocal : i.val-2176 < 16 := by omega
                  have hh := checked_nodes_2176 ⟨i.val-2176,hlocal⟩
                  have heq : 2176+(i.val-2176)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-2192 < 16 := by omega
                  have hh := checked_nodes_2192 ⟨i.val-2192,hlocal⟩
                  have heq : 2192+(i.val-2192)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_2240 : i.val < 2240
            · by_cases hsplit_2224 : i.val < 2224
              · have hlocal : i.val-2208 < 16 := by omega
                have hh := checked_nodes_2208 ⟨i.val-2208,hlocal⟩
                have heq : 2208+(i.val-2208)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-2224 < 16 := by omega
                have hh := checked_nodes_2224 ⟨i.val-2224,hlocal⟩
                have heq : 2224+(i.val-2224)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_2256 : i.val < 2256
              · have hlocal : i.val-2240 < 16 := by omega
                have hh := checked_nodes_2240 ⟨i.val-2240,hlocal⟩
                have heq : 2240+(i.val-2240)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_2272 : i.val < 2272
                · have hlocal : i.val-2256 < 16 := by omega
                  have hh := checked_nodes_2256 ⟨i.val-2256,hlocal⟩
                  have heq : 2256+(i.val-2256)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-2272 < 16 := by omega
                  have hh := checked_nodes_2272 ⟨i.val-2272,hlocal⟩
                  have heq : 2272+(i.val-2272)=i.val := by omega
                  simpa only [heq] using hh
        · by_cases hsplit_2368 : i.val < 2368
          · by_cases hsplit_2320 : i.val < 2320
            · by_cases hsplit_2304 : i.val < 2304
              · have hlocal : i.val-2288 < 16 := by omega
                have hh := checked_nodes_2288 ⟨i.val-2288,hlocal⟩
                have heq : 2288+(i.val-2288)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-2304 < 16 := by omega
                have hh := checked_nodes_2304 ⟨i.val-2304,hlocal⟩
                have heq : 2304+(i.val-2304)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_2336 : i.val < 2336
              · have hlocal : i.val-2320 < 16 := by omega
                have hh := checked_nodes_2320 ⟨i.val-2320,hlocal⟩
                have heq : 2320+(i.val-2320)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_2352 : i.val < 2352
                · have hlocal : i.val-2336 < 16 := by omega
                  have hh := checked_nodes_2336 ⟨i.val-2336,hlocal⟩
                  have heq : 2336+(i.val-2336)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-2352 < 16 := by omega
                  have hh := checked_nodes_2352 ⟨i.val-2352,hlocal⟩
                  have heq : 2352+(i.val-2352)=i.val := by omega
                  simpa only [heq] using hh
          · by_cases hsplit_2400 : i.val < 2400
            · by_cases hsplit_2384 : i.val < 2384
              · have hlocal : i.val-2368 < 16 := by omega
                have hh := checked_nodes_2368 ⟨i.val-2368,hlocal⟩
                have heq : 2368+(i.val-2368)=i.val := by omega
                simpa only [heq] using hh
              · have hlocal : i.val-2384 < 16 := by omega
                have hh := checked_nodes_2384 ⟨i.val-2384,hlocal⟩
                have heq : 2384+(i.val-2384)=i.val := by omega
                simpa only [heq] using hh
            · by_cases hsplit_2416 : i.val < 2416
              · have hlocal : i.val-2400 < 16 := by omega
                have hh := checked_nodes_2400 ⟨i.val-2400,hlocal⟩
                have heq : 2400+(i.val-2400)=i.val := by omega
                simpa only [heq] using hh
              · by_cases hsplit_2432 : i.val < 2432
                · have hlocal : i.val-2416 < 16 := by omega
                  have hh := checked_nodes_2416 ⟨i.val-2416,hlocal⟩
                  have heq : 2416+(i.val-2416)=i.val := by omega
                  simpa only [heq] using hh
                · have hlocal : i.val-2432 < 9 := by omega
                  have hh := checked_nodes_2432 ⟨i.val-2432,hlocal⟩
                  have heq : 2432+(i.val-2432)=i.val := by omega
                  simpa only [heq] using hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
