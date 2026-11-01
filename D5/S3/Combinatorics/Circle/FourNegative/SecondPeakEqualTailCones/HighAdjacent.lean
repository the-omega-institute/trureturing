/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/HighAdjacent
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twelve exact positive Horner gate proofs for high_a_adjacent. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Dyadic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private heads newHeads successor newSuccessor sourceN delta
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private allocation dot doubledSeams gate
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams
open private chartPowers chartEpsilon chartDelta chartMasks
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Dyadic

-- Complete shifted coefficient map: high_a_adjacent; grouped by exact Horner identities.
-- Python supplies source literals only. Lean ring and positivity prove each gate.
set_option maxHeartbeats 8000000 in
private theorem high_a_adjacent_gates (u v w : ℤ) (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (chartPowers 0 u v w 0) (chartPowers 0 u v w 1)
        (chartPowers 0 u v w 2) (chartMasks 0 u v w) r slot := by
  obtain ⟨U,hU,rfl⟩ : ∃ U : ℤ, 0≤U ∧ u=U+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨V,hV,rfl⟩ : ∃ V : ℤ, 0≤V ∧ v=V+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨W,hW,rfl⟩ : ∃ W : ℤ, 0≤W ∧ w=W+1 := ⟨w-1,by omega,by ring⟩
  intro r slot
  fin_cases r <;> fin_cases slot
  · -- high_a_adjacent/2S1: 10 positive coefficient leaves.
    calc
      0 ≤ (1738 + V*(1776) + U*(6412 + V*(6480) + U*(8896 + V*(8928) + U*(5504 + V*(5504) + U*(1280 +
        V*(1280)))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 0 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/old_cap_1: 12 positive coefficient leaves.
    calc
      0 ≤ (950 + V*(912) + U*(6260 + V*(6192) + U*(15040 + V*(15008) + U*(17152 + V*(17152) + U*(9472 +
        V*(9472) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 0 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/2T1: 10 positive coefficient leaves.
    calc
      0 ≤ (2604 + V*(2672) + U*(9808 + V*(9936) + U*(13856 + V*(13920) + U*(8704 + V*(8704) + U*(2048 +
        V*(2048)))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 0 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/new_cap_1: 12 positive coefficient leaves.
    calc
      0 ≤ (2132 + V*(2064) + U*(13104 + V*(12976) + U*(30560 + V*(30496) + U*(34432 + V*(34432) +
        U*(18944 + V*(18944) + U*(4096 + V*(4096))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 0 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/2S2: 24 positive coefficient leaves.
    calc
      0 ≤ (24120 + V*(50768 + V*(26624)) + U*(177276 + V*(367776 + V*(190464)) + U*(558144 + V*(1143888
        + V*(585728)) + U*(974848 + V*(1978368 + V*(1003520)) + U*(1019392 + V*(2053632 + V*(1034240)) +
        U*(637952 + V*(1278976 + V*(641024)) + U*(221184 + V*(442368 + V*(221184)) + U*(32768 + V*(65536
        + V*(32768)))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 1 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/old_cap_2: 21 positive coefficient leaves.
    calc
      0 ≤ (8908 + V*(15024 + V*(6144)) + U*(53128 + V*(92000 + V*(38912)) + U*(131520 + V*(233904 +
        V*(102400)) + U*(173056 + V*(316416 + V*(143360)) + U*(127744 + V*(240384 + V*(112640)) +
        U*(50176 + V*(97280 + V*(47104)) + U*(8192 + V*(16384 + V*(8192))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 1 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/2T2: 24 positive coefficient leaves.
    calc
      0 ≤ (38310 + V*(81360 + V*(43008)) + U*(296668 + V*(618272 + V*(321536)) + U*(975536 + V*(2003664
        + V*(1028096)) + U*(1767296 + V*(3590016 + V*(1822720)) + U*(1906176 + V*(3841536 + V*(1935360))
        + U*(1224704 + V*(2455552 + V*(1230848)) + U*(434176 + V*(868352 + V*(434176)) + U*(65536 +
        V*(131072 + V*(65536)))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 1 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/new_cap_2: 21 positive coefficient leaves.
    calc
      0 ≤ (27746 + V*(50224 + V*(22528)) + U*(164140 + V*(301280 + V*(137216)) + U*(403792 + V*(751920 +
        V*(348160)) + U*(528512 + V*(999552 + V*(471040)) + U*(388096 + V*(746496 + V*(358400)) +
        U*(151552 + V*(296960 + V*(145408)) + U*(24576 + V*(49152 + V*(24576))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 1 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/2S3: 18 positive coefficient leaves.
    calc
      0 ≤ (954 + V*(3024 + V*(2048)) + U*(4924 + V*(15200 + V*(10240)) + U*(10048 + V*(30544 +
        V*(20480)) + U*(10176 + V*(30656 + V*(20480)) + U*(5120 + V*(15360 + V*(10240)) + U*(1024 +
        V*(3072 + V*(2048)))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 2 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/old_cap_3: 24 positive coefficient leaves.
    calc
      0 ≤ (40070 + V*(78960 + V*(38912)) + U*(273796 + V*(542048 + V*(268288)) + U*(801152 + V*(1591664
        + V*(790528)) + U*(1300608 + V*(2590848 + V*(1290240)) + U*(1264640 + V*(2524160 + V*(1259520))
        + U*(736256 + V*(1471488 + V*(735232)) + U*(237568 + V*(475136 + V*(237568)) + U*(32768 +
        V*(65536 + V*(32768)))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 2 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/2T3: 24 positive coefficient leaves.
    calc
      0 ≤ (32682 + V*(67536 + V*(34816)) + U*(229148 + V*(468832 + V*(239616)) + U*(687920 + V*(1396560
        + V*(708608)) + U*(1146816 + V*(2314176 + V*(1167360)) + U*(1146880 + V*(2304000 + V*(1157120))
        + U*(688128 + V*(1378304 + V*(690176)) + U*(229376 + V*(458752 + V*(229376)) + U*(32768 +
        V*(65536 + V*(32768)))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 2 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_adjacent/new_cap_3: 21 positive coefficient leaves.
    calc
      0 ≤ (8342 + V*(14448 + V*(6144)) + U*(49572 + V*(88416 + V*(38912)) + U*(123280 + V*(225648 +
        V*(102400)) + U*(163968 + V*(307328 + V*(143360)) + U*(122880 + V*(235520 + V*(112640)) +
        U*(49152 + V*(96256 + V*(47104)) + U*(8192 + V*(16384 + V*(8192))))))))) := by positivity
      _ = gate (chartPowers 0 (U+1) (V+1) (W+1) 0)
          (chartPowers 0 (U+1) (V+1) (W+1) 1)
          (chartPowers 0 (U+1) (V+1) (W+1) 2)
          (chartMasks 0 (U+1) (V+1) (W+1)) 2 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
