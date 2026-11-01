/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowAFirst
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twelve exact positive Horner gate proofs for a_eq_s_plus1. -/
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

-- Complete shifted coefficient map: a_eq_s_plus1; grouped by exact Horner identities.
-- Python supplies source literals only. Lean ring and positivity prove each gate.
set_option maxHeartbeats 8000000 in
private theorem a_eq_s_plus1_gates (u v w : ℤ) (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (chartPowers 5 u v w 0) (chartPowers 5 u v w 1)
        (chartPowers 5 u v w 2) (chartMasks 5 u v w) r slot := by
  obtain ⟨U,hU,rfl⟩ : ∃ U : ℤ, 0≤U ∧ u=U+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨V,hV,rfl⟩ : ∃ V : ℤ, 0≤V ∧ v=V+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨W,hW,rfl⟩ : ∃ W : ℤ, 0≤W ∧ w=W+1 := ⟨w-1,by omega,by ring⟩
  intro r slot
  fin_cases r <;> fin_cases slot
  · -- a_eq_s_plus1/2S1: 12 positive coefficient leaves.
    calc
      0 ≤ (2226 + V*(2504) + U*(9548 + V*(10336) + U*(16376 + V*(17144) + U*(14048 + V*(14304) + U*(6016
        + V*(6016) + U*(1024 + V*(1024))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 0 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/old_cap_1: 12 positive coefficient leaves.
    calc
      0 ≤ (462 + V*(184) + U*(3124 + V*(2336) + U*(7560 + V*(6792) + U*(8608 + V*(8352) + U*(4736 +
        V*(4736) + U*(1024 + V*(1024))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 0 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/2T1: 12 positive coefficient leaves.
    calc
      0 ≤ (3620 + V*(4168) + U*(16192 + V*(17760) + U*(28920 + V*(30456) + U*(25824 + V*(26336) +
        U*(11520 + V*(11520) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 0 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/new_cap_1: 12 positive coefficient leaves.
    calc
      0 ≤ (1116 + V*(568) + U*(6720 + V*(5152) + U*(15496 + V*(13960) + U*(17312 + V*(16800) + U*(9472 +
        V*(9472) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 0 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/2S2: 12 positive coefficient leaves.
    calc
      0 ≤ (1818 + V*(1984) + U*(9036 + V*(9472) + U*(18224 + V*(18624) + U*(18688 + V*(18816) + U*(9728
        + V*(9728) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 1 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/old_cap_2: 12 positive coefficient leaves.
    calc
      0 ≤ (2314 + V*(2112) + U*(11512 + V*(11008) + U*(22768 + V*(22336) + U*(22272 + V*(22144) +
        U*(10752 + V*(10752) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 1 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/2T2: 12 positive coefficient leaves.
    calc
      0 ≤ (2680 + V*(3008) + U*(14748 + V*(15616) + U*(32160 + V*(32960) + U*(34944 + V*(35200) +
        U*(18944 + V*(18944) + U*(4096 + V*(4096))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 1 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/new_cap_2: 12 positive coefficient leaves.
    calc
      0 ≤ (5584 + V*(5184) + U*(26348 + V*(25344) + U*(49824 + V*(48960) + U*(46976 + V*(46720) +
        U*(22016 + V*(22016) + U*(4096 + V*(4096))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 1 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/2S3: 8 positive coefficient leaves.
    calc
      0 ≤ (100 + V*(256) + U*(340 + V*(768) + U*(368 + V*(768) + U*(128 + V*(256))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 2 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/old_cap_3: 12 positive coefficient leaves.
    calc
      0 ≤ (5028 + V*(4864) + U*(24244 + V*(23808) + U*(46736 + V*(46336) + U*(44928 + V*(44800) +
        U*(21504 + V*(21504) + U*(4096 + V*(4096))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 2 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/2T3: 12 positive coefficient leaves.
    calc
      0 ≤ (4052 + V*(4352) + U*(20404 + V*(21248) + U*(40928 + V*(41728) + U*(40960 + V*(41216) +
        U*(20480 + V*(20480) + U*(4096 + V*(4096))))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 2 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_s_plus1/new_cap_3: 10 positive coefficient leaves.
    calc
      0 ≤ (1076 + V*(768) + U*(4180 + V*(3328) + U*(6176 + V*(5376) + U*(4096 + V*(3840) + U*(1024 +
        V*(1024)))))) := by positivity
      _ = gate (chartPowers 5 (U+1) (V+1) (W+1) 0)
          (chartPowers 5 (U+1) (V+1) (W+1) 1)
          (chartPowers 5 (U+1) (V+1) (W+1) 2)
          (chartMasks 5 (U+1) (V+1) (W+1)) 2 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
