/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowALast
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twelve exact positive Horner gate proofs for a_eq_2s_plus1. -/
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

-- Complete shifted coefficient map: a_eq_2s_plus1; grouped by exact Horner identities.
-- Python supplies source literals only. Lean ring and positivity prove each gate.
set_option maxHeartbeats 8000000 in
private theorem a_eq_2s_plus1_gates (u v w : ℤ) (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (chartPowers 7 u v w 0) (chartPowers 7 u v w 1)
        (chartPowers 7 u v w 2) (chartMasks 7 u v w) r slot := by
  obtain ⟨U,hU,rfl⟩ : ∃ U : ℤ, 0≤U ∧ u=U+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨V,hV,rfl⟩ : ∃ V : ℤ, 0≤V ∧ v=V+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨W,hW,rfl⟩ : ∃ W : ℤ, 0≤W ∧ w=W+1 := ⟨w-1,by omega,by ring⟩
  intro r slot
  fin_cases r <;> fin_cases slot
  · -- a_eq_2s_plus1/2S1: 12 positive coefficient leaves.
    calc
      0 ≤ (1632 + V*(2630) + U*(6938 + V*(10846) + U*(12056 + V*(17912) + U*(10848 + V*(14816) + U*(5120
        + V*(6144) + U*(1024 + V*(1024))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 0 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/old_cap_1: 12 positive coefficient leaves.
    calc
      0 ≤ (1056 + V*(58) + U*(5734 + V*(1826) + U*(11880 + V*(6024) + U*(11808 + V*(7840) + U*(5632 +
        V*(4608) + U*(1024 + V*(1024))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 0 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/2T1: 12 positive coefficient leaves.
    calc
      0 ≤ (2402 + V*(4390) + U*(10878 + V*(18686) + U*(20184 + V*(31896) + U*(19392 + V*(27328) +
        U*(9728 + V*(11776) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 0 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/new_cap_1: 12 positive coefficient leaves.
    calc
      0 ≤ (2334 + V*(346) + U*(12034 + V*(4226) + U*(24232 + V*(12520) + U*(23744 + V*(15808) + U*(11264
        + V*(9216) + U*(2048 + V*(2048))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 0 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/2S2: 14 positive coefficient leaves.
    calc
      0 ≤ (11376 + V*(11968) + U*(72036 + V*(74240) + U*(190832 + V*(193984) + U*(270464 + V*(272512) +
        U*(216064 + V*(216576) + U*(92160 + V*(92160) + U*(16384 + V*(16384)))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 1 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/old_cap_2: 12 positive coefficient leaves.
    calc
      0 ≤ (5140 + V*(4416) + U*(26656 + V*(24064) + U*(55312 + V*(51776) + U*(57344 + V*(55168) +
        U*(29696 + V*(29184) + U*(6144 + V*(6144))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 1 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/2T2: 14 positive coefficient leaves.
    calc
      0 ≤ (17950 + V*(19136) + U*(121028 + V*(125440) + U*(337184 + V*(343488) + U*(497792 + V*(501888)
        + U*(411136 + V*(412160) + U*(180224 + V*(180224) + U*(32768 + V*(32768)))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 1 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/new_cap_2: 12 positive coefficient leaves.
    calc
      0 ≤ (15082 + V*(13632) + U*(76356 + V*(71168) + U*(155104 + V*(148032) + U*(157824 + V*(153472) +
        U*(80384 + V*(79360) + U*(16384 + V*(16384))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 1 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/2S3: 10 positive coefficient leaves.
    calc
      0 ≤ (466 + V*(1024) + U*(1956 + V*(4096) + U*(3024 + V*(6144) + U*(2048 + V*(4096) + U*(512 +
        V*(1024)))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 2 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/old_cap_3: 14 positive coefficient leaves.
    calc
      0 ≤ (20046 + V*(19456) + U*(116892 + V*(114688) + U*(283728 + V*(280576) + U*(366592 + V*(364544)
        + U*(265728 + V*(265216) + U*(102400 + V*(102400) + U*(16384 + V*(16384)))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 2 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/2T3: 14 positive coefficient leaves.
    calc
      0 ≤ (16322 + V*(17408) + U*(98180 + V*(102400) + U*(245696 + V*(251904) + U*(327680 + V*(331776) +
        U*(245760 + V*(246784) + U*(98304 + V*(98304) + U*(16384 + V*(16384)))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 2 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_eq_2s_plus1/new_cap_3: 12 positive coefficient leaves.
    calc
      0 ≤ (4190 + V*(3072) + U*(20668 + V*(16384) + U*(41056 + V*(34816) + U*(40960 + V*(36864) +
        U*(20480 + V*(19456) + U*(4096 + V*(4096))))))) := by positivity
      _ = gate (chartPowers 7 (U+1) (V+1) (W+1) 0)
          (chartPowers 7 (U+1) (V+1) (W+1) 1)
          (chartPowers 7 (U+1) (V+1) (W+1) 2)
          (chartMasks 7 (U+1) (V+1) (W+1)) 2 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
