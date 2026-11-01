/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/HighSeparated
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twelve exact positive Horner gate proofs for high_a_separated. -/
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

-- Complete shifted coefficient map: high_a_separated; grouped by exact Horner identities.
-- Python supplies source literals only. Lean ring and positivity prove each gate.
set_option maxHeartbeats 8000000 in
private theorem high_a_separated_gates (u v w : ℤ) (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (chartPowers 1 u v w 0) (chartPowers 1 u v w 1)
        (chartPowers 1 u v w 2) (chartMasks 1 u v w) r slot := by
  obtain ⟨U,hU,rfl⟩ : ∃ U : ℤ, 0≤U ∧ u=U+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨V,hV,rfl⟩ : ∃ V : ℤ, 0≤V ∧ v=V+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨W,hW,rfl⟩ : ∃ W : ℤ, 0≤W ∧ w=W+1 := ⟨w-1,by omega,by ring⟩
  intro r slot
  fin_cases r <;> fin_cases slot
  · -- high_a_separated/2S1: 22 positive coefficient leaves.
    calc
      0 ≤ (3344 + U*(12180 + U*(16640 + U*(10112 + U*(2304)))) + W*(5302 + U*(21848 + U*(36000 +
        U*(29696 + U*(12288 + U*(2048)))))) + V*(3424 + U*(12320 + U*(16704 + U*(10112 + U*(2304)))) +
        W*(5344 + U*(21920 + U*(36032 + U*(29696 + U*(12288 + U*(2048)))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 0 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/old_cap_1: 24 positive coefficient leaves.
    calc
      0 ≤ (2032 + W*(74) + V*(1952 + W*(32)) + U*(13164 + W*(3496) + V*(13024 + W*(3424)) + U*(31232 +
        W*(11872) + V*(31168 + W*(11840)) + U*(35200 + W*(15616) + V*(35200 + W*(15616)) + U*(19200 +
        W*(9216) + V*(19200 + W*(9216)) + U*(4096 + W*(2048) + V*(4096 + W*(2048)))))))) := by
        positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 0 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/2T1: 22 positive coefficient leaves.
    calc
      0 ≤ (4946 + U*(18328 + U*(25408 + U*(15616 + U*(3584)))) + W*(8854 + U*(37656 + U*(64128 +
        U*(54784 + U*(23552 + U*(4096)))))) + V*(5088 + U*(18592 + U*(25536 + U*(15616 + U*(3584)))) +
        W*(8928 + U*(37792 + U*(64192 + U*(54784 + U*(23552 + U*(4096)))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 0 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/new_cap_1: 24 positive coefficient leaves.
    calc
      0 ≤ (4526 + W*(618) + V*(4384 + W*(544)) + U*(27496 + W*(8168) + V*(27232 + W*(8032)) + U*(63424 +
        W*(24704) + V*(63296 + W*(24640)) + U*(70656 + W*(31488) + V*(70656 + W*(31488)) + U*(38400 +
        W*(18432) + V*(38400 + W*(18432)) + U*(8192 + W*(4096) + V*(8192 + W*(4096)))))))) := by
        positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 0 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/2S2: 48 positive coefficient leaves.
    calc
      0 ≤ (49400 + W*(50560) + V*(102672 + W*(103808) + V*(53248 + W*(53248))) + U*(360060 + W*(365568)
        + V*(741024 + W*(746496) + V*(380928 + W*(380928))) + U*(1126912 + W*(1137536) + V*(2298384 +
        W*(2308992) + V*(1171456 + W*(1171456))) + U*(1960064 + W*(1970432) + V*(3967104 + W*(3977472) +
        V*(2007040 + W*(2007040))) + U*(2043904 + W*(2049024) + V*(4112384 + W*(4117504) + V*(2068480 +
        W*(2068480))) + U*(1276928 + W*(1277952) + V*(2558976 + W*(2560000) + V*(1282048 + W*(1282048)))
        + U*(442368 + W*(442368) + V*(884736 + W*(884736) + V*(442368 + W*(442368))) + U*(65536 +
        W*(65536) + V*(131072 + W*(131072) + V*(65536 + W*(65536))))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 1 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/old_cap_2: 42 positive coefficient leaves.
    calc
      0 ≤ (16396 + W*(14976) + V*(28656 + W*(27264) + V*(12288 + W*(12288))) + U*(99720 + W*(93184) +
        V*(177504 + W*(171008) + V*(77824 + W*(77824))) + U*(250880 + W*(238720) + V*(455664 +
        W*(443520) + V*(204800 + W*(204800))) + U*(334720 + W*(323328) + V*(621440 + W*(610048) +
        V*(286720 + W*(286720))) + U*(250112 + W*(244736) + V*(475392 + W*(470016) + V*(225280 +
        W*(225280))) + U*(99328 + W*(98304) + V*(193536 + W*(192512) + V*(94208 + W*(94208))) + U*(16384
        + W*(16384) + V*(32768 + W*(32768) + V*(16384 + W*(16384)))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 1 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/2T2: 48 positive coefficient leaves.
    calc
      0 ≤ (78950 + W*(81280) + V*(165008 + W*(167296) + V*(86016 + W*(86016))) + U*(604380 + W*(615424)
        + V*(1247520 + W*(1258496) + V*(643072 + W*(643072))) + U*(1972336 + W*(1993600) + V*(4028560 +
        W*(4049792) + V*(2056192 + W*(2056192))) + U*(3555328 + W*(3576064) + V*(7200768 + W*(7221504) +
        V*(3645440 + W*(3645440))) + U*(3822592 + W*(3832832) + V*(7693312 + W*(7703552) + V*(3870720 +
        W*(3870720))) + U*(2451456 + W*(2453504) + V*(4913152 + W*(4915200) + V*(2461696 + W*(2461696)))
        + U*(868352 + W*(868352) + V*(1736704 + W*(1736704) + V*(868352 + W*(868352))) + U*(131072 +
        W*(131072) + V*(262144 + W*(262144) + V*(131072 + W*(131072))))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 1 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/new_cap_2: 42 positive coefficient leaves.
    calc
      0 ≤ (52642 + W*(49792) + V*(97648 + W*(94848) + V*(45056 + W*(45056))) + U*(315180 + W*(302080) +
        V*(589536 + W*(576512) + V*(274432 + W*(274432))) + U*(783248 + W*(758912) + V*(1479536 +
        W*(1455232) + V*(696320 + W*(696320))) + U*(1034240 + W*(1011456) + V*(1976320 + W*(1953536) +
        V*(942080 + W*(942080))) + U*(765440 + W*(754688) + V*(1482240 + W*(1471488) + V*(716800 +
        W*(716800))) + U*(301056 + W*(299008) + V*(591872 + W*(589824) + V*(290816 + W*(290816))) +
        U*(49152 + W*(49152) + V*(98304 + W*(98304) + V*(49152 + W*(49152)))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 1 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/2S3: 36 positive coefficient leaves.
    calc
      0 ≤ (3002 + W*(4096) + V*(7120 + W*(8192) + V*(4096 + W*(4096))) + U*(15164 + W*(20480) + V*(35680
        + W*(40960) + V*(20480 + W*(20480))) + U*(30528 + W*(40960) + V*(71504 + W*(81920) + V*(40960 +
        W*(40960))) + U*(30656 + W*(40960) + V*(71616 + W*(81920) + V*(40960 + W*(40960))) + U*(15360 +
        W*(20480) + V*(35840 + W*(40960) + V*(20480 + W*(20480))) + U*(3072 + W*(4096) + V*(7168 +
        W*(8192) + V*(4096 + W*(4096))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 2 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/old_cap_3: 48 positive coefficient leaves.
    calc
      0 ≤ (78982 + W*(77824) + V*(156784 + W*(155648) + V*(77824 + W*(77824))) + U*(542084 + W*(536576)
        + V*(1078624 + W*(1073152) + V*(536576 + W*(536576))) + U*(1591680 + W*(1581056) + V*(3172720 +
        W*(3162112) + V*(1581056 + W*(1581056))) + U*(2590848 + W*(2580480) + V*(5171328 + W*(5160960) +
        V*(2580480 + W*(2580480))) + U*(2524160 + W*(2519040) + V*(5043200 + W*(5038080) + V*(2519040 +
        W*(2519040))) + U*(1471488 + W*(1470464) + V*(2941952 + W*(2940928) + V*(1470464 + W*(1470464)))
        + U*(475136 + W*(475136) + V*(950272 + W*(950272) + V*(475136 + W*(475136))) + U*(65536 +
        W*(65536) + V*(131072 + W*(131072) + V*(65536 + W*(65536))))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 2 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/2T3: 48 positive coefficient leaves.
    calc
      0 ≤ (67498 + W*(69632) + V*(137168 + W*(139264) + V*(69632 + W*(69632))) + U*(468764 + W*(479232)
        + V*(948064 + W*(958464) + V*(479232 + W*(479232))) + U*(1396528 + W*(1417216) + V*(2813776 +
        W*(2834432) + V*(1417216 + W*(1417216))) + U*(2314176 + W*(2334720) + V*(4648896 + W*(4669440) +
        V*(2334720 + W*(2334720))) + U*(2304000 + W*(2314240) + V*(4618240 + W*(4628480) + V*(2314240 +
        W*(2314240))) + U*(1378304 + W*(1380352) + V*(2758656 + W*(2760704) + V*(1380352 + W*(1380352)))
        + U*(458752 + W*(458752) + V*(917504 + W*(917504) + V*(458752 + W*(458752))) + U*(65536 +
        W*(65536) + V*(131072 + W*(131072) + V*(65536 + W*(65536))))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 2 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- high_a_separated/new_cap_3: 42 positive coefficient leaves.
    calc
      0 ≤ (14486 + W*(12288) + V*(26736 + W*(24576) + V*(12288 + W*(12288))) + U*(88484 + W*(77824) +
        V*(166240 + W*(155648) + V*(77824 + W*(77824))) + U*(225680 + W*(204800) + V*(430448 +
        W*(409600) + V*(204800 + W*(204800))) + U*(307328 + W*(286720) + V*(594048 + W*(573440) +
        V*(286720 + W*(286720))) + U*(235520 + W*(225280) + V*(460800 + W*(450560) + V*(225280 +
        W*(225280))) + U*(96256 + W*(94208) + V*(190464 + W*(188416) + V*(94208 + W*(94208))) + U*(16384
        + W*(16384) + V*(32768 + W*(32768) + V*(16384 + W*(16384)))))))))) := by positivity
      _ = gate (chartPowers 1 (U+1) (V+1) (W+1) 0)
          (chartPowers 1 (U+1) (V+1) (W+1) 1)
          (chartPowers 1 (U+1) (V+1) (W+1) 2)
          (chartMasks 1 (U+1) (V+1) (W+1)) 2 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
