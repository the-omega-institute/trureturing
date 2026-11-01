/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowBAdjacent
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twelve exact positive Horner gate proofs for low_b_adjacent. -/
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

-- Complete shifted coefficient map: low_b_adjacent; grouped by exact Horner identities.
-- Python supplies source literals only. Lean ring and positivity prove each gate.
set_option maxHeartbeats 8000000 in
private theorem low_b_adjacent_gates (u v w : ℤ) (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (chartPowers 3 u v w 0) (chartPowers 3 u v w 1)
        (chartPowers 3 u v w 2) (chartMasks 3 u v w) r slot := by
  obtain ⟨U,hU,rfl⟩ : ∃ U : ℤ, 0≤U ∧ u=U+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨V,hV,rfl⟩ : ∃ V : ℤ, 0≤V ∧ v=V+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨W,hW,rfl⟩ : ∃ W : ℤ, 0≤W ∧ w=W+1 := ⟨w-1,by omega,by ring⟩
  intro r slot
  fin_cases r <;> fin_cases slot
  · -- low_b_adjacent/2S1: 20 positive coefficient leaves.
    calc
      0 ≤ (11846 + V*(33720 + V*(32128 + V*(10240))) + U*(45704 + V*(131960 + V*(127232 + V*(40960))) +
        U*(66112 + V*(193472 + V*(188800 + V*(61440))) + U*(42496 + V*(125952 + V*(124416 + V*(40960)))
        + U*(10240 + V*(30720 + V*(30720 + V*(10240)))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 0 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/old_cap_1: 30 positive coefficient leaves.
    calc
      0 ≤ (25530 + V*(110664 + V*(177280 + V*(124928 + V*(32768)))) + U*(136056 + V*(575624 + V*(906496
        + V*(630784 + V*(163840)))) + U*(287680 + V*(1194048 + V*(1852544 + V*(1273856 + V*(327680)))) +
        U*(302080 + V*(1234944 + V*(1891328 + V*(1286144 + V*(327680)))) + U*(157696 + V*(636928 +
        V*(964608 + V*(649216 + V*(163840)))) + U*(32768 + V*(131072 + V*(196608 + V*(131072 +
        V*(32768)))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 0 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/2T1: 20 positive coefficient leaves.
    calc
      0 ≤ (18380 + V*(52928 + V*(50944 + V*(16384))) + U*(71568 + V*(208256 + V*(202240 + V*(65536))) +
        U*(104384 + V*(306880 + V*(300800 + V*(98304))) + U*(67584 + V*(200704 + V*(198656 + V*(65536)))
        + U*(16384 + V*(49152 + V*(49152 + V*(16384)))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 0 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/new_cap_1: 30 positive coefficient leaves.
    calc
      0 ≤ (51764 + V*(222528 + V*(355072 + V*(249856 + V*(65536)))) + U*(274032 + V*(1154688 +
        V*(1814528 + V*(1261568 + V*(327680)))) + U*(577088 + V*(2391360 + V*(3706624 + V*(2547712 +
        V*(655360)))) + U*(604672 + V*(2470912 + V*(3783168 + V*(2572288 + V*(655360)))) + U*(315392 +
        V*(1273856 + V*(1929216 + V*(1298432 + V*(327680)))) + U*(65536 + V*(262144 + V*(393216 +
        V*(262144 + V*(65536)))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 0 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/2S2: 48 positive coefficient leaves.
    calc
      0 ≤ (963670 + V*(4872216 + V*(9884608 + V*(10055680 + V*(5128192 + V*(1048576))))) + U*(6769848 +
        V*(34281528 + V*(69569408 + V*(70713344 + V*(35995648 + V*(7340032))))) + U*(20458592 +
        V*(103610400 + V*(210103232 + V*(213229568 + V*(108298240 + V*(22020096))))) + U*(34456576 +
        V*(174311424 + V*(352896000 + V*(357384192 + V*(181043200 + V*(36700160))))) + U*(34910208 +
        V*(176246784 + V*(355979264 + V*(359559168 + V*(181616640 + V*(36700160))))) + U*(21266432 +
        V*(107069440 + V*(215629824 + V*(217137152 + V*(109330432 + V*(22020096))))) + U*(7208960 +
        V*(36175872 + V*(72613888 + V*(72876032 + V*(36569088 + V*(7340032))))) + U*(1048576 +
        V*(5242880 + V*(10485760 + V*(10485760 + V*(5242880 + V*(1048576))))))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 1 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/old_cap_2: 35 positive coefficient leaves.
    calc
      0 ≤ (86962 + V*(376816 + V*(607296 + V*(432128 + V*(114688)))) + U*(578384 + V*(2443216 +
        V*(3855488 + V*(2695168 + V*(704512)))) + U*(1573792 + V*(6526944 + V*(10134592 + V*(6983680 +
        V*(1802240)))) + U*(2251776 + V*(9213952 + V*(14130176 + V*(9625600 + V*(2457600)))) +
        U*(1792000 + V*(7260160 + V*(11028480 + V*(7444480 + V*(1884160)))) + U*(753664 + V*(3031040 +
        V*(4571136 + V*(3063808 + V*(770048)))) + U*(131072 + V*(524288 + V*(786432 + V*(524288 +
        V*(131072))))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 1 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/2T2: 48 positive coefficient leaves.
    calc
      0 ≤ (1774100 + V*(9155480 + V*(18919808 + V*(19566592 + V*(10125312 + V*(2097152))))) +
        U*(12650040 + V*(65112888 + V*(134120704 + V*(138182656 + V*(71204864 + V*(14680064))))) +
        U*(38757920 + V*(198781856 + V*(407840128 + V*(418406400 + V*(214630400 + V*(44040192))))) +
        U*(66109952 + V*(337593344 + V*(689521152 + V*(704102400 + V*(359464960 + V*(73400320))))) +
        U*(67768320 + V*(344371200 + V*(699904000 + V*(711168000 + V*(361267200 + V*(73400320))))) +
        U*(41730048 + V*(210944000 + V*(426491904 + V*(431112192 + V*(217874432 + V*(44040192))))) +
        U*(14286848 + V*(71827456 + V*(144441344 + V*(145227776 + V*(73007104 + V*(14680064))))) +
        U*(2097152 + V*(10485760 + V*(20971520 + V*(20971520 + V*(10485760 + V*(2097152))))))))))))) :=
        by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 1 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/new_cap_2: 35 positive coefficient leaves.
    calc
      0 ≤ (327164 + V*(1342584 + V*(2064000 + V*(1409024 + V*(360448)))) + U*(2046424 + V*(8336600 +
        V*(12729088 + V*(8634368 + V*(2195456)))) + U*(5306848 + V*(21492832 + V*(32635520 + V*(22020096
        + V*(5570560)))) + U*(7306752 + V*(29457408 + V*(44531200 + V*(29917184 + V*(7536640)))) +
        U*(5636096 + V*(22642688 + V*(34111488 + V*(22839296 + V*(5734400)))) + U*(2310144 + V*(9256960
        + V*(13910016 + V*(9289728 + V*(2326528)))) + U*(393216 + V*(1572864 + V*(2359296 + V*(1572864 +
        V*(393216))))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 1 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/2S3: 30 positive coefficient leaves.
    calc
      0 ≤ (74456 + V*(271768 + V*(369344 + V*(221184 + V*(49152)))) + U*(362680 + V*(1331512 +
        V*(1820800 + V*(1097728 + V*(245760)))) + U*(706784 + V*(2609568 + V*(3590336 + V*(2179072 +
        V*(491520)))) + U*(688896 + V*(2557440 + V*(3539712 + V*(2162688 + V*(491520)))) + U*(335872 +
        V*(1253376 + V*(1744896 + V*(1073152 + V*(245760)))) + U*(65536 + V*(245760 + V*(344064 +
        V*(212992 + V*(49152)))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 2 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/old_cap_3: 48 positive coefficient leaves.
    calc
      0 ≤ (1105448 + V*(5495912 + V*(10903104 + V*(10788864 + V*(5324800 + V*(1048576))))) + U*(7764552
        + V*(38515912 + V*(76298880 + V*(75448320 + V*(37240832 + V*(7340032))))) + U*(23280160 +
        V*(115356768 + V*(228407872 + V*(225886208 + V*(111575040 + V*(22020096))))) + U*(38632960 +
        V*(191429632 + V*(379190784 + V*(375324672 + V*(185630720 + V*(36700160))))) + U*(38330368 +
        V*(190111744 + V*(377053184 + V*(373792768 + V*(185221120 + V*(36700160))))) + U*(22740992 +
        V*(113000448 + V*(224575488 + V*(223133696 + V*(110837760 + V*(22020096))))) + U*(7471104 +
        V*(37224448 + V*(74186752 + V*(73924608 + V*(36831232 + V*(7340032))))) + U*(1048576 +
        V*(5242880 + V*(10485760 + V*(10485760 + V*(5242880 + V*(1048576))))))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 2 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/2T3: 48 positive coefficient leaves.
    calc
      0 ≤ (1172120 + V*(5711128 + V*(11149952 + V*(10903552 + V*(5341184 + V*(1048576))))) + U*(7948344
        + V*(39014456 + V*(76695552 + V*(75481088 + V*(37191680 + V*(7340032))))) + U*(23218336 +
        V*(114676000 + V*(226740352 + V*(224346112 + V*(111083520 + V*(22020096))))) + U*(37880576 +
        V*(188024320 + V*(373490432 + V*(371130368 + V*(184483840 + V*(36700160))))) + U*(37281792 +
        V*(185737216 + V*(370221056 + V*(369057792 + V*(183992320 + V*(36700160))))) + U*(22134784 +
        V*(110542848 + V*(220839936 + V*(220610560 + V*(110198784 + V*(22020096))))) + U*(7340032 +
        V*(36700160 + V*(73400320 + V*(73400320 + V*(36700160 + V*(7340032))))) + U*(1048576 +
        V*(5242880 + V*(10485760 + V*(10485760 + V*(5242880 + V*(1048576))))))))))))) := by positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 2 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- low_b_adjacent/new_cap_3: 35 positive coefficient leaves.
    calc
      0 ≤ (7784 + V*(56552 + V*(122496 + V*(106496 + V*(32768)))) + U*(178888 + V*(832968 + V*(1424128 +
        V*(1064960 + V*(294912)))) + U*(768608 + V*(3290336 + V*(5257856 + V*(3719168 + V*(983040)))) +
        U*(1441280 + V*(5962752 + V*(9240064 + V*(6356992 + V*(1638400)))) + U*(1384448 + V*(5627904 +
        V*(8577024 + V*(5808128 + V*(1474560)))) + U*(671744 + V*(2703360 + V*(4079616 + V*(2736128 +
        V*(688128)))) + U*(131072 + V*(524288 + V*(786432 + V*(524288 + V*(131072))))))))))) := by
        positivity
      _ = gate (chartPowers 3 (U+1) (V+1) (W+1) 0)
          (chartPowers 3 (U+1) (V+1) (W+1) 1)
          (chartPowers 3 (U+1) (V+1) (W+1) 2)
          (chartMasks 3 (U+1) (V+1) (W+1)) 2 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
