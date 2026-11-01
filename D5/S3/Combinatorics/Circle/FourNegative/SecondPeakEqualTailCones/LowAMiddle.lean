/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowAMiddle
   generality: I
   mirror-B: none(waiver:private-consumed-exact-arithmetic)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Twelve exact positive Horner gate proofs for a_between_s_plus2_and_2s. -/
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

-- Complete shifted coefficient map: a_between_s_plus2_and_2s; grouped by exact Horner identities.
-- Python supplies source literals only. Lean ring and positivity prove each gate.
set_option maxHeartbeats 8000000 in
private theorem a_between_s_plus2_and_2s_gates (u v w : ℤ) (hu : 1≤u) (hv : 1≤v) (hw : 1≤w) :
    ∀ (r : Fin 3) (slot : Fin 4),
      0≤gate (chartPowers 6 u v w 0) (chartPowers 6 u v w 1)
        (chartPowers 6 u v w 2) (chartMasks 6 u v w) r slot := by
  obtain ⟨U,hU,rfl⟩ : ∃ U : ℤ, 0≤U ∧ u=U+1 := ⟨u-1,by omega,by ring⟩
  obtain ⟨V,hV,rfl⟩ : ∃ V : ℤ, 0≤V ∧ v=V+1 := ⟨v-1,by omega,by ring⟩
  obtain ⟨W,hW,rfl⟩ : ∃ W : ℤ, 0≤W ∧ w=W+1 := ⟨w-1,by omega,by ring⟩
  intro r slot
  fin_cases r <;> fin_cases slot
  · -- a_between_s_plus2_and_2s/2S1: 72 positive coefficient leaves.
    calc
      0 ≤ (2070 + W*(2588) + V*(9140 + W*(10648) + V*(16076 + W*(17580) + V*(14064 + W*(14576) + V*(6080
        + W*(6080) + V*(1024 + W*(1024)))))) + U*(8744 + W*(10732) + V*(40164 + W*(46120) + V*(73308 +
        W*(79324) + V*(66272 + W*(68320) + V*(29504 + W*(29504) + V*(5120 + W*(5120)))))) + U*(14864 +
        W*(17808) + V*(70832 + W*(79760) + V*(133712 + W*(142768) + V*(124656 + W*(127728) + V*(57152 +
        W*(57152) + V*(10240 + W*(10240)))))) + U*(12800 + W*(14784) + V*(62848 + W*(68864) + V*(122048
        + W*(128128) + V*(116992 + W*(119040) + V*(55232 + W*(55232) + V*(10240 + W*(10240)))))) +
        U*(5632 + W*(6144) + V*(28160 + W*(29696) + V*(55808 + W*(57344) + V*(54784 + W*(55296) +
        V*(26624 + W*(26624) + V*(5120 + W*(5120)))))) + U*(1024 + W*(1024) + V*(5120 + W*(5120) +
        V*(10240 + W*(10240) + V*(10240 + W*(10240) + V*(5120 + W*(5120) + V*(1024 + W*(1024))))))))))))
        := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 0 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/old_cap_1: 72 positive coefficient leaves.
    calc
      0 ≤ (618 + W*(100) + V*(3532 + W*(2024) + V*(7860 + W*(6356) + V*(8592 + W*(8080) + V*(4672 +
        W*(4672) + V*(1024 + W*(1024)))))) + U*(3928 + W*(1940) + V*(20380 + W*(14424) + V*(42532 +
        W*(36516) + V*(44704 + W*(42656) + V*(23744 + W*(23744) + V*(5120 + W*(5120)))))) + U*(9072 +
        W*(6128) + V*(45008 + W*(36080) + V*(90672 + W*(81616) + V*(92816 + W*(89744) + V*(48320 +
        W*(48320) + V*(10240 + W*(10240)))))) + U*(9856 + W*(7872) + V*(48128 + W*(42112) + V*(95424 +
        W*(89344) + V*(96128 + W*(94080) + V*(49216 + W*(49216) + V*(10240 + W*(10240)))))) + U*(5120 +
        W*(4608) + V*(25088 + W*(23552) + V*(49664 + W*(48128) + V*(49664 + W*(49152) + V*(25088 +
        W*(25088) + V*(5120 + W*(5120)))))) + U*(1024 + W*(1024) + V*(5120 + W*(5120) + V*(10240 +
        W*(10240) + V*(10240 + W*(10240) + V*(5120 + W*(5120) + V*(1024 + W*(1024)))))))))))) := by
        positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 0 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/2T1: 72 positive coefficient leaves.
    calc
      0 ≤ (3288 + W*(4316) + V*(15320 + W*(18328) + V*(28268 + W*(31276) + V*(25840 + W*(26864) +
        V*(11648 + W*(11648) + V*(2048 + W*(2048)))))) + U*(14508 + W*(18476) + V*(69544 + W*(81448) +
        V*(131932 + W*(143964) + V*(123616 + W*(127712) + V*(56960 + W*(56960) + V*(10240 +
        W*(10240)))))) + U*(25808 + W*(31696) + V*(126928 + W*(144784) + V*(246640 + W*(264752) +
        V*(236272 + W*(242416) + V*(111232 + W*(111232) + V*(20480 + W*(20480)))))) + U*(23296 +
        W*(27264) + V*(116736 + W*(128768) + V*(231040 + W*(243200) + V*(225536 + W*(229632) + V*(108416
        + W*(108416) + V*(20480 + W*(20480)))))) + U*(10752 + W*(11776) + V*(54272 + W*(57344) +
        V*(108544 + W*(111616) + V*(107520 + W*(108544) + V*(52736 + W*(52736) + V*(10240 +
        W*(10240)))))) + U*(2048 + W*(2048) + V*(10240 + W*(10240) + V*(20480 + W*(20480) + V*(20480 +
        W*(20480) + V*(10240 + W*(10240) + V*(2048 + W*(2048)))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 0 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/new_cap_1: 72 positive coefficient leaves.
    calc
      0 ≤ (1448 + W*(420) + V*(7592 + W*(4584) + V*(16148 + W*(13140) + V*(17296 + W*(16272) + V*(9344 +
        W*(9344) + V*(2048 + W*(2048)))))) + U*(8404 + W*(4436) + V*(42200 + W*(30296) + V*(86308 +
        W*(74276) + V*(89760 + W*(85664) + V*(47488 + W*(47488) + V*(10240 + W*(10240)))))) + U*(18608 +
        W*(12720) + V*(91312 + W*(73456) + V*(182544 + W*(164432) + V*(186000 + W*(179856) + V*(96640 +
        W*(96640) + V*(20480 + W*(20480)))))) + U*(19840 + W*(15872) + V*(96640 + W*(84608) + V*(191232
        + W*(179072) + V*(192384 + W*(188288) + V*(98432 + W*(98432) + V*(20480 + W*(20480)))))) +
        U*(10240 + W*(9216) + V*(50176 + W*(47104) + V*(99328 + W*(96256) + V*(99328 + W*(98304) +
        V*(50176 + W*(50176) + V*(10240 + W*(10240)))))) + U*(2048 + W*(2048) + V*(10240 + W*(10240) +
        V*(20480 + W*(20480) + V*(20480 + W*(20480) + V*(10240 + W*(10240) + V*(2048 +
        W*(2048)))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 0 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/2S2: 84 positive coefficient leaves.
    calc
      0 ≤ (5004 + W*(5312) + V*(25788 + W*(26624) + V*(53424 + W*(54208) + V*(55680 + W*(55936) +
        V*(29184 + W*(29184) + V*(6144 + W*(6144)))))) + U*(32160 + W*(33280) + V*(166140 + W*(169344) +
        V*(344288 + W*(347392) + V*(357760 + W*(358784) + V*(186368 + W*(186368) + V*(38912 +
        W*(38912)))))) + U*(86928 + W*(88512) + V*(448192 + W*(452864) + V*(925360 + W*(929984) +
        V*(956288 + W*(957824) + V*(494592 + W*(494592) + V*(102400 + W*(102400)))))) + U*(126080 +
        W*(127104) + V*(646528 + W*(649600) + V*(1326464 + W*(1329536) + V*(1361024 + W*(1362048) +
        V*(698368 + W*(698368) + V*(143360 + W*(143360)))))) + U*(103168 + W*(103424) + V*(525056 +
        W*(525824) + V*(1068800 + W*(1069568) + V*(1087744 + W*(1088000) + V*(553472 + W*(553472) +
        V*(112640 + W*(112640)))))) + U*(45056 + W*(45056) + V*(227328 + W*(227328) + V*(458752 +
        W*(458752) + V*(462848 + W*(462848) + V*(233472 + W*(233472) + V*(47104 + W*(47104)))))) +
        U*(8192 + W*(8192) + V*(40960 + W*(40960) + V*(81920 + W*(81920) + V*(81920 + W*(81920) +
        V*(40960 + W*(40960) + V*(8192 + W*(8192))))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 1 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/old_cap_2: 72 positive coefficient leaves.
    calc
      0 ≤ (3256 + W*(2880) + V*(15304 + W*(14336) + V*(28560 + W*(27712) + V*(26240 + W*(25984) +
        V*(11776 + W*(11776) + V*(2048 + W*(2048)))))) + U*(17188 + W*(15872) + V*(80008 + W*(76416) +
        V*(147424 + W*(144128) + V*(133760 + W*(132736) + V*(59392 + W*(59392) + V*(10240 +
        W*(10240)))))) + U*(36144 + W*(34368) + V*(166592 + W*(161536) + V*(303632 + W*(298816) +
        V*(272512 + W*(270976) + V*(119808 + W*(119808) + V*(20480 + W*(20480)))))) + U*(37824 +
        W*(36736) + V*(172800 + W*(169600) + V*(312000 + W*(308864) + V*(277376 + W*(276352) + V*(120832
        + W*(120832) + V*(20480 + W*(20480)))))) + U*(19712 + W*(19456) + V*(89344 + W*(88576) +
        V*(160000 + W*(159232) + V*(141056 + W*(140800) + V*(60928 + W*(60928) + V*(10240 +
        W*(10240)))))) + U*(4096 + W*(4096) + V*(18432 + W*(18432) + V*(32768 + W*(32768) + V*(28672 +
        W*(28672) + V*(12288 + W*(12288) + V*(2048 + W*(2048)))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 1 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/2T2: 84 positive coefficient leaves.
    calc
      0 ≤ (7770 + W*(8384) + V*(43388 + W*(45056) + V*(95648 + W*(97216) + V*(104576 + W*(105088) +
        V*(56832 + W*(56832) + V*(12288 + W*(12288)))))) + U*(53568 + W*(55808) + V*(291964 + W*(298368)
        + V*(632000 + W*(638208) + V*(680320 + W*(682368) + V*(364544 + W*(364544) + V*(77824 +
        W*(77824)))))) + U*(152928 + W*(156096) + V*(816256 + W*(825600) + V*(1735840 + W*(1745088) +
        V*(1839488 + W*(1842560) + V*(971776 + W*(971776) + V*(204800 + W*(204800)))))) + U*(231552 +
        W*(233600) + V*(1212800 + W*(1218944) + V*(2535808 + W*(2541952) + V*(2646144 + W*(2648192) +
        V*(1378304 + W*(1378304) + V*(286720 + W*(286720)))))) + U*(196096 + W*(196608) + V*(1009664 +
        W*(1011200) + V*(2077696 + W*(2079232) + V*(2136064 + W*(2136576) + V*(1097216 + W*(1097216) +
        V*(225280 + W*(225280)))))) + U*(88064 + W*(88064) + V*(446464 + W*(446464) + V*(905216 +
        W*(905216) + V*(917504 + W*(917504) + V*(464896 + W*(464896) + V*(94208 + W*(94208)))))) +
        U*(16384 + W*(16384) + V*(81920 + W*(81920) + V*(163840 + W*(163840) + V*(163840 + W*(163840) +
        V*(81920 + W*(81920) + V*(16384 + W*(16384))))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 1 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/new_cap_2: 72 positive coefficient leaves.
    calc
      0 ≤ (8750 + W*(8000) + V*(38796 + W*(36864) + V*(68320 + W*(66624) + V*(59264 + W*(58752) +
        V*(25088 + W*(25088) + V*(4096 + W*(4096)))))) + U*(45128 + W*(42496) + V*(200332 + W*(193152) +
        V*(351424 + W*(344832) + V*(302720 + W*(300672) + V*(126976 + W*(126976) + V*(20480 +
        W*(20480)))))) + U*(93216 + W*(89664) + V*(413312 + W*(403200) + V*(722144 + W*(712512) +
        V*(618112 + W*(615040) + V*(257024 + W*(257024) + V*(40960 + W*(40960)))))) + U*(96256 +
        W*(94080) + V*(425856 + W*(419456) + V*(741120 + W*(734848) + V*(630656 + W*(628608) + V*(260096
        + W*(260096) + V*(40960 + W*(40960)))))) + U*(49664 + W*(49152) + V*(219136 + W*(217600) +
        V*(379904 + W*(378368) + V*(321536 + W*(321024) + V*(131584 + W*(131584) + V*(20480 +
        W*(20480)))))) + U*(10240 + W*(10240) + V*(45056 + W*(45056) + V*(77824 + W*(77824) + V*(65536 +
        W*(65536) + V*(26624 + W*(26624) + V*(4096 + W*(4096)))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 1 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/2S3: 40 positive coefficient leaves.
    calc
      0 ≤ (222 + W*(512) + V*(716 + W*(1536) + V*(752 + W*(1536) + V*(256 + W*(512)))) + U*(960 +
        W*(2048) + V*(2972 + W*(6144) + V*(3040 + W*(6144) + V*(1024 + W*(2048)))) + U*(1504 + W*(3072)
        + V*(4560 + W*(9216) + V*(4592 + W*(9216) + V*(1536 + W*(3072)))) + U*(1024 + W*(2048) + V*(3072
        + W*(6144) + V*(3072 + W*(6144) + V*(1024 + W*(2048)))) + U*(256 + W*(512) + V*(768 + W*(1536) +
        V*(768 + W*(1536) + V*(256 + W*(512))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 2 0 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/old_cap_3: 84 positive coefficient leaves.
    calc
      0 ≤ (10034 + W*(9728) + V*(48452 + W*(47616) + V*(93456 + W*(92672) + V*(89856 + W*(89600) +
        V*(43008 + W*(43008) + V*(8192 + W*(8192)))))) + U*(58464 + W*(57344) + V*(283780 + W*(280576) +
        V*(549920 + W*(546816) + V*(531456 + W*(530432) + V*(256000 + W*(256000) + V*(49152 +
        W*(49152)))))) + U*(141872 + W*(140288) + V*(691776 + W*(687104) + V*(1347088 + W*(1342464) +
        V*(1309184 + W*(1307648) + V*(634880 + W*(634880) + V*(122880 + W*(122880)))))) + U*(183296 +
        W*(182272) + V*(898048 + W*(894976) + V*(1758208 + W*(1755136) + V*(1719296 + W*(1718272) +
        V*(839680 + W*(839680) + V*(163840 + W*(163840)))))) + U*(132864 + W*(132608) + V*(654592 +
        W*(653824) + V*(1289472 + W*(1288704) + V*(1269504 + W*(1269248) + V*(624640 + W*(624640) +
        V*(122880 + W*(122880)))))) + U*(51200 + W*(51200) + V*(253952 + W*(253952) + V*(503808 +
        W*(503808) + V*(499712 + W*(499712) + V*(247808 + W*(247808) + V*(49152 + W*(49152)))))) +
        U*(8192 + W*(8192) + V*(40960 + W*(40960) + V*(81920 + W*(81920) + V*(81920 + W*(81920) +
        V*(40960 + W*(40960) + V*(8192 + W*(8192))))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 2 1 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/2T3: 84 positive coefficient leaves.
    calc
      0 ≤ (8142 + W*(8704) + V*(40876 + W*(42496) + V*(81888 + W*(83456) + V*(81920 + W*(82432) +
        V*(40960 + W*(40960) + V*(8192 + W*(8192)))))) + U*(49056 + W*(51200) + V*(245596 + W*(251904) +
        V*(491456 + W*(497664) + V*(491520 + W*(493568) + V*(245760 + W*(245760) + V*(49152 +
        W*(49152)))))) + U*(122832 + W*(125952) + V*(614320 + W*(623616) + V*(1228768 + W*(1238016) +
        V*(1228800 + W*(1231872) + V*(614400 + W*(614400) + V*(122880 + W*(122880)))))) + U*(163840 +
        W*(165888) + V*(819200 + W*(825344) + V*(1638400 + W*(1644544) + V*(1638400 + W*(1640448) +
        V*(819200 + W*(819200) + V*(163840 + W*(163840)))))) + U*(122880 + W*(123392) + V*(614400 +
        W*(615936) + V*(1228800 + W*(1230336) + V*(1228800 + W*(1229312) + V*(614400 + W*(614400) +
        V*(122880 + W*(122880)))))) + U*(49152 + W*(49152) + V*(245760 + W*(245760) + V*(491520 +
        W*(491520) + V*(491520 + W*(491520) + V*(245760 + W*(245760) + V*(49152 + W*(49152)))))) +
        U*(8192 + W*(8192) + V*(40960 + W*(40960) + V*(81920 + W*(81920) + V*(81920 + W*(81920) +
        V*(40960 + W*(40960) + V*(8192 + W*(8192))))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 2 2 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring
  · -- a_between_s_plus2_and_2s/new_cap_3: 60 positive coefficient leaves.
    calc
      0 ≤ (2114 + W*(1536) + V*(8292 + W*(6656) + V*(12320 + W*(10752) + V*(8192 + W*(7680) + V*(2048 +
        W*(2048))))) + U*(10368 + W*(8192) + V*(41156 + W*(34816) + V*(61504 + W*(55296) + V*(40960 +
        W*(38912) + V*(10240 + W*(10240))))) + U*(20544 + W*(17408) + V*(82016 + W*(72704) + V*(122912 +
        W*(113664) + V*(81920 + W*(78848) + V*(20480 + W*(20480))))) + U*(20480 + W*(18432) + V*(81920 +
        W*(75776) + V*(122880 + W*(116736) + V*(81920 + W*(79872) + V*(20480 + W*(20480))))) + U*(10240
        + W*(9728) + V*(40960 + W*(39424) + V*(61440 + W*(59904) + V*(40960 + W*(40448) + V*(10240 +
        W*(10240))))) + U*(2048 + W*(2048) + V*(8192 + W*(8192) + V*(12288 + W*(12288) + V*(8192 +
        W*(8192) + V*(2048 + W*(2048))))))))))) := by positivity
      _ = gate (chartPowers 6 (U+1) (V+1) (W+1) 0)
          (chartPowers 6 (U+1) (V+1) (W+1) 1)
          (chartPowers 6 (U+1) (V+1) (W+1) 2)
          (chartMasks 6 (U+1) (V+1) (W+1)) 2 3 := by
        dsimp [gate,doubledSeams,dot,chartMasks,chartPowers,chartEpsilon,chartDelta,
          allocation,heads,newHeads,successor,newSuccessor,sourceN,delta]
        ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
