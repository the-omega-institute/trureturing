/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7AG2
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7AG2
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.exactChunk
   digest: Checked intervals exhaust a contiguous range of exceptional layer codes. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact
import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked0 : exactChunk positions7a 2048 16 = true := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked1 : exactChunk positions7a 2064 16 = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032_Tail
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked2 : exactChunk positions7a 2080 16 = true := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked3 : exactChunk positions7a 2096 16 = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032_Tail



set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked0 : exactChunk positions7a 2112 16 = true := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked1 : exactChunk positions7a 2128 16 = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033_Tail
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked2 : exactChunk positions7a 2144 16 = true := by decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked3 : exactChunk positions7a 2160 16 = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033_Tail



set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_034
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem checked0 : exactChunk positions7a 2176 11 = true := by decide

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_034


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7AG2
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapExact

/-- Every layer code in this interval satisfies its exact finite row. -/
theorem covers (code : Nat) (hlo : 2048 ≤ code) (hhi : code < 2187) :
    exactRow positions7a code = true := by
  have of_chunk (s k : Nat) (hc : exactChunk positions7a s k = true)
      (hs : s ≤ code) (he : code < s + k) : exactRow positions7a code = true := by
    have hj : code - s ∈ List.range k := List.mem_range.mpr (by omega)
    have hrow := (List.all_eq_true.mp hc) (code - s) hj
    change exactRow positions7a (s + (code - s)) = true at hrow
    simpa [Nat.add_sub_of_le hs] using hrow
  by_cases h2048 : code < 2064
  · exact of_chunk 2048 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032.checked0 (by omega) h2048
  by_cases h2064 : code < 2080
  · exact of_chunk 2064 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032.checked1 (by omega) h2064
  by_cases h2080 : code < 2096
  · exact of_chunk 2080 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032_Tail.checked2 (by omega) h2080
  by_cases h2096 : code < 2112
  · exact of_chunk 2096 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_032_Tail.checked3 (by omega) h2096
  by_cases h2112 : code < 2128
  · exact of_chunk 2112 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033.checked0 (by omega) h2112
  by_cases h2128 : code < 2144
  · exact of_chunk 2128 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033.checked1 (by omega) h2128
  by_cases h2144 : code < 2160
  · exact of_chunk 2144 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033_Tail.checked2 (by omega) h2144
  by_cases h2160 : code < 2176
  · exact of_chunk 2160 16 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_033_Tail.checked3 (by omega) h2160
  by_cases h2176 : code < 2187
  · exact of_chunk 2176 11 D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCertificatesA.ZeroForcingThreeGapExact7A_034.checked0 (by omega) h2176
  omega

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeGapCover7AG2
