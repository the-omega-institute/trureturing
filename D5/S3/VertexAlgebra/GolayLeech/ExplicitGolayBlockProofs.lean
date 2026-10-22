/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayBlockProofs
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayBlockProofs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All finite Golay message blocks have kernel-proved weight constraints. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCode
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayBlockProofs
open ExplicitGolayCode

theorem weight_chunk_0 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_1 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_2 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_3 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_4 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_5 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_6 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_7 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 0, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 0, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 0, 0, 0] tail))) := by
  decide

theorem weight_chunk_8 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_9 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_10 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_11 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_12 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_13 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_14 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_15 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 1, 0, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 1, 0, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 1, 0, 0] tail))) := by
  decide

theorem weight_chunk_16 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_17 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_18 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_19 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_20 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_21 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_22 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_23 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 0, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 0, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 0, 1, 0] tail))) := by
  decide

theorem weight_chunk_24 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_25 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_26 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_27 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_28 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_29 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_30 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_31 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 1, 1, 0] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 1, 1, 0] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 1, 1, 0] tail))) := by
  decide

theorem weight_chunk_32 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_33 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_34 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_35 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_36 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_37 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_38 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_39 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 0, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 0, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 0, 0, 1] tail))) := by
  decide

theorem weight_chunk_40 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_41 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_42 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_43 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_44 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_45 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_46 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_47 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 1, 0, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 1, 0, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 1, 0, 1] tail))) := by
  decide

theorem weight_chunk_48 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_49 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_50 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_51 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_52 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_53 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_54 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_55 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 0, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 0, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 0, 1, 1] tail))) := by
  decide

theorem weight_chunk_56 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 0, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 0, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 0, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_57 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 0, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 0, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 0, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_58 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 0, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 0, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 0, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_59 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 0, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 0, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 0, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_60 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 0, 1, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 0, 1, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 0, 1, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_61 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 0, 1, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 0, 1, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 0, 1, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_62 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![0, 1, 1, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![0, 1, 1, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![0, 1, 1, 1, 1, 1] tail))) := by
  decide

theorem weight_chunk_63 : ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage ![1, 1, 1, 1, 1, 1] tail)) % 4 = 0 ∧
    (encode (joinedMessage ![1, 1, 1, 1, 1, 1] tail) ≠ 0 →
      8 ≤ weight (encode (joinedMessage ![1, 1, 1, 1, 1, 1] tail))) := by
  decide

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayBlockProofs
