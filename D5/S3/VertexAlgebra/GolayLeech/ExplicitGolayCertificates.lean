/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCertificates
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel finite blocks certify all extended polynomial-code weights. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayBlockProofs

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCertificates
open ExplicitGolayCode ExplicitGolayBlockProofs

theorem certified_blocks : ∀ block : Fin 64, ∀ tail : Fin 6 → Binary,
    weight (encode (joinedMessage (packedPrefix block) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix block) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix block) tail))) := by
  intro block tail
  fin_cases block
  · change weight (encode (joinedMessage (packedPrefix (0 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (0 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (0 : Fin 64)) tail)))
    have equality : packedPrefix 0 = ![0, 0, 0, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_0 tail
  · change weight (encode (joinedMessage (packedPrefix (1 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (1 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (1 : Fin 64)) tail)))
    have equality : packedPrefix 1 = ![1, 0, 0, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_1 tail
  · change weight (encode (joinedMessage (packedPrefix (2 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (2 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (2 : Fin 64)) tail)))
    have equality : packedPrefix 2 = ![0, 1, 0, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_2 tail
  · change weight (encode (joinedMessage (packedPrefix (3 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (3 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (3 : Fin 64)) tail)))
    have equality : packedPrefix 3 = ![1, 1, 0, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_3 tail
  · change weight (encode (joinedMessage (packedPrefix (4 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (4 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (4 : Fin 64)) tail)))
    have equality : packedPrefix 4 = ![0, 0, 1, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_4 tail
  · change weight (encode (joinedMessage (packedPrefix (5 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (5 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (5 : Fin 64)) tail)))
    have equality : packedPrefix 5 = ![1, 0, 1, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_5 tail
  · change weight (encode (joinedMessage (packedPrefix (6 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (6 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (6 : Fin 64)) tail)))
    have equality : packedPrefix 6 = ![0, 1, 1, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_6 tail
  · change weight (encode (joinedMessage (packedPrefix (7 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (7 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (7 : Fin 64)) tail)))
    have equality : packedPrefix 7 = ![1, 1, 1, 0, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_7 tail
  · change weight (encode (joinedMessage (packedPrefix (8 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (8 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (8 : Fin 64)) tail)))
    have equality : packedPrefix 8 = ![0, 0, 0, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_8 tail
  · change weight (encode (joinedMessage (packedPrefix (9 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (9 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (9 : Fin 64)) tail)))
    have equality : packedPrefix 9 = ![1, 0, 0, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_9 tail
  · change weight (encode (joinedMessage (packedPrefix (10 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (10 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (10 : Fin 64)) tail)))
    have equality : packedPrefix 10 = ![0, 1, 0, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_10 tail
  · change weight (encode (joinedMessage (packedPrefix (11 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (11 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (11 : Fin 64)) tail)))
    have equality : packedPrefix 11 = ![1, 1, 0, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_11 tail
  · change weight (encode (joinedMessage (packedPrefix (12 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (12 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (12 : Fin 64)) tail)))
    have equality : packedPrefix 12 = ![0, 0, 1, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_12 tail
  · change weight (encode (joinedMessage (packedPrefix (13 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (13 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (13 : Fin 64)) tail)))
    have equality : packedPrefix 13 = ![1, 0, 1, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_13 tail
  · change weight (encode (joinedMessage (packedPrefix (14 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (14 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (14 : Fin 64)) tail)))
    have equality : packedPrefix 14 = ![0, 1, 1, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_14 tail
  · change weight (encode (joinedMessage (packedPrefix (15 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (15 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (15 : Fin 64)) tail)))
    have equality : packedPrefix 15 = ![1, 1, 1, 1, 0, 0] := by decide
    rw [equality]
    exact weight_chunk_15 tail
  · change weight (encode (joinedMessage (packedPrefix (16 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (16 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (16 : Fin 64)) tail)))
    have equality : packedPrefix 16 = ![0, 0, 0, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_16 tail
  · change weight (encode (joinedMessage (packedPrefix (17 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (17 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (17 : Fin 64)) tail)))
    have equality : packedPrefix 17 = ![1, 0, 0, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_17 tail
  · change weight (encode (joinedMessage (packedPrefix (18 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (18 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (18 : Fin 64)) tail)))
    have equality : packedPrefix 18 = ![0, 1, 0, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_18 tail
  · change weight (encode (joinedMessage (packedPrefix (19 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (19 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (19 : Fin 64)) tail)))
    have equality : packedPrefix 19 = ![1, 1, 0, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_19 tail
  · change weight (encode (joinedMessage (packedPrefix (20 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (20 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (20 : Fin 64)) tail)))
    have equality : packedPrefix 20 = ![0, 0, 1, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_20 tail
  · change weight (encode (joinedMessage (packedPrefix (21 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (21 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (21 : Fin 64)) tail)))
    have equality : packedPrefix 21 = ![1, 0, 1, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_21 tail
  · change weight (encode (joinedMessage (packedPrefix (22 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (22 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (22 : Fin 64)) tail)))
    have equality : packedPrefix 22 = ![0, 1, 1, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_22 tail
  · change weight (encode (joinedMessage (packedPrefix (23 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (23 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (23 : Fin 64)) tail)))
    have equality : packedPrefix 23 = ![1, 1, 1, 0, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_23 tail
  · change weight (encode (joinedMessage (packedPrefix (24 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (24 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (24 : Fin 64)) tail)))
    have equality : packedPrefix 24 = ![0, 0, 0, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_24 tail
  · change weight (encode (joinedMessage (packedPrefix (25 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (25 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (25 : Fin 64)) tail)))
    have equality : packedPrefix 25 = ![1, 0, 0, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_25 tail
  · change weight (encode (joinedMessage (packedPrefix (26 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (26 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (26 : Fin 64)) tail)))
    have equality : packedPrefix 26 = ![0, 1, 0, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_26 tail
  · change weight (encode (joinedMessage (packedPrefix (27 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (27 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (27 : Fin 64)) tail)))
    have equality : packedPrefix 27 = ![1, 1, 0, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_27 tail
  · change weight (encode (joinedMessage (packedPrefix (28 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (28 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (28 : Fin 64)) tail)))
    have equality : packedPrefix 28 = ![0, 0, 1, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_28 tail
  · change weight (encode (joinedMessage (packedPrefix (29 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (29 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (29 : Fin 64)) tail)))
    have equality : packedPrefix 29 = ![1, 0, 1, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_29 tail
  · change weight (encode (joinedMessage (packedPrefix (30 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (30 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (30 : Fin 64)) tail)))
    have equality : packedPrefix 30 = ![0, 1, 1, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_30 tail
  · change weight (encode (joinedMessage (packedPrefix (31 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (31 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (31 : Fin 64)) tail)))
    have equality : packedPrefix 31 = ![1, 1, 1, 1, 1, 0] := by decide
    rw [equality]
    exact weight_chunk_31 tail
  · change weight (encode (joinedMessage (packedPrefix (32 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (32 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (32 : Fin 64)) tail)))
    have equality : packedPrefix 32 = ![0, 0, 0, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_32 tail
  · change weight (encode (joinedMessage (packedPrefix (33 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (33 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (33 : Fin 64)) tail)))
    have equality : packedPrefix 33 = ![1, 0, 0, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_33 tail
  · change weight (encode (joinedMessage (packedPrefix (34 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (34 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (34 : Fin 64)) tail)))
    have equality : packedPrefix 34 = ![0, 1, 0, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_34 tail
  · change weight (encode (joinedMessage (packedPrefix (35 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (35 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (35 : Fin 64)) tail)))
    have equality : packedPrefix 35 = ![1, 1, 0, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_35 tail
  · change weight (encode (joinedMessage (packedPrefix (36 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (36 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (36 : Fin 64)) tail)))
    have equality : packedPrefix 36 = ![0, 0, 1, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_36 tail
  · change weight (encode (joinedMessage (packedPrefix (37 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (37 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (37 : Fin 64)) tail)))
    have equality : packedPrefix 37 = ![1, 0, 1, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_37 tail
  · change weight (encode (joinedMessage (packedPrefix (38 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (38 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (38 : Fin 64)) tail)))
    have equality : packedPrefix 38 = ![0, 1, 1, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_38 tail
  · change weight (encode (joinedMessage (packedPrefix (39 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (39 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (39 : Fin 64)) tail)))
    have equality : packedPrefix 39 = ![1, 1, 1, 0, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_39 tail
  · change weight (encode (joinedMessage (packedPrefix (40 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (40 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (40 : Fin 64)) tail)))
    have equality : packedPrefix 40 = ![0, 0, 0, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_40 tail
  · change weight (encode (joinedMessage (packedPrefix (41 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (41 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (41 : Fin 64)) tail)))
    have equality : packedPrefix 41 = ![1, 0, 0, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_41 tail
  · change weight (encode (joinedMessage (packedPrefix (42 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (42 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (42 : Fin 64)) tail)))
    have equality : packedPrefix 42 = ![0, 1, 0, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_42 tail
  · change weight (encode (joinedMessage (packedPrefix (43 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (43 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (43 : Fin 64)) tail)))
    have equality : packedPrefix 43 = ![1, 1, 0, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_43 tail
  · change weight (encode (joinedMessage (packedPrefix (44 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (44 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (44 : Fin 64)) tail)))
    have equality : packedPrefix 44 = ![0, 0, 1, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_44 tail
  · change weight (encode (joinedMessage (packedPrefix (45 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (45 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (45 : Fin 64)) tail)))
    have equality : packedPrefix 45 = ![1, 0, 1, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_45 tail
  · change weight (encode (joinedMessage (packedPrefix (46 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (46 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (46 : Fin 64)) tail)))
    have equality : packedPrefix 46 = ![0, 1, 1, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_46 tail
  · change weight (encode (joinedMessage (packedPrefix (47 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (47 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (47 : Fin 64)) tail)))
    have equality : packedPrefix 47 = ![1, 1, 1, 1, 0, 1] := by decide
    rw [equality]
    exact weight_chunk_47 tail
  · change weight (encode (joinedMessage (packedPrefix (48 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (48 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (48 : Fin 64)) tail)))
    have equality : packedPrefix 48 = ![0, 0, 0, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_48 tail
  · change weight (encode (joinedMessage (packedPrefix (49 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (49 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (49 : Fin 64)) tail)))
    have equality : packedPrefix 49 = ![1, 0, 0, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_49 tail
  · change weight (encode (joinedMessage (packedPrefix (50 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (50 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (50 : Fin 64)) tail)))
    have equality : packedPrefix 50 = ![0, 1, 0, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_50 tail
  · change weight (encode (joinedMessage (packedPrefix (51 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (51 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (51 : Fin 64)) tail)))
    have equality : packedPrefix 51 = ![1, 1, 0, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_51 tail
  · change weight (encode (joinedMessage (packedPrefix (52 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (52 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (52 : Fin 64)) tail)))
    have equality : packedPrefix 52 = ![0, 0, 1, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_52 tail
  · change weight (encode (joinedMessage (packedPrefix (53 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (53 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (53 : Fin 64)) tail)))
    have equality : packedPrefix 53 = ![1, 0, 1, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_53 tail
  · change weight (encode (joinedMessage (packedPrefix (54 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (54 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (54 : Fin 64)) tail)))
    have equality : packedPrefix 54 = ![0, 1, 1, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_54 tail
  · change weight (encode (joinedMessage (packedPrefix (55 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (55 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (55 : Fin 64)) tail)))
    have equality : packedPrefix 55 = ![1, 1, 1, 0, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_55 tail
  · change weight (encode (joinedMessage (packedPrefix (56 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (56 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (56 : Fin 64)) tail)))
    have equality : packedPrefix 56 = ![0, 0, 0, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_56 tail
  · change weight (encode (joinedMessage (packedPrefix (57 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (57 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (57 : Fin 64)) tail)))
    have equality : packedPrefix 57 = ![1, 0, 0, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_57 tail
  · change weight (encode (joinedMessage (packedPrefix (58 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (58 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (58 : Fin 64)) tail)))
    have equality : packedPrefix 58 = ![0, 1, 0, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_58 tail
  · change weight (encode (joinedMessage (packedPrefix (59 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (59 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (59 : Fin 64)) tail)))
    have equality : packedPrefix 59 = ![1, 1, 0, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_59 tail
  · change weight (encode (joinedMessage (packedPrefix (60 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (60 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (60 : Fin 64)) tail)))
    have equality : packedPrefix 60 = ![0, 0, 1, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_60 tail
  · change weight (encode (joinedMessage (packedPrefix (61 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (61 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (61 : Fin 64)) tail)))
    have equality : packedPrefix 61 = ![1, 0, 1, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_61 tail
  · change weight (encode (joinedMessage (packedPrefix (62 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (62 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (62 : Fin 64)) tail)))
    have equality : packedPrefix 62 = ![0, 1, 1, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_62 tail
  · change weight (encode (joinedMessage (packedPrefix (63 : Fin 64)) tail)) % 4 = 0 ∧
      (encode (joinedMessage (packedPrefix (63 : Fin 64)) tail) ≠ 0 →
        8 ≤ weight (encode (joinedMessage (packedPrefix (63 : Fin 64)) tail)))
    have equality : packedPrefix 63 = ![1, 1, 1, 1, 1, 1] := by decide
    rw [equality]
    exact weight_chunk_63 tail

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCertificates
