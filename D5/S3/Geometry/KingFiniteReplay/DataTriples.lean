/- GID: D5/S3/Geometry/KingFiniteReplay/DataTriples
   generality: I
   mirror-B: D5/B/S3/Geometry/KingFiniteReplay/DataTriples
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Geometry/KingFiniteReplay.fortyMoves; premises=D5/S3/Geometry/KingFiniteReplay/FiniteLabels.rowBits_spec
   digest: The exact forty-one Nat-labeled graph states and proved row caches. -/
import D5.S3.Geometry.KingFiniteReplay.FiniteLabels
/-!
# The literal forty-one finite graph states

The scientific input is graph-construction.json, SHA-256
ff9876310835eca475074719e41da20ea0d5056d76b996c3ea7d5b63fcaa0980.
The initial graph is the complement of graph6 JEhbtj{rve?. Ten triple
subdivisions, five matching suspensions and twenty-five Lozin replacements
produce the final 141-vertex, 178-edge graph. Each state retains its actual
edge list; its row identity supplies the adjacency decision procedure.
-/
noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace D5.S3.Geometry.KingFiniteReplay

/-- Exact state 0: 11 vertices and 23 edges. -/
def vertexList00 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def vertices00 : Finset ℕ := vertexList00.toFinset
abbrev Vertex00 := ↥vertices00
def edges00 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 5), (0, 6), (1, 2), (1, 4), (1, 7), (2, 3), (2, 9), (3, 4), (3, 5), (3, 9),
    (4, 5), (4, 7), (4, 10), (5, 6), (5, 10), (6, 7), (6, 8), (7, 8), (8, 9), (8, 10), (9, 10)]
def graph00 : SimpleGraph Vertex00 := listGraph vertices00 edges00
private def rows00 : ℕ → ℕ
  | 0 => 102
  | 1 => 149
  | 2 => 523
  | 3 => 564
  | 4 => 1194
  | 5 => 1113
  | 6 => 417
  | 7 => 338
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | _ => 0
private theorem rows00_correct : ∀ x : Vertex00,
    rowBits edges00 x.val = rows00 x.val := by decide
instance (priority := 2000) graph00Decidable : DecidableRel graph00.Adj :=
  cachedAdjDecidable vertices00 edges00 rows00 rows00_correct

/-- Exact state 1: 14 vertices and 26 edges. -/
def vertexList01 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def vertices01 : Finset ℕ := vertexList01.toFinset
abbrev Vertex01 := ↥vertices01
def edges01 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 4), (1, 7), (2, 3), (2, 9), (3, 4), (3, 5), (3, 9),
    (4, 5), (4, 7), (4, 10), (5, 6), (5, 10), (5, 13), (6, 7), (6, 8), (7, 8), (8, 9), (8, 10),
    (9, 10), (11, 12), (12, 13)]
def graph01 : SimpleGraph Vertex01 := listGraph vertices01 edges01
private def rows01 : ℕ → ℕ
  | 0 => 2118
  | 1 => 149
  | 2 => 523
  | 3 => 564
  | 4 => 1194
  | 5 => 9304
  | 6 => 417
  | 7 => 338
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | 11 => 4097
  | 12 => 10240
  | 13 => 4128
  | _ => 0
private theorem rows01_correct : ∀ x : Vertex01,
    rowBits edges01 x.val = rows01 x.val := by decide
instance (priority := 2000) graph01Decidable : DecidableRel graph01.Adj :=
  cachedAdjDecidable vertices01 edges01 rows01 rows01_correct

/-- Exact state 2: 17 vertices and 29 edges. -/
def vertexList02 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
def vertices02 : Finset ℕ := vertexList02.toFinset
abbrev Vertex02 := ↥vertices02
def edges02 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 4), (1, 7), (2, 3), (2, 9), (3, 4), (3, 5), (3, 9),
    (4, 5), (4, 7), (4, 10), (5, 6), (5, 10), (5, 16), (6, 7), (6, 8), (7, 8), (8, 9), (8, 10),
    (9, 10), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16)]
def graph02 : SimpleGraph Vertex02 := listGraph vertices02 edges02
private def rows02 : ℕ → ℕ
  | 0 => 2118
  | 1 => 149
  | 2 => 523
  | 3 => 564
  | 4 => 1194
  | 5 => 66648
  | 6 => 417
  | 7 => 338
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 32800
  | _ => 0
private theorem rows02_correct : ∀ x : Vertex02,
    rowBits edges02 x.val = rows02 x.val := by decide
instance (priority := 2000) graph02Decidable : DecidableRel graph02.Adj :=
  cachedAdjDecidable vertices02 edges02 rows02 rows02_correct

/-- Exact state 3: 20 vertices and 32 edges. -/
def vertexList03 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def vertices03 : Finset ℕ := vertexList03.toFinset
abbrev Vertex03 := ↥vertices03
def edges03 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 4), (1, 7), (2, 3), (2, 9), (3, 4), (3, 5), (3, 9),
    (4, 5), (4, 7), (4, 10), (5, 6), (5, 10), (5, 19), (6, 7), (6, 8), (7, 8), (8, 9), (8, 10),
    (9, 10), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (17, 18), (18, 19)]
def graph03 : SimpleGraph Vertex03 := listGraph vertices03 edges03
private def rows03 : ℕ → ℕ
  | 0 => 2118
  | 1 => 149
  | 2 => 523
  | 3 => 564
  | 4 => 1194
  | 5 => 525400
  | 6 => 417
  | 7 => 338
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | _ => 0
private theorem rows03_correct : ∀ x : Vertex03,
    rowBits edges03 x.val = rows03 x.val := by decide
instance (priority := 2000) graph03Decidable : DecidableRel graph03.Adj :=
  cachedAdjDecidable vertices03 edges03 rows03 rows03_correct

/-- Exact state 4: 23 vertices and 35 edges. -/
def vertexList04 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
def vertices04 : Finset ℕ := vertexList04.toFinset
abbrev Vertex04 := ↥vertices04
def edges04 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 7), (1, 20), (2, 3), (2, 9), (3, 4), (3, 5), (3, 9),
    (4, 5), (4, 7), (4, 10), (4, 22), (5, 6), (5, 10), (5, 19), (6, 7), (6, 8), (7, 8), (8, 9),
    (8, 10), (9, 10), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (17, 18),
    (18, 19), (20, 21), (21, 22)]
def graph04 : SimpleGraph Vertex04 := listGraph vertices04 edges04
private def rows04 : ℕ → ℕ
  | 0 => 2118
  | 1 => 1048709
  | 2 => 523
  | 3 => 564
  | 4 => 4195496
  | 5 => 525400
  | 6 => 417
  | 7 => 338
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | _ => 0
private theorem rows04_correct : ∀ x : Vertex04,
    rowBits edges04 x.val = rows04 x.val := by decide
instance (priority := 2000) graph04Decidable : DecidableRel graph04.Adj :=
  cachedAdjDecidable vertices04 edges04 rows04 rows04_correct

/-- Exact state 5: 26 vertices and 38 edges. -/
def vertexList05 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
def vertices05 : Finset ℕ := vertexList05.toFinset
abbrev Vertex05 := ↥vertices05
def edges05 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 20), (1, 23), (2, 3), (2, 9), (3, 4), (3, 5),
    (3, 9), (4, 5), (4, 7), (4, 10), (4, 22), (5, 6), (5, 10), (5, 19), (6, 7), (6, 8), (7, 8),
    (7, 25), (8, 9), (8, 10), (9, 10), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17),
    (17, 18), (18, 19), (20, 21), (21, 22), (23, 24), (24, 25)]
def graph05 : SimpleGraph Vertex05 := listGraph vertices05 edges05
private def rows05 : ℕ → ℕ
  | 0 => 2118
  | 1 => 9437189
  | 2 => 523
  | 3 => 564
  | 4 => 4195496
  | 5 => 525400
  | 6 => 417
  | 7 => 33554768
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | 23 => 16777218
  | 24 => 41943040
  | 25 => 16777344
  | _ => 0
private theorem rows05_correct : ∀ x : Vertex05,
    rowBits edges05 x.val = rows05 x.val := by decide
instance (priority := 2000) graph05Decidable : DecidableRel graph05.Adj :=
  cachedAdjDecidable vertices05 edges05 rows05 rows05_correct

/-- Exact state 6: 29 vertices and 41 edges. -/
def vertexList06 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28]
def vertices06 : Finset ℕ := vertexList06.toFinset
abbrev Vertex06 := ↥vertices06
def edges06 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 20), (1, 23), (2, 3), (2, 9), (3, 5), (3, 9),
    (3, 26), (4, 5), (4, 7), (4, 10), (4, 22), (4, 28), (5, 6), (5, 10), (5, 19), (6, 7), (6, 8),
    (7, 8), (7, 25), (8, 9), (8, 10), (9, 10), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16),
    (16, 17), (17, 18), (18, 19), (20, 21), (21, 22), (23, 24), (24, 25), (26, 27), (27, 28)]
def graph06 : SimpleGraph Vertex06 := listGraph vertices06 edges06
private def rows06 : ℕ → ℕ
  | 0 => 2118
  | 1 => 9437189
  | 2 => 523
  | 3 => 67109412
  | 4 => 272630944
  | 5 => 525400
  | 6 => 417
  | 7 => 33554768
  | 8 => 1728
  | 9 => 1292
  | 10 => 816
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | 23 => 16777218
  | 24 => 41943040
  | 25 => 16777344
  | 26 => 134217736
  | 27 => 335544320
  | 28 => 134217744
  | _ => 0
private theorem rows06_correct : ∀ x : Vertex06,
    rowBits edges06 x.val = rows06 x.val := by decide
instance (priority := 2000) graph06Decidable : DecidableRel graph06.Adj :=
  cachedAdjDecidable vertices06 edges06 rows06 rows06_correct

/-- Exact state 7: 32 vertices and 44 edges. -/
def vertexList07 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31]
def vertices07 : Finset ℕ := vertexList07.toFinset
abbrev Vertex07 := ↥vertices07
def edges07 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 20), (1, 23), (2, 3), (2, 9), (3, 5), (3, 9),
    (3, 26), (4, 5), (4, 7), (4, 22), (4, 28), (4, 29), (5, 6), (5, 10), (5, 19), (6, 7), (6, 8),
    (7, 8), (7, 25), (8, 9), (8, 10), (9, 10), (10, 31), (11, 12), (12, 13), (13, 14), (14, 15),
    (15, 16), (16, 17), (17, 18), (18, 19), (20, 21), (21, 22), (23, 24), (24, 25), (26, 27),
    (27, 28), (29, 30), (30, 31)]
def graph07 : SimpleGraph Vertex07 := listGraph vertices07 edges07
private def rows07 : ℕ → ℕ
  | 0 => 2118
  | 1 => 9437189
  | 2 => 523
  | 3 => 67109412
  | 4 => 809500832
  | 5 => 525400
  | 6 => 417
  | 7 => 33554768
  | 8 => 1728
  | 9 => 1292
  | 10 => 2147484448
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | 23 => 16777218
  | 24 => 41943040
  | 25 => 16777344
  | 26 => 134217736
  | 27 => 335544320
  | 28 => 134217744
  | 29 => 1073741840
  | 30 => 2684354560
  | 31 => 1073742848
  | _ => 0
private theorem rows07_correct : ∀ x : Vertex07,
    rowBits edges07 x.val = rows07 x.val := by decide
instance (priority := 2000) graph07Decidable : DecidableRel graph07.Adj :=
  cachedAdjDecidable vertices07 edges07 rows07 rows07_correct

/-- Exact state 8: 35 vertices and 47 edges. -/
def vertexList08 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34]
def vertices08 : Finset ℕ := vertexList08.toFinset
abbrev Vertex08 := ↥vertices08
def edges08 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 20), (1, 23), (2, 3), (2, 9), (3, 5), (3, 9),
    (3, 26), (4, 5), (4, 7), (4, 22), (4, 28), (4, 29), (5, 10), (5, 19), (5, 32), (6, 7), (6, 8),
    (6, 34), (7, 8), (7, 25), (8, 9), (8, 10), (9, 10), (10, 31), (11, 12), (12, 13), (13, 14),
    (14, 15), (15, 16), (16, 17), (17, 18), (18, 19), (20, 21), (21, 22), (23, 24), (24, 25),
    (26, 27), (27, 28), (29, 30), (30, 31), (32, 33), (33, 34)]
def graph08 : SimpleGraph Vertex08 := listGraph vertices08 edges08
private def rows08 : ℕ → ℕ
  | 0 => 2118
  | 1 => 9437189
  | 2 => 523
  | 3 => 67109412
  | 4 => 809500832
  | 5 => 4295492632
  | 6 => 17179869569
  | 7 => 33554768
  | 8 => 1728
  | 9 => 1292
  | 10 => 2147484448
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | 23 => 16777218
  | 24 => 41943040
  | 25 => 16777344
  | 26 => 134217736
  | 27 => 335544320
  | 28 => 134217744
  | 29 => 1073741840
  | 30 => 2684354560
  | 31 => 1073742848
  | 32 => 8589934624
  | 33 => 21474836480
  | 34 => 8589934656
  | _ => 0
private theorem rows08_correct : ∀ x : Vertex08,
    rowBits edges08 x.val = rows08 x.val := by decide
instance (priority := 2000) graph08Decidable : DecidableRel graph08.Adj :=
  cachedAdjDecidable vertices08 edges08 rows08 rows08_correct

/-- Exact state 9: 38 vertices and 50 edges. -/
def vertexList09 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
def vertices09 : Finset ℕ := vertexList09.toFinset
abbrev Vertex09 := ↥vertices09
def edges09 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 20), (1, 23), (2, 3), (2, 9), (3, 5), (3, 9),
    (3, 26), (4, 5), (4, 7), (4, 22), (4, 28), (4, 29), (5, 10), (5, 19), (5, 32), (6, 7), (6, 8),
    (6, 37), (7, 8), (7, 25), (8, 9), (8, 10), (9, 10), (10, 31), (11, 12), (12, 13), (13, 14),
    (14, 15), (15, 16), (16, 17), (17, 18), (18, 19), (20, 21), (21, 22), (23, 24), (24, 25),
    (26, 27), (27, 28), (29, 30), (30, 31), (32, 33), (33, 34), (34, 35), (35, 36), (36, 37)]
def graph09 : SimpleGraph Vertex09 := listGraph vertices09 edges09
private def rows09 : ℕ → ℕ
  | 0 => 2118
  | 1 => 9437189
  | 2 => 523
  | 3 => 67109412
  | 4 => 809500832
  | 5 => 4295492632
  | 6 => 137438953857
  | 7 => 33554768
  | 8 => 1728
  | 9 => 1292
  | 10 => 2147484448
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | 23 => 16777218
  | 24 => 41943040
  | 25 => 16777344
  | 26 => 134217736
  | 27 => 335544320
  | 28 => 134217744
  | 29 => 1073741840
  | 30 => 2684354560
  | 31 => 1073742848
  | 32 => 8589934624
  | 33 => 21474836480
  | 34 => 42949672960
  | 35 => 85899345920
  | 36 => 171798691840
  | 37 => 68719476800
  | _ => 0
private theorem rows09_correct : ∀ x : Vertex09,
    rowBits edges09 x.val = rows09 x.val := by decide
instance (priority := 2000) graph09Decidable : DecidableRel graph09.Adj :=
  cachedAdjDecidable vertices09 edges09 rows09 rows09_correct

/-- Exact state 10: 41 vertices and 53 edges. -/
def vertexList10 : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
def vertices10 : Finset ℕ := vertexList10.toFinset
abbrev Vertex10 := ↥vertices10
def edges10 : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 6), (0, 11), (1, 2), (1, 20), (1, 23), (2, 3), (2, 9), (3, 5), (3, 9),
    (3, 26), (4, 5), (4, 7), (4, 22), (4, 28), (4, 29), (5, 10), (5, 19), (5, 32), (6, 7), (6, 8),
    (6, 37), (7, 25), (7, 38), (8, 9), (8, 10), (8, 40), (9, 10), (10, 31), (11, 12), (12, 13),
    (13, 14), (14, 15), (15, 16), (16, 17), (17, 18), (18, 19), (20, 21), (21, 22), (23, 24),
    (24, 25), (26, 27), (27, 28), (29, 30), (30, 31), (32, 33), (33, 34), (34, 35), (35, 36),
    (36, 37), (38, 39), (39, 40)]
def graph10 : SimpleGraph Vertex10 := listGraph vertices10 edges10
private def rows10 : ℕ → ℕ
  | 0 => 2118
  | 1 => 9437189
  | 2 => 523
  | 3 => 67109412
  | 4 => 809500832
  | 5 => 4295492632
  | 6 => 137438953857
  | 7 => 274911461456
  | 8 => 1099511629376
  | 9 => 1292
  | 10 => 2147484448
  | 11 => 4097
  | 12 => 10240
  | 13 => 20480
  | 14 => 40960
  | 15 => 81920
  | 16 => 163840
  | 17 => 327680
  | 18 => 655360
  | 19 => 262176
  | 20 => 2097154
  | 21 => 5242880
  | 22 => 2097168
  | 23 => 16777218
  | 24 => 41943040
  | 25 => 16777344
  | 26 => 134217736
  | 27 => 335544320
  | 28 => 134217744
  | 29 => 1073741840
  | 30 => 2684354560
  | 31 => 1073742848
  | 32 => 8589934624
  | 33 => 21474836480
  | 34 => 42949672960
  | 35 => 85899345920
  | 36 => 171798691840
  | 37 => 68719476800
  | 38 => 549755814016
  | 39 => 1374389534720
  | 40 => 549755814144
  | _ => 0
private theorem rows10_correct : ∀ x : Vertex10,
    rowBits edges10 x.val = rows10 x.val := by decide
instance (priority := 2000) graph10Decidable : DecidableRel graph10.Adj :=
  cachedAdjDecidable vertices10 edges10 rows10 rows10_correct


end D5.S3.Geometry.KingFiniteReplay
