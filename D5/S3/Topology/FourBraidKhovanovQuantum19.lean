/- GID: D5/S3/Topology/FourBraidKhovanovQuantum19
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovQuantum19
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: none
   digest: Degree 19 of the signed integral Khovanov cube. -/

import D5.S3.Topology.FourBraidKhovanovIntegralRow


/-! Exact coefficients and contraction identities in the signed integral cube. -/

set_option autoImplicit false

namespace D5.S3.Topology.FourBraidKhovanovCube


set_option maxRecDepth 8192
set_option linter.style.setOption false
set_option maxHeartbeats 3500000

private def b19_8 : Array Enhanced := #[
    (1522, 0)
  ]
private def b19_9 : Array Enhanced := #[
    (509, 0), (510, 0), (765, 0), (893, 0), (957, 0), (989, 0),
    (1005, 0), (1011, 0), (1013, 0), (1017, 0), (1020, 0), (1277, 0),
    (1278, 0), (1405, 0), (1406, 0), (1469, 0), (1470, 0), (1501, 0),
    (1502, 0), (1517, 0), (1518, 0), (1523, 0), (1525, 0), (1526, 0),
    (1529, 0), (1530, 0), (1532, 0), (2034, 0)
  ]
private def b19_10_part0 : Array Enhanced := #[
  (511, 0), (767, 0), (895, 0), (959, 0), (991, 0), (1007, 0),
  (1015, 0), (1019, 0), (1021, 536870912), (1021, 33554432), (1021, 4096), (1021, 16),
  (1021, 8), (1021, 4), (1021, 1), (1022, 0), (1279, 0), (1407, 0),
  (1471, 0), (1503, 0)
]
private def b19_10_part1 : Array Enhanced := #[
  (1519, 0), (1527, 0), (1531, 0), (1533, 137438953472), (1533, 536870912), (1533, 33554432),
  (1533, 4096), (1533, 16), (1533, 8), (1533, 1), (1534, 137438953472), (1534, 536870912),
  (1534, 33554432), (1534, 4096), (1534, 8), (1534, 2), (1534, 1), (1789, 0),
  (1790, 0), (1917, 0)
]
private def b19_10_part2 : Array Enhanced := #[
  (1918, 0), (1981, 0), (1982, 0), (2013, 0), (2014, 0), (2029, 0),
  (2030, 0), (2035, 0), (2037, 0), (2038, 0), (2041, 0), (2042, 0),
  (2044, 0)
]
private def b19_10 : Array Enhanced :=
    b19_10_part0 ++
    b19_10_part1 ++
    b19_10_part2
private def b19_11 : Array Enhanced := #[
    (1023, 536870912), (1023, 33554432), (1023, 4096), (1023, 8), (1023, 4), (1023, 1),
    (1535, 137438953472), (1535, 536870912), (1535, 33554432), (1535, 4096), (1535, 8), (1535, 1),
    (1791, 0), (1919, 0), (1983, 0), (2015, 0), (2031, 0), (2039, 0),
    (2043, 0), (2045, 536870912), (2045, 33554432), (2045, 4096), (2045, 16), (2045, 8),
    (2045, 1), (2046, 536870912), (2046, 33554432), (2046, 4096), (2046, 8), (2046, 2),
    (2046, 1)
  ]
private def b19_12 : Array Enhanced := #[
    (2047, 536870912), (2047, 33554432), (2047, 4096), (2047, 8), (2047, 1)
  ]
private def b19Data : Nat → Array Enhanced
  | 8 => b19_8
  | 9 => b19_9
  | 10 => b19_10
  | 11 => b19_11
  | 12 => b19_12
  | _ => #[]

private def b19 (t : Nat) : Array Enhanced := if t < 13 then b19Data t else #[]

private def d19_8 : RawColumns := #[
    [(21, 1), (23, -1), (25, -1), (27, 1)]
  ]
private def d19_9 : RawColumns := #[
    [(0, -1), (14, 1), (13, 1), (29, 1), (23, 1)], [(0, 1), (15, 1), (35, 1), (30, 1)],
    [(1, -1), (13, -1), (8, -1), (37, 1)], [(2, -1), (12, 1), (8, 1), (39, 1)],
    [(3, -1), (9, -1), (8, -1), (41, 1)], [(4, -1), (13, 1), (9, 1), (43, 1)],
    [(5, -1), (13, -1), (12, -1), (45, 1)], [(6, 1), (7, 1), (47, 1)],
    [(6, -1), (13, 1), (10, 1), (48, 1)], [(7, -1), (11, -1), (10, -1), (50, 1)],
    [(14, 1), (11, 1), (15, 1), (52, 1)], [(16, -1), (24, -1), (23, -1), (37, -1)],
    [(16, 1), (31, -1), (30, -1), (38, -1)], [(17, -1), (28, 1), (24, 1), (39, -1)],
    [(17, 1), (34, 1), (31, 1), (40, -1)], [(18, -1), (25, -1), (24, -1), (41, -1)],
    [(18, 1), (32, -1), (31, -1), (42, -1)], [(19, -1), (29, 1), (25, 1), (43, -1)],
    [(19, 1), (36, 1), (32, 1), (44, -1)], [(20, -1), (29, -1), (28, -1), (45, -1)],
    [(20, 1), (36, -1), (34, -1), (46, -1)], [(21, 1), (22, 1), (47, -1)],
    [(21, -1), (29, 1), (26, 1), (48, -1)], [(21, 1), (36, 1), (33, 1), (49, -1)],
    [(22, -1), (27, -1), (26, -1), (50, -1)], [(22, 1), (36, -1), (33, -1), (51, -1)],
    [(29, 1), (27, 1), (36, 1), (35, 1), (52, -1)], [(47, 1), (49, -1), (51, -1)]
  ]
private def d19_10_part0 : RawColumns := #[
  [(5, -1), (4, -1), (11, -1), (6, -1)], [(4, 1), (0, 1), (12, -1)], [(3, -1), (0, -1), (13, -1)],
  [(1, 1), (0, 1), (14, -1)], [(4, -1), (1, -1), (15, -1)], [(4, 1), (3, 1), (16, -1)],
  [(4, -1), (2, -1), (17, -1)], [(4, 1), (2, 1), (18, -1)], [(0, -1), (19, -1)], [(1, -1), (20, -1)],
  [(2, -1), (21, -1)], [(4, -1), (22, -1)], [(3, -1), (23, -1)], [(4, -1), (24, -1)], [(5, -1), (24, -1)],
  [(5, 1), (4, 1), (30, -1), (29, -1)], [(7, 1), (6, 1), (12, 1)], [(10, -1), (7, -1), (13, 1)],
  [(8, 1), (7, 1), (14, 1)], [(11, -1), (8, -1), (15, 1)]
]
private def d19_10_part1 : RawColumns := #[
  [(11, 1), (10, 1), (16, 1)], [(11, -1), (9, -1), (17, 1)], [(11, 1), (9, 1), (18, 1)],
  [(6, -1), (24, 1)], [(7, -1), (19, 1)], [(8, -1), (20, 1)], [(9, -1), (21, 1)], [(11, -1), (22, 1)],
  [(10, -1), (23, 1)], [(11, -1), (24, 1)], [(6, 1), (30, 1)], [(7, 1), (25, 1)], [(8, 1), (26, 1)],
  [(9, 1), (27, 1)], [(10, 1), (28, 1)], [(11, 1), (29, 1)], [(11, 1), (30, 1)],
  [(12, -1), (24, -1), (19, -1)], [(12, 1), (30, -1), (25, -1)], [(13, -1), (23, 1), (19, 1)]
]
private def d19_10_part2 : RawColumns := #[
  [(13, 1), (28, 1), (25, 1)], [(14, -1), (20, -1), (19, -1)], [(14, 1), (26, -1), (25, -1)],
  [(15, -1), (24, 1), (20, 1)], [(15, 1), (30, 1), (26, 1)], [(16, -1), (24, -1), (23, -1)],
  [(16, 1), (30, -1), (28, -1)], [(17, 1), (18, 1)], [(17, -1), (24, 1), (21, 1)],
  [(17, 1), (30, 1), (27, 1)], [(18, -1), (22, -1), (21, -1)], [(18, 1), (30, -1), (27, -1)],
  [(24, 1), (22, 1), (30, 1), (29, 1)]
]
private def d19_10 : RawColumns :=
    d19_10_part0 ++
    d19_10_part1 ++
    d19_10_part2
private def d19_11 : RawColumns := #[
    [(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(4, 1)], [(4, -1)], [(0, -1)], [(1, -1)],
    [(2, -1)], [(3, -1)], [(4, -1)], [(4, 1), (0, 1)], [(3, -1), (0, -1)], [(1, 1), (0, 1)],
    [(4, -1), (1, -1)], [(4, 1), (3, 1)], [(4, -1), (2, -1)], [(4, 1), (2, 1)], [(0, -1)],
    [(1, -1)], [(2, -1)], [(4, -1)], [(3, -1)], [(4, -1)], [(0, 1)], [(1, 1)], [(2, 1)],
    [(3, 1)], [(4, 1)], [(4, 1)]
  ]
private def d19Data : Nat → RawColumns
  | 8 => d19_8
  | 9 => d19_9
  | 10 => d19_10
  | 11 => d19_11
  | _ => #[]

private def d19 (t : Nat) : RawColumns := if t < 13 then d19Data t else #[]

private def p19Data : Nat → RawColumns
  | _ => #[]

private def p19 (t : Nat) : RawColumns := if t < 13 then p19Data t else #[]

private def i19Data : Nat → RawColumns
  | _ => #[]

private def i19 (t : Nat) : RawColumns := if t < 13 then i19Data t else #[]

private def h19_9 : RawColumns := #[
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [(0, 1)],
    [], [], [], [], [], []
  ]
private def h19_10 : RawColumns := #[
    [(1, 1), (22, -1), (23, -1), (24, -1), (25, -1), (26, -1)],
    [(0, -1), (1, -1), (2, -1), (11, -1), (12, -1), (15, 1), (16, 1), (17, 1), (18, 1), (22, 1), (23, 1), (24, 1), (25, 1), (26, 1)],
    [(3, -1), (13, -1), (14, -1), (15, -1), (16, -1), (17, -1), (18, -1), (19, -1), (20, -1)],
    [(4, -1)], [(5, -1), (7, 1), (8, 1), (9, 1), (10, 1), (27, -1)],
    [(6, -1), (7, -1), (8, -1), (9, -1), (10, -1), (27, 1)], [(7, 1), (9, 1), (10, 1), (27, -1)],
    [(9, -1), (10, -1)], [], [], [], [(10, 1)], [], [(7, 1), (8, 1), (9, 1), (10, 1), (27, -1)],
    [], [], [(12, 1)], [(14, 1)], [(16, 1)], [(18, 1)], [(20, 1)], [(23, 1)], [(25, 1)],
    [(0, 1), (1, 1), (7, -1), (8, -1), (9, -1), (10, -1), (22, -1), (23, -1), (24, -1), (25, -1), (26, -1), (27, 1)],
    [(15, -1), (16, -1), (17, -1), (18, -1)], [(17, 1), (18, 1)], [(22, 1), (23, 1)],
    [(22, -1), (23, -1), (24, -1), (25, -1)], [(19, -1), (20, -1)], [], [], [], [], [], [],
    [(22, 1), (23, 1), (24, 1), (25, 1), (26, 1)], [],
    [(0, -1), (1, -1), (7, 1), (8, 1), (9, 1), (10, 1), (11, -1), (12, -1), (15, 1), (16, 1), (17, 1), (18, 1), (22, 1), (23, 1), (24, 1), (25, 1), (26, 1), (27, -1)],
    [], [(13, -1), (14, -1), (15, -1), (16, -1), (17, -1), (18, -1), (19, -1), (20, -1)], [], [],
    [], [], [], [], [], [(27, 1)], [], [], [], [], []
  ]
private def h19_11 : RawColumns := #[
    [(8, -1), (29, -1), (36, -1), (41, 1), (42, 1), (43, 1), (44, 1)],
    [(9, -1), (29, 1), (36, 1), (43, -1), (44, -1)],
    [(10, -1), (29, 1), (36, 1), (48, -1), (49, -1)],
    [(12, -1), (29, 1), (36, 1), (45, 1), (46, 1)],
    [(14, 1), (15, 1), (29, -1), (36, -1), (48, 1), (49, 1), (50, 1), (51, 1), (52, 1)],
    [(14, -1), (29, -1), (36, -1)], [(30, 1)], [(31, 1)], [(32, 1)], [(33, 1)], [(34, 1)],
    [(36, 1)], [(38, 1)], [(40, 1)], [(42, 1)], [(44, 1)], [(46, 1)], [(49, 1)], [(51, 1)],
    [(29, 1), (36, 1), (41, -1), (42, -1), (43, -1), (44, -1)],
    [(29, -1), (36, -1), (43, 1), (44, 1)], [(29, -1), (36, -1), (48, 1), (49, 1)],
    [(29, 1), (36, 1), (48, -1), (49, -1), (50, -1), (51, -1)],
    [(29, -1), (36, -1), (45, -1), (46, -1)], [(29, 1), (36, 1)], [], [], [], [],
    [(29, -2), (36, -2), (48, 1), (49, 1), (50, 1), (51, 1), (52, 1)], []
  ]
private def h19_12 : RawColumns := #[
    [(25, 1)], [(26, 1)], [(27, 1)], [(28, 1)], [(30, 1)]
  ]
private def h19Data : Nat → RawColumns
  | 9 => h19_9
  | 10 => h19_10
  | 11 => h19_11
  | 12 => h19_12
  | _ => #[]

private def h19 (t : Nat) : RawColumns := if t < 13 then h19Data t else #[]

private def rank19 (k : Nat) : Nat := 0

private def cached19 : IntegralRow :=
  ⟨b19, fun t => some (if (d19 t).isEmpty then
    Array.replicate (b19 t).size [] else d19 t)⟩

private def contraction19 : Contraction := ⟨rank19, p19, i19, h19⟩

private theorem basis19_0 : replayStageBasis 19 0 = b19 0 := by decide +kernel
private theorem matrix19_0 :
    calculateMatrix replayResolution (b19 0) (b19 (0 + 1)) =
      cached19.matrix 0 := rfl
private theorem check19_0 : contraction19.check cached19 0 = true := by decide +kernel
private theorem basis19_1 : replayStageBasis 19 1 = b19 1 := by decide +kernel
private theorem matrix19_1 :
    calculateMatrix replayResolution (b19 1) (b19 (1 + 1)) =
      cached19.matrix 1 := rfl
private theorem check19_1 : contraction19.check cached19 1 = true := by decide +kernel
private theorem basis19_2 : replayStageBasis 19 2 = b19 2 := by decide +kernel
private theorem matrix19_2 :
    calculateMatrix replayResolution (b19 2) (b19 (2 + 1)) =
      cached19.matrix 2 := rfl
private theorem check19_2 : contraction19.check cached19 2 = true := by decide +kernel
private theorem basis19_3 : replayStageBasis 19 3 = b19 3 := by decide +kernel
private theorem matrix19_3 :
    calculateMatrix replayResolution (b19 3) (b19 (3 + 1)) =
      cached19.matrix 3 := rfl
private theorem check19_3 : contraction19.check cached19 3 = true := by decide +kernel
private theorem basis19_4 : replayStageBasis 19 4 = b19 4 := by decide +kernel
private theorem matrix19_4 :
    calculateMatrix replayResolution (b19 4) (b19 (4 + 1)) =
      cached19.matrix 4 := rfl
private theorem check19_4 : contraction19.check cached19 4 = true := by decide +kernel
private theorem basis19_5 : replayStageBasis 19 5 = b19 5 := by decide +kernel
private theorem matrix19_5 :
    calculateMatrix replayResolution (b19 5) (b19 (5 + 1)) =
      cached19.matrix 5 := rfl
private theorem check19_5 : contraction19.check cached19 5 = true := by decide +kernel
private theorem basis19_6 : replayStageBasis 19 6 = b19 6 := by decide +kernel
private theorem matrix19_6 :
    calculateMatrix replayResolution (b19 6) (b19 (6 + 1)) =
      cached19.matrix 6 := rfl
private theorem check19_6 : contraction19.check cached19 6 = true := by decide +kernel
private theorem basis19_7 : replayStageBasis 19 7 = b19 7 := by decide +kernel
private theorem matrix19_7 :
    calculateMatrix replayResolution (b19 7) (b19 (7 + 1)) =
      cached19.matrix 7 := rfl
private theorem check19_7 : contraction19.check cached19 7 = true := by decide +kernel
private theorem basis19_8 : replayStageBasis 19 8 = b19 8 := by decide +kernel
private theorem matrix19_8 :
    calculateMatrix replayResolution (b19 8) (b19 (8 + 1)) =
      cached19.matrix 8 := rfl
private theorem check19_8 : contraction19.check cached19 8 = true := by decide +kernel
private theorem basis19_9 : replayStageBasis 19 9 = b19 9 := by decide +kernel
private theorem matrix19_9 :
    calculateMatrix replayResolution (b19 9) (b19 (9 + 1)) =
      cached19.matrix 9 := rfl
private theorem check19_9_block0 :
    contraction19.checkBlock cached19 9 0 = true := by decide +kernel
private theorem check19_9_block1 :
    contraction19.checkBlock cached19 9 1 = true := by decide +kernel
private theorem check19_9_block2 :
    contraction19.checkBlock cached19 9 2 = true := by decide +kernel
private theorem check19_9_block3 :
    contraction19.checkBlock cached19 9 3 = true := by decide +kernel

private theorem check19_9 : contraction19.check cached19 9 = true := by
  apply Contraction.check_of_blocks _ _ _ 4 (by decide) (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact check19_9_block0
  · exact check19_9_block1
  · exact check19_9_block2
  · exact check19_9_block3
private theorem basis19_10 : replayStageBasis 19 10 = b19 10 := by decide +kernel
private theorem matrix19_10_part0 :
    calculateMatrix replayResolution b19_10_part0 (b19 (10 + 1)) =
      some d19_10_part0 := by decide +kernel

private theorem matrix19_10_part1 :
    calculateMatrix replayResolution b19_10_part1 (b19 (10 + 1)) =
      some d19_10_part1 := by decide +kernel

private theorem matrix19_10_part2 :
    calculateMatrix replayResolution b19_10_part2 (b19 (10 + 1)) =
      some d19_10_part2 := by decide +kernel

private theorem matrix19_10 :
    calculateMatrix replayResolution (b19 10) (b19 (10 + 1)) =
      cached19.matrix 10 := by
  change calculateMatrix replayResolution b19_10 (b19 (10 + 1)) = some d19_10
  simp only [b19_10, d19_10, calculateMatrix_append, matrix19_10_part0, matrix19_10_part1, matrix19_10_part2, Option.pure_def]
  rfl
private theorem check19_10_block0 :
    contraction19.checkBlock cached19 10 0 = true := by decide +kernel
private theorem check19_10_block1 :
    contraction19.checkBlock cached19 10 1 = true := by decide +kernel
private theorem check19_10_block2 :
    contraction19.checkBlock cached19 10 2 = true := by decide +kernel
private theorem check19_10_block3 :
    contraction19.checkBlock cached19 10 3 = true := by decide +kernel

private theorem check19_10 : contraction19.check cached19 10 = true := by
  apply Contraction.check_of_blocks _ _ _ 4 (by decide) (by decide) (by decide)
  intro b hb
  interval_cases b
  · exact check19_10_block0
  · exact check19_10_block1
  · exact check19_10_block2
  · exact check19_10_block3
private theorem basis19_11 : replayStageBasis 19 11 = b19 11 := by decide +kernel
private theorem matrix19_11 :
    calculateMatrix replayResolution (b19 11) (b19 (11 + 1)) =
      cached19.matrix 11 := rfl
private theorem check19_11 : contraction19.check cached19 11 = true := by decide +kernel
private theorem basis19_12 : replayStageBasis 19 12 = b19 12 := by decide +kernel
private theorem matrix19_12 :
    calculateMatrix replayResolution (b19 12) (b19 (12 + 1)) =
      cached19.matrix 12 := rfl
private theorem check19_12 : contraction19.check cached19 12 = true := by decide +kernel
private theorem allBasis19 (t : Nat) : replayStageBasis 19 t = b19 t := by
  by_cases ht : t < 13
  · interval_cases t
    · exact basis19_0
    · exact basis19_1
    · exact basis19_2
    · exact basis19_3
    · exact basis19_4
    · exact basis19_5
    · exact basis19_6
    · exact basis19_7
    · exact basis19_8
    · exact basis19_9
    · exact basis19_10
    · exact basis19_11
    · exact basis19_12
  · have ht' : 13 ≤ t := by omega
    cases t with
    | zero => omega
    | succ k =>
      have hk : ¬ k < crossings + 1 := by norm_num [crossings, braid]; omega
      simp only [replayStageBasis, if_neg hk]
      simp [b19, show ¬k + 1 < 13 by omega]
private theorem allMatrix19 (t : Nat) : calculateMatrix replayResolution (b19 t) (b19 (t + 1)) = cached19.matrix t := by
  by_cases ht : t < 13
  · interval_cases t
    · exact matrix19_0
    · exact matrix19_1
    · exact matrix19_2
    · exact matrix19_3
    · exact matrix19_4
    · exact matrix19_5
    · exact matrix19_6
    · exact matrix19_7
    · exact matrix19_8
    · exact matrix19_9
    · exact matrix19_10
    · exact matrix19_11
    · exact matrix19_12
  · have h₀ : b19 t = #[] := by simp [b19, ht]
    have h₁ : d19 t = #[] := by simp [d19, ht]
    simp [cached19, calculateMatrix, h₀, h₁]
private theorem allChecks19 (t : Nat) : contraction19.check cached19 t = true := by
  by_cases ht : t < 13
  · interval_cases t
    · exact check19_0
    · exact check19_1
    · exact check19_2
    · exact check19_3
    · exact check19_4
    · exact check19_5
    · exact check19_6
    · exact check19_7
    · exact check19_8
    · exact check19_9
    · exact check19_10
    · exact check19_11
    · exact check19_12
  · have h₀ : (cached19.basis t).size = 0 := by simp [cached19, b19, ht]
    have h₁ : (cached19.basis (t + 1)).size = 0 := by
      simp [cached19, b19, show ¬ t + 1 < 13 by omega]
    have h₂ : contraction19.rank t = 0 := by
      simp [contraction19, rank19, show t ≠ 7 by omega, show t ≠ 8 by omega]
    exact Contraction.check_empty _ _ _ h₀ h₁ h₂
private theorem cached19_eq : cached19 = integralRow 19 := by
  have hb : replayStageBasis 19 = b19 := funext allBasis19
  have hs := replayStageBasis_eq 19 (by decide)
  have hm : (fun t => (cached19).matrix t) = stageMatrix 19 := by
    funext t
    rw [stageMatrix_eq_replay 19 t (by decide), hb]
    exact (allMatrix19 t).symm
  exact congrArg₂ IntegralRow.mk (hb.symm.trans hs) hm

theorem quantum19_integral : (integralRow 19).Computes
    (fun k => 0) := by
  rw [← cached19_eq]
  exact contraction19.sound _ (fun _ => rfl) allChecks19


end D5.S3.Topology.FourBraidKhovanovCube
