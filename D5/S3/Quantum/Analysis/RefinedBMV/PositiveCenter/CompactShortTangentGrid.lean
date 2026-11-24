/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentGrid
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational coverage of the compact short-gap band for the tangent certificate. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! The adaptive rational cover of `[1/2, 4] × [0, 1]` for the short-gap comparison. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentGrid

/-- The endpoints used to compute the radii of a short-gap box. -/
structure Rectangle where
  uLo : ℚ
  uHi : ℚ
  dLo : ℚ
  dHi : ℚ

/-- A box and its positive tangent root in the normalized `compactZ` coordinates. -/
structure Leaf where
  box : Rectangle
  root : ℚ
  rootPos : 0 < root

/-- Membership in the closed rectangle after casting its endpoints to the reals. -/
def Rectangle.Contains (b : Rectangle) (u d : ℝ) : Prop :=
  (b.uLo : ℝ) ≤ u ∧ u ≤ (b.uHi : ℝ) ∧ (b.dLo : ℝ) ≤ d ∧ d ≤ (b.dHi : ℝ)

/-- Both rational widths are positive and both intervals lie in the short band. -/
def Rectangle.Valid (b : Rectangle) : Prop :=
  (1 / 2 ≤ b.uLo ∧ b.uLo < b.uHi ∧ b.uHi ≤ 4) ∧
    (0 ≤ b.dLo ∧ b.dLo < b.dHi ∧ b.dHi ≤ 1)

private def Rectangle.halves (b : Rectangle) : Rectangle × Rectangle :=
  if b.dHi - b.dLo ≤ b.uHi - b.uLo then
    let mid := (b.uLo + b.uHi) / 2
    ({ b with uHi := mid }, { b with uLo := mid })
  else
    let mid := (b.dLo + b.dHi) / 2
    ({ b with dHi := mid }, { b with dLo := mid })

private theorem Rectangle.contains_halves {b : Rectangle} {u d : ℝ} (hb : b.Contains u d) :
    b.halves.1.Contains u d ∨ b.halves.2.Contains u d := by
  unfold Rectangle.halves
  split
  · by_cases hm : u ≤ (((b.uLo + b.uHi) / 2 : ℚ) : ℝ)
    · exact Or.inl ⟨hb.1, hm, hb.2.2⟩
    · exact Or.inr ⟨le_of_not_ge hm, hb.2⟩
  · by_cases hm : d ≤ (((b.dLo + b.dHi) / 2 : ℚ) : ℝ)
    · exact Or.inl ⟨hb.1, hb.2.1, hb.2.2.1, hm⟩
    · exact Or.inr ⟨hb.1, hb.2.1, le_of_not_ge hm, hb.2.2.2⟩

private theorem Rectangle.valid_halves {b : Rectangle} (hb : b.Valid) :
    b.halves.1.Valid ∧ b.halves.2.Valid := by
  obtain ⟨hu, hd⟩ := hb
  unfold Rectangle.halves
  split
  · have hl : b.uLo < (b.uLo + b.uHi) / 2 := by linarith only [hu.2.1]
    have hr : (b.uLo + b.uHi) / 2 < b.uHi := by linarith only [hu.2.1]
    exact ⟨⟨⟨hu.1, hl, hr.le.trans hu.2.2⟩, hd⟩,
      ⟨⟨hu.1.trans hl.le, hr, hu.2.2⟩, hd⟩⟩
  · have hl : b.dLo < (b.dLo + b.dHi) / 2 := by linarith only [hd.2.1]
    have hr : (b.dLo + b.dHi) / 2 < b.dHi := by linarith only [hd.2.1]
    exact ⟨⟨hu, ⟨hd.1, hl, hr.le.trans hd.2.2⟩⟩,
      ⟨hu, ⟨hd.1.trans hl.le, hr, hd.2.2⟩⟩⟩

private inductive Partition
  | leaf (root : ℚ) (rootPos : 0 < root)
  | split (upper lower : Partition)

private def tangent (root : ℚ) (rootPos : 0 < root := by norm_num) : Partition :=
  .leaf root rootPos

private def Partition.leaves : Partition → Rectangle → List Leaf
  | .leaf root rootPos, b => [⟨b, root, rootPos⟩]
  | .split upper lower, b => upper.leaves b.halves.2 ++ lower.leaves b.halves.1

private theorem Partition.exists_leaf (tree : Partition) {b : Rectangle} {u d : ℝ}
    (hb : b.Contains u d) : ∃ leaf ∈ tree.leaves b, leaf.box.Contains u d := by
  induction tree generalizing b with
  | leaf root rootPos => exact ⟨⟨b, root, rootPos⟩, List.mem_singleton_self _, hb⟩
  | split _ _ ihUpper ihLower =>
    rcases Rectangle.contains_halves hb with hl | hu
    · obtain ⟨leaf, hm, hc⟩ := ihLower hl
      refine ⟨leaf, ?_, hc⟩
      rw [Partition.leaves, List.mem_append]
      exact Or.inr hm
    · obtain ⟨leaf, hm, hc⟩ := ihUpper hu
      refine ⟨leaf, ?_, hc⟩
      rw [Partition.leaves, List.mem_append]
      exact Or.inl hm

private theorem Partition.valid_of_mem (tree : Partition) {b : Rectangle} {leaf : Leaf}
    (hb : b.Valid) (hm : leaf ∈ tree.leaves b) : leaf.box.Valid := by
  induction tree generalizing b with
  | leaf root rootPos =>
    rw [Partition.leaves, List.mem_singleton] at hm
    subst leaf
    exact hb
  | split _ _ ihUpper ihLower =>
    rw [Partition.leaves, List.mem_append] at hm
    obtain ⟨hl, hu⟩ := Rectangle.valid_halves hb
    exact hm.elim (ihUpper hu) (ihLower hl)

private def quarter (a : ℚ) (i : ℕ) : ℚ := a + (i : ℚ) / 4

private theorem cover_quarters (a : ℚ) {x : ℝ} (hLo : (a : ℝ) ≤ x) (n : ℕ)
    (hHi : x ≤ (quarter a (n + 1) : ℝ)) :
    ∃ i : Fin (n + 1), (quarter a i.val : ℝ) ≤ x ∧ x ≤ (quarter a (i.val + 1) : ℝ) := by
  induction n with
  | zero =>
    refine ⟨⟨0, Nat.zero_lt_succ 0⟩, ?_, hHi⟩
    simpa [quarter] using hLo
  | succ n ih =>
    by_cases h : x ≤ (quarter a (n + 1) : ℝ)
    · obtain ⟨i, hiLo, hiHi⟩ := ih h
      exact ⟨i.castSucc, hiLo, hiHi⟩
    · exact ⟨Fin.last (n + 1), le_of_not_ge h, hHi⟩

private theorem quarter_bounds (a : ℚ) {n : ℕ} (i : Fin n) :
    a ≤ quarter a i.val ∧ quarter a i.val < quarter a (i.val + 1) ∧
      quarter a (i.val + 1) ≤ quarter a n := by
  have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  have hiRat : (i.val : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast hi
  have hnonneg : 0 ≤ (i.val : ℚ) := Nat.cast_nonneg _
  simp only [quarter, Nat.cast_add, Nat.cast_one]
  exact ⟨by linarith only [hnonneg], by linarith, by linarith only [hiRat]⟩

private theorem uEnd : quarter (1 / 2) 14 = 4 := by norm_num [quarter]
private theorem dEnd : quarter 0 4 = 1 := by norm_num [quarter]

private def base (i : Fin 14) (j : Fin 4) : Rectangle :=
  ⟨quarter (1 / 2) i.val, quarter (1 / 2) (i.val + 1), quarter 0 j.val, quarter 0 (j.val + 1)⟩

private theorem base_valid (i : Fin 14) (j : Fin 4) : (base i j).Valid := by
  have hu := quarter_bounds (1 / 2) i
  have hd := quarter_bounds 0 j
  rw [uEnd] at hu
  rw [dEnd] at hd
  exact ⟨hu, hd⟩

-- The trees follow central-short-compact-normalized-20261124.jsonl.
-- Both quarter indices descend, and each split visits the higher child first.
private def partitions : Fin 14 → Fin 4 → Partition := ![
  ![ -- u quarter 13
    .split (.split (.split (tangent (457 / 64)) (tangent (1755 / 256))) (tangent (1617 / 256)))
      (.split (.split (tangent (1685 / 256)) (tangent (1619 / 256))) (tangent (1493 / 256))),
    .split (tangent (1395 / 256)) (tangent (645 / 128)),
    tangent (1115 / 256),
    tangent (939 / 256)
  ],
  ![ -- u quarter 12
    .split (.split (tangent (1525 / 256)) (tangent (345 / 64))) (.split (tangent (705 / 128))
      (tangent (1277 / 256))),
    tangent (1151 / 256),
    tangent (963 / 256),
    tangent (51 / 16)
  ],
  ![ -- u quarter 11
    .split (.split (tangent (1305 / 256)) (tangent (37 / 8))) (.split (tangent (605 / 128))
      (tangent (1099 / 256))),
    tangent (497 / 128),
    tangent (209 / 64),
    tangent (357 / 128)
  ],
  ![ -- u quarter 10
    .split (.split (tangent (1123 / 256)) (tangent (511 / 128))) (tangent (997 / 256)),
    tangent (863 / 256),
    tangent (183 / 64),
    tangent (629 / 256)
  ],
  ![ -- u quarter 9
    .split (tangent (929 / 256)) (tangent (867 / 256)),
    tangent (755 / 256),
    tangent (645 / 256),
    tangent (559 / 256)
  ],
  ![ -- u quarter 8
    .split (tangent (811 / 256)) (tangent (95 / 32)),
    tangent (665 / 256),
    tangent (143 / 64),
    tangent (125 / 64)
  ],
  ![ -- u quarter 7
    tangent (173 / 64),
    tangent (591 / 256),
    tangent (2 / 1),
    tangent (451 / 256)
  ],
  ![ -- u quarter 6
    tangent (307 / 128),
    tangent (529 / 256),
    tangent (463 / 256),
    tangent (411 / 256)
  ],
  ![ -- u quarter 5
    tangent (275 / 128),
    tangent (477 / 256),
    tangent (421 / 256),
    tangent (377 / 256)
  ],
  ![ -- u quarter 4
    tangent (31 / 16),
    tangent (435 / 256),
    tangent (387 / 256),
    tangent (175 / 128)
  ],
  ![ -- u quarter 3
    tangent (113 / 64),
    tangent (399 / 256),
    tangent (179 / 128),
    tangent (327 / 256)
  ],
  ![ -- u quarter 2
    tangent (415 / 256),
    tangent (185 / 128),
    tangent (335 / 256),
    tangent (77 / 64)
  ],
  ![ -- u quarter 1
    tangent (385 / 256),
    tangent (173 / 128),
    tangent (79 / 64),
    tangent (293 / 256)
  ],
  ![ -- u quarter 0
    tangent (359 / 256),
    tangent (163 / 128),
    tangent (75 / 64),
    tangent (281 / 256)
  ]
]

/-- The leaves of the coarse cell with lower endpoints `1/2 + i/4` and `j/4`. -/
def leavesAt (i : Fin 14) (j : Fin 4) : List Leaf :=
  (partitions i.rev j.rev).leaves (base i j)

/-- All short-gap leaves in the order of the rational input rows. -/
def leaves : List Leaf :=
  (List.finRange 14).reverse.flatMap fun i ↦
    (List.finRange 4).reverse.flatMap fun j ↦ leavesAt i j

/-- Every short-gap leaf has positive rational widths and lies within the short band. -/
theorem valid_of_mem_leaves {leaf : Leaf} (hm : leaf ∈ leaves) : leaf.box.Valid := by
  simp only [leaves, List.mem_flatMap] at hm
  obtain ⟨i, _, j, _, hij⟩ := hm
  exact (partitions i.rev j.rev).valid_of_mem (base_valid i j) hij

/-- Every real point of the closed short band belongs to a valid leaf. -/
theorem exists_leaf {u d : ℝ} (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4)
    (hdLo : 0 ≤ d) (hdHi : d ≤ 1) :
    ∃ leaf ∈ leaves, leaf.box.Contains u d ∧ leaf.box.Valid := by
  have huTop : u ≤ (quarter (1 / 2) 14 : ℝ) := by
    rw [uEnd]
    exact_mod_cast huHi
  have hdTop : d ≤ (quarter 0 4 : ℝ) := by
    rw [dEnd]
    exact_mod_cast hdHi
  obtain ⟨i, hiLo, hiHi⟩ := cover_quarters (x := u) (1 / 2) (by simpa [Rat.cast_div] using huLo) 13 huTop
  obtain ⟨j, hjLo, hjHi⟩ := cover_quarters (x := d) 0 (by exact_mod_cast hdLo) 3 hdTop
  have hb : (base i j).Contains u d := ⟨hiLo, hiHi, hjLo, hjHi⟩
  obtain ⟨leaf, hm, hc⟩ := (partitions i.rev j.rev).exists_leaf hb
  have hmAll : leaf ∈ leaves := by
    simp only [leaves, List.mem_flatMap, List.mem_reverse]
    exact ⟨i, List.mem_finRange i, j, List.mem_finRange j, hm⟩
  exact ⟨leaf, hmAll, hc, valid_of_mem_leaves hmAll⟩

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentGrid
