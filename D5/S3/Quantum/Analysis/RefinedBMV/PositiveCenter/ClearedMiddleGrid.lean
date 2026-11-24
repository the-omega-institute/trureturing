/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleGrid
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The adaptive rational partition for the cleared central middle certificate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleGrid

/-! Cover the compact middle region by the 39 boxes of the cleared certificate. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open private lowerU upperU lowerD upperD cover_u cover_d from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleGrid

namespace ClearedMiddleGrid

/-- A rational rectangle in the lower coordinate and the gap. -/
structure Rectangle where
  uLo : ℚ
  uHi : ℚ
  dLo : ℚ
  dHi : ℚ

/-- The recorded maximal Bernstein head degree accompanies each leaf. -/
structure Leaf where
  box : Rectangle
  degree : ℕ

/-- Membership in the closed rectangle, with rational endpoints cast to the reals. -/
def Rectangle.Contains (b : Rectangle) (u d : ℝ) : Prop :=
  (b.uLo : ℝ) ≤ u ∧ u ≤ (b.uHi : ℝ) ∧ (b.dLo : ℝ) ≤ d ∧ d ≤ (b.dHi : ℝ)

/-- Both widths are positive and both intervals lie in the compact middle region. -/
def Rectangle.Valid (b : Rectangle) : Prop :=
  (1 / 2 ≤ b.uLo ∧ b.uLo < b.uHi ∧ b.uHi ≤ 4) ∧
    (1 ≤ b.dLo ∧ b.dLo < b.dHi ∧ b.dHi ≤ 4)

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
  | leaf (degree : ℕ)
  | split (left right : Partition)

private def Partition.leaves : Partition → Rectangle → List Leaf
  | .leaf degree, b => [⟨b, degree⟩]
  | .split left right, b => left.leaves b.halves.1 ++ right.leaves b.halves.2

private theorem Partition.exists_leaf (tree : Partition) {b : Rectangle} {u d : ℝ}
    (hb : b.Contains u d) : ∃ leaf ∈ tree.leaves b, leaf.box.Contains u d := by
  induction tree generalizing b with
  | leaf degree => exact ⟨⟨b, degree⟩, by simp [Partition.leaves], hb⟩
  | split _ _ ihLeft ihRight =>
    rcases Rectangle.contains_halves hb with hl | hr
    · obtain ⟨leaf, hm, hc⟩ := ihLeft hl
      refine ⟨leaf, ?_, hc⟩
      rw [Partition.leaves, List.mem_append]
      exact Or.inl hm
    · obtain ⟨leaf, hm, hc⟩ := ihRight hr
      refine ⟨leaf, ?_, hc⟩
      rw [Partition.leaves, List.mem_append]
      exact Or.inr hm

private theorem Partition.valid_of_mem (tree : Partition) {b : Rectangle} {leaf : Leaf}
    (hb : b.Valid) (hm : leaf ∈ tree.leaves b) : leaf.box.Valid := by
  induction tree generalizing b with
  | leaf degree =>
    rw [Partition.leaves, List.mem_singleton] at hm
    subst leaf
    exact hb
  | split _ _ ihLeft ihRight =>
    rw [Partition.leaves, List.mem_append] at hm
    obtain ⟨hl, hr⟩ := Rectangle.valid_halves hb
    exact hm.elim (ihLeft hl) (ihRight hr)

private def base (i : Fin 4) (j : Fin 7) : Rectangle :=
  ⟨lowerU i, upperU i, lowerD j, upperD j⟩

private theorem base_valid (i : Fin 4) (j : Fin 7) : (base i j).Valid := by
  unfold Rectangle.Valid
  constructor
  · fin_cases i <;> norm_num [base, lowerU, upperU]
  · fin_cases j <;> norm_num [base, lowerD, upperD]

-- The trees follow central-middle-cleared-upper-gap-20261124.jsonl.
-- Splits visit the lower half first and favor u on equal widths.
private def partition (i : Fin 4) (j : Fin 7) : Partition :=
  match i.val, j.val with
  | 0, 0 => .split (.split (.leaf 2) (.leaf 2)) (.leaf 2)
  | 0, 2 => .split (.split (.leaf 2) (.leaf 2)) (.leaf 3)
  | 0, 1 | 0, 3 | 0, 4 | 1, 1 | 1, 3 => .split (.leaf 2) (.leaf 2)
  | 1, 0 | 1, 2 => .split (.leaf 3) (.leaf 2)
  | 1, 4 | 3, 0 => .leaf 3
  | 2, 0 => .leaf 4
  | _, _ => .leaf 2

/-- The rational leaf boxes in the order of the recorded certificate. -/
def leaves : List Leaf :=
  (List.finRange 4).flatMap fun i ↦
    (List.finRange 7).flatMap fun j ↦ (partition i j).leaves (base i j)

/-- Every recorded leaf has positive widths and stays inside the compact middle region. -/
theorem valid_of_mem_leaves {leaf : Leaf} (hm : leaf ∈ leaves) : leaf.box.Valid := by
  simp only [leaves, List.mem_flatMap] at hm
  obtain ⟨i, _, j, _, hij⟩ := hm
  exact (partition i j).valid_of_mem (base_valid i j) hij

/-- Every point of the compact middle region belongs to a leaf of the recorded certificate. -/
theorem exists_leaf {u d : ℝ} (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4)
    (hdLo : 1 ≤ d) (hdHi : d ≤ 4) :
    ∃ leaf ∈ leaves, leaf.box.Contains u d := by
  obtain ⟨i, hiLo, hiHi⟩ := cover_u huLo huHi
  obtain ⟨j, hjLo, hjHi⟩ := cover_d hdLo hdHi
  have hb : (base i j).Contains u d := ⟨hiLo, hiHi, hjLo, hjHi⟩
  obtain ⟨leaf, hm, hc⟩ := (partition i j).exists_leaf hb
  refine ⟨leaf, ?_, hc⟩
  simp only [leaves, List.mem_flatMap]
  exact ⟨i, List.mem_finRange i, j, List.mem_finRange j, hm⟩

end ClearedMiddleGrid

end RefinedBMV.PositiveCenter.CompactTaylorModel
