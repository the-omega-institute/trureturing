/- GID: D5/S3/Combinatorics/CrosswordRookCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordRookCounts
   mirror-E: none(waiver:direct-resolution-of-external-open-question)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Square crossword grids realize every natural rook-placement count. -/

import D5.S3.Combinatorics.CrosswordRookCountsDefs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordRookCounts

/-- All white cells in a row belong to its unique across word. -/
theorem white_same_across {r : ℕ} {c d : Cell (gridSize r)}
    (hc : c ∈ white r) (hd : d ∈ white r) (hrow : c.1 = d.1) :
    SameAcross (white r) c d := by
  refine ⟨hrow, ?_⟩
  intro j hjmin hjmax
  simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hc hd ⊢
  have heq : c.1.val = d.1.val := congrArg Fin.val hrow
  rw [← heq] at hd
  rcases le_total c.2 d.2 with hcd | hdc
  · rw [min_eq_left hcd] at hjmin
    rw [max_eq_right hcd] at hjmax
    change c.2.val ≤ j.val at hjmin
    change j.val ≤ d.2.val at hjmax
    omega
  · rw [min_eq_right hdc] at hjmin
    rw [max_eq_left hdc] at hjmax
    change d.2.val ≤ j.val at hjmin
    change j.val ≤ c.2.val at hjmax
    omega

/-- A down word through block `i` cannot cross either black separator. -/
theorem side_word_stays_in_block {r i : ℕ} {c d : Cell (gridSize r)}
    (hrow : 2 * i ≤ c.1.val ∧ c.1.val ≤ 2 * i + 2)
    (hcol : c.2.val = side i) (hdown : SameDown (white r) c d) :
    2 * i ≤ d.1.val ∧ d.1.val ≤ 2 * i + 2 := by
  have hbetween (a : ℕ) (ha : min c.1.val d.1.val ≤ a)
      (hb : a ≤ max c.1.val d.1.val) :
      rowLeft r a ≤ side i ∧ side i ≤ rowRight r a := by
    have hn : a < gridSize r := by
      have hc := c.1.isLt
      have hd := d.1.isLt
      omega
    let x : Fin (gridSize r) := ⟨a, hn⟩
    have hx : (x, c.2) ∈ white r := hdown.2 x (by
      change min c.1.val d.1.val ≤ a
      exact ha) (by
      change a ≤ max c.1.val d.1.val
      exact hb)
    simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [x] at hx
    omega
  constructor
  · by_contra h
    have hlt : d.1.val < 2 * i := by omega
    rcases i with _ | j
    · omega
    · have hgap := hbetween (2 * j + 1) (by omega) (by omega)
      have hblack : ¬ (rowLeft r (2 * j + 1) ≤ side (j + 1) ∧
          side (j + 1) ≤ rowRight r (2 * j + 1)) := by
        have hodd : (2 * j + 1) % 2 = 1 := by omega
        by_cases hj : j % 2 = 0
        · have hnext : (j + 1) % 2 = 1 := by omega
          have hmod : (2 * j + 1) % 4 = 1 := by omega
          simp [rowLeft, rowRight, side, hnext, hodd, hmod]
        · have hnext : (j + 1) % 2 = 0 := by omega
          have hmod : (2 * j + 1) % 4 = 3 := by omega
          simp [rowLeft, rowRight, side, hnext, hodd, hmod]
      exact hblack (by simpa [Nat.succ_eq_add_one] using hgap)
  · by_contra h
    have hgt : 2 * i + 2 < d.1.val := by omega
    have hgap := hbetween (2 * i + 3) (by omega) (by omega)
    have hblack : ¬ (rowLeft r (2 * i + 3) ≤ side i ∧
        side i ≤ rowRight r (2 * i + 3)) := by
      have hodd : (2 * i + 3) % 2 = 1 := by omega
      by_cases hi : i % 2 = 0
      · have hmod : (2 * i + 3) % 4 = 3 := by omega
        simp [rowLeft, rowRight, side, hi, hodd, hmod]
      · have hi' : i % 2 = 1 := by omega
        have hmod : (2 * i + 3) % 4 = 1 := by omega
        simp [rowLeft, rowRight, side, hi, hodd, hmod]
    exact hblack hgap

/-- Every outer tip is a singleton down word. -/
theorem tip_word_is_singleton {r i : ℕ} {c d : Cell (gridSize r)}
    (hrow : c.1.val = 2 * i + 1) (hcol : c.2.val = tip i)
    (hdown : SameDown (white r) c d) : c = d := by
  have hbetween (a : ℕ) (ha : min c.1.val d.1.val ≤ a)
      (hb : a ≤ max c.1.val d.1.val) :
      rowLeft r a ≤ tip i ∧ tip i ≤ rowRight r a := by
    have hn : a < gridSize r := by
      have hc := c.1.isLt
      have hd := d.1.isLt
      omega
    let x : Fin (gridSize r) := ⟨a, hn⟩
    have hx : (x, c.2) ∈ white r := hdown.2 x (by
      change min c.1.val d.1.val ≤ a
      exact ha) (by
      change a ≤ max c.1.val d.1.val
      exact hb)
    simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [x] at hx
    omega
  have hdrow : d.1.val = 2 * i + 1 := by
    have hblack (j : ℕ) :
        ¬ (rowLeft r (2 * j) ≤ tip i ∧ tip i ≤ rowRight r (2 * j)) := by
      have heven : (2 * j) % 2 = 0 := by omega
      have hlo : 1 ≤ rowLeft r (2 * j) := by
        simp [rowLeft, heven]
        split_ifs <;> omega
      have hhi : rowRight r (2 * j) ≤ 3 := by
        simp [rowRight, heven]
        split_ifs <;> omega
      by_cases hi : i % 2 = 0
      · simp [tip, hi] at *
        omega
      · simp [tip, hi] at *
        omega
    by_contra h
    by_cases hlt : d.1.val < 2 * i + 1
    · have hgap := hbetween (2 * i) (by omega) (by omega)
      exact hblack i hgap
    · have hgap := hbetween (2 * (i + 1)) (by omega) (by omega)
      exact hblack (i + 1) hgap
  apply Prod.ext
  · apply Fin.ext
    omega
  · exact hdown.1

/-- Every occupied odd row is exactly its three-cell block interval. -/
theorem odd_row_columns (r i b : ℕ) (hi : i + 1 < r) :
    (2 * i + 1 < 2 * r - 1 ∧
      rowLeft r (2 * i + 1) ≤ b ∧ b ≤ rowRight r (2 * i + 1)) ↔
      b = 2 ∨ b = side i ∨ b = tip i := by
  have hrow : 2 * i + 1 < 2 * r - 1 := by omega
  have hodd : (2 * i + 1) % 2 = 1 := by omega
  by_cases heven : i % 2 = 0
  · have hmod : (2 * i + 1) % 4 = 1 := by omega
    simp [rowLeft, rowRight, side, tip, heven, hodd, hmod, hrow]
    omega
  · have hmod : (2 * i + 1) % 4 = 3 := by omega
    simp [rowLeft, rowRight, side, tip, heven, hodd, hmod, hrow]
    omega

/-- An even row meets the central word and the incident side words. -/
theorem even_row_columns (r j b : ℕ) (hj : j < r) :
    (2 * j < 2 * r - 1 ∧
      rowLeft r (2 * j) ≤ b ∧ b ≤ rowRight r (2 * j)) ↔
      b = 2 ∨ (0 < j ∧ b = side (j - 1)) ∨
        (j + 1 < r ∧ b = side j) := by
  have hrow : 2 * j < 2 * r - 1 := by omega
  rcases j with _ | m
  · by_cases hr : r = 1
    · simp [rowLeft, rowRight, side, hr]
      omega
    · have hr' : 1 < r := by omega
      have hneq : 0 ≠ 2 * r - 2 := by omega
      simp [rowLeft, rowRight, side, hneq, hr']
      omega
  · have heven : (2 * (m + 1)) % 2 = 0 := by omega
    have hne0 : 2 * (m + 1) ≠ 0 := by omega
    have hend : 2 * (m + 1) = 2 * r - 2 ↔ m + 2 = r := by omega
    by_cases hm : m % 2 = 0
    · have hmnext : (m + 1) % 2 = 1 := by omega
      have hmod : (2 * (m + 1)) % 4 = 2 := by omega
      by_cases hlast : m + 2 = r
      · simp [rowLeft, rowRight, side, heven, hne0, hend, hlast,
          hm, hmnext, hmod, hrow]
        omega
      · have hmore : m + 2 < r := by omega
        simp [rowLeft, rowRight, side, heven, hne0, hend, hlast,
          hm, hmnext, hmod, hmore, hrow]
        omega
    · have hmnext : (m + 1) % 2 = 0 := by omega
      have hmod : (2 * (m + 1)) % 4 = 0 := by omega
      by_cases hlast : m + 2 = r
      · simp [rowLeft, rowRight, side, heven, hne0, hend, hlast,
          hm, hmnext, hmod, hrow]
        omega
      · have hmore : m + 2 < r := by omega
        simp [rowLeft, rowRight, side, heven, hne0, hend, hlast,
          hm, hmnext, hmod, hmore, hrow]
        omega

/-- The interval description has precisely the spine, side runs, and tips of the report. -/
theorem white_iff_pattern {r : ℕ} (c : Cell (gridSize r)) :
    c ∈ white r ↔
      (c.1.val < 2 * r - 1 ∧ c.2.val = 2) ∨
      (∃ i : ℕ, i + 1 < r ∧ c.2.val = side i ∧
        2 * i ≤ c.1.val ∧ c.1.val ≤ 2 * i + 2) ∨
      (∃ i : ℕ, i + 1 < r ∧ c.1.val = 2 * i + 1 ∧ c.2.val = tip i) := by
  simp only [white, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hc
    by_cases hpar : c.1.val % 2 = 0
    · let j := c.1.val / 2
      have hrow : c.1.val = 2 * j := by omega
      have hj : j < r := by omega
      have he := (even_row_columns r j c.2.val hj).mp (by simpa [hrow] using hc)
      rcases he with htwo | ⟨hpos, hside⟩ | ⟨hnext, hside⟩
      · exact Or.inl ⟨hc.1, htwo⟩
      · right; left
        refine ⟨j - 1, by omega, hside, ?_, ?_⟩ <;> omega
      · right; left
        exact ⟨j, hnext, hside, by omega, by omega⟩
    · let i := c.1.val / 2
      have hrow : c.1.val = 2 * i + 1 := by omega
      have hi : i + 1 < r := by omega
      have ho := (odd_row_columns r i c.2.val hi).mp (by simpa [hrow] using hc)
      rcases ho with htwo | hside | htip
      · exact Or.inl ⟨hc.1, htwo⟩
      · exact Or.inr (Or.inl ⟨i, hi, hside, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨i, hi, hrow, htip⟩)
  · rintro (⟨hrow, htwo⟩ | ⟨i, hi, hside, hlo, hhi⟩ | ⟨i, hi, hrow, htip⟩)
    · by_cases hpar : c.1.val % 2 = 0
      · let j := c.1.val / 2
        have heq : c.1.val = 2 * j := by omega
        have hj : j < r := by omega
        have he := (even_row_columns r j c.2.val hj).mpr (Or.inl htwo)
        simpa [heq] using he
      · let i := c.1.val / 2
        have heq : c.1.val = 2 * i + 1 := by omega
        have hi : i + 1 < r := by omega
        have ho := (odd_row_columns r i c.2.val hi).mpr (Or.inl htwo)
        simpa [heq] using ho
    · have hcases : c.1.val = 2 * i ∨ c.1.val = 2 * i + 1 ∨
          c.1.val = 2 * i + 2 := by omega
      rcases hcases with htop | hmid | hbot
      · have he := (even_row_columns r i c.2.val (by omega)).mpr
          (Or.inr (Or.inr ⟨hi, hside⟩))
        simpa [htop] using he
      · have ho := (odd_row_columns r i c.2.val hi).mpr
          (Or.inr (Or.inl hside))
        simpa [hmid] using ho
      · have he := (even_row_columns r (i + 1) c.2.val (by omega)).mpr
          (Or.inr (Or.inl ⟨by omega, by simpa using hside⟩))
        have hmul : 2 * (i + 1) = 2 * i + 2 := by omega
        rw [hmul] at he
        simpa [hbot] using he
    · have ho := (odd_row_columns r i c.2.val hi).mpr
        (Or.inr (Or.inr htip))
      simpa [hrow] using ho

/-- The down words are the central spine, one three-cell word per block, and singleton tips. -/
theorem same_down_iff {r : ℕ} {c d : Cell (gridSize r)}
    (hc : c ∈ white r) (hd : d ∈ white r) :
    SameDown (white r) c d ↔
      (c.2.val = 2 ∧ d.2.val = 2) ∨
      (∃ i : ℕ, i + 1 < r ∧ c.2.val = side i ∧ d.2.val = side i ∧
        2 * i ≤ c.1.val ∧ c.1.val ≤ 2 * i + 2 ∧
        2 * i ≤ d.1.val ∧ d.1.val ≤ 2 * i + 2) ∨
      c = d := by
  constructor
  · intro hdown
    rcases (white_iff_pattern c).mp hc with ⟨_, htwo⟩ |
        ⟨i, hi, hside, hlow, hhigh⟩ | ⟨i, hi, hrow, htip⟩
    · left
      exact ⟨htwo, by simpa [← hdown.1] using htwo⟩
    · right; left
      have hlocal := side_word_stays_in_block ⟨hlow, hhigh⟩ hside hdown
      exact ⟨i, hi, hside, by simpa [← hdown.1] using hside,
        hlow, hhigh, hlocal.1, hlocal.2⟩
    · exact Or.inr (Or.inr (tip_word_is_singleton hrow htip hdown))
  · rintro (⟨hc2, hd2⟩ |
        ⟨i, hi, hcs, hds, hcl, hch, hdl, hdh⟩ | heq)
    · refine ⟨Fin.ext (by omega), ?_⟩
      intro a ha hb
      change min c.1.val d.1.val ≤ a.val at ha
      change a.val ≤ max c.1.val d.1.val at hb
      have hcr : c.1.val < 2 * r - 1 := by
        simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact hc.1
      have hdr : d.1.val < 2 * r - 1 := by
        simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hd
        exact hd.1
      apply (white_iff_pattern (a, c.2)).mpr
      left
      constructor
      · have hu : max c.1.val d.1.val ≤ 2 * r - 2 := max_le (by omega) (by omega)
        change a.val < 2 * r - 1
        omega
      · exact hc2
    · refine ⟨Fin.ext (by omega), ?_⟩
      intro a ha hb
      change min c.1.val d.1.val ≤ a.val at ha
      change a.val ≤ max c.1.val d.1.val at hb
      have hl : 2 * i ≤ min c.1.val d.1.val := le_min hcl hdl
      have hu : max c.1.val d.1.val ≤ 2 * i + 2 := max_le hch hdh
      apply (white_iff_pattern (a, c.2)).mpr
      right; left
      refine ⟨i, hi, hcs, ?_, ?_⟩
      · change 2 * i ≤ a.val
        omega
      · change a.val ≤ 2 * i + 2
        omega
    · subst d
      refine ⟨rfl, ?_⟩
      intro a ha hb
      have heq : a = c.1 := by
        apply Fin.ext
        change min c.1.val c.1.val ≤ a.val at ha
        change a.val ≤ max c.1.val c.1.val at hb
        omega
      simpa [heq] using hc

/-- A proposed placement chooses exactly one cell in each occupied row. -/
theorem candidate_row_unique {r k : ℕ} {c d : Cell (gridSize r)}
    (hc : c ∈ candidate r k) (hd : d ∈ candidate r k)
    (hrow : c.1 = d.1) : c = d := by
  simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and] at hc hd
  apply Prod.ext hrow
  apply Fin.ext
  have hv : c.1.val = d.1.val := congrArg Fin.val hrow
  rcases hc with ⟨hcr, hcc⟩ | ⟨i, hi, hcr, hcc⟩ |
      ⟨i, hi, hcc, (⟨hik, hcr⟩ | ⟨hki, hcr⟩)⟩ <;>
    rcases hd with ⟨hdr, hdc⟩ | ⟨j, hj, hdr, hdc⟩ |
      ⟨j, hj, hdc, (⟨hjk, hdr⟩ | ⟨hkj, hdr⟩)⟩ <;>
    first
    | omega
    | (have hij : i = j := by omega
       subst j
       simpa [hcc] using hdc.symm)

/-- A candidate rook in a side word is the endpoint selected for that block. -/
theorem candidate_side_choice {r k i : ℕ} {c : Cell (gridSize r)}
    (hc : c ∈ candidate r k) (hcol : c.2.val = side i)
    (hrow : 2 * i ≤ c.1.val ∧ c.1.val ≤ 2 * i + 2) :
    (i < k ∧ c.1.val = 2 * i) ∨
      (k ≤ i ∧ c.1.val = 2 * i + 2) := by
  simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases hc with ⟨hcr, hcc⟩ | ⟨j, hj, hcr, hcc⟩ |
      ⟨j, hj, hcc, (⟨hjk, hcr⟩ | ⟨hkj, hcr⟩)⟩
  · have hs : side i = 1 ∨ side i = 3 := by
      simp [side]; omega
    omega
  · have ht : tip j = 0 ∨ tip j = 4 := by
      simp [tip]; omega
    have hs : side i = 1 ∨ side i = 3 := by
      simp [side]; omega
    omega
  · have hij : i = j := by
      by_cases hpi : i % 2 = 0 <;> by_cases hpj : j % 2 = 0
      all_goals simp [side, hpi, hpj] at hcol hcc
      all_goals omega
    subst j
    exact Or.inl ⟨hjk, hcr⟩
  · have hij : i = j := by
      by_cases hpi : i % 2 = 0 <;> by_cases hpj : j % 2 = 0
      all_goals simp [side, hpi, hpj] at hcol hcc
      all_goals omega
    subst j
    exact Or.inr ⟨hkj, hcr⟩

/-- The candidate indexed by `k` meets every occupied across word. -/
theorem candidate_row_exists {r k : ℕ} (hk : k < r)
    (a : Fin (gridSize r)) (ha : a.val < 2 * r - 1) :
    ∃ d ∈ candidate r k, d.1 = a := by
  have hside (i : ℕ) : side i < gridSize r := by
    have hs : side i = 1 ∨ side i = 3 := by simp [side]; omega
    simp [gridSize]
    omega
  have htip (i : ℕ) : tip i < gridSize r := by
    have ht : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
    simp [gridSize]
    omega
  by_cases heven : a.val % 2 = 0
  · let j := a.val / 2
    have hrow : a.val = 2 * j := by omega
    have hj : j < r := by omega
    rcases lt_trichotomy j k with hlt | heq | hgt
    · let d : Cell (gridSize r) := (a, ⟨side j, hside j⟩)
      refine ⟨d, ?_, rfl⟩
      simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr (Or.inr ⟨j, by omega, rfl, Or.inl ⟨hlt, hrow⟩⟩)
    · have htwo : 2 < gridSize r := by simp [gridSize]
      let d : Cell (gridSize r) := (a, ⟨2, htwo⟩)
      refine ⟨d, ?_, rfl⟩
      simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨by change a.val = 2 * k; omega, rfl⟩
    · let d : Cell (gridSize r) := (a, ⟨side (j - 1), hside (j - 1)⟩)
      refine ⟨d, ?_, rfl⟩
      simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
      right; right
      refine ⟨j - 1, by omega, rfl, Or.inr ⟨by omega, ?_⟩⟩
      change a.val = 2 * (j - 1) + 2
      omega
  · let i := a.val / 2
    have hrow : a.val = 2 * i + 1 := by omega
    have hi : i + 1 < r := by omega
    let d : Cell (gridSize r) := (a, ⟨tip i, htip i⟩)
    refine ⟨d, ?_, rfl⟩
    simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl ⟨i, hi, hrow, rfl⟩)

private def gridPoint (r a b : ℕ) (ha : a < 2 * r - 1) (hb : b ≤ 4) :
    Cell (gridSize r) :=
  (⟨a, by simp [gridSize]; omega⟩, ⟨b, by simp [gridSize]; omega⟩)

/-- Each down word contains the cell selected by the candidate placement. -/
theorem candidate_down_exists {r k : ℕ} (hk : k < r)
    (c : Cell (gridSize r)) (hc : c ∈ white r) :
    ∃ d ∈ candidate r k, SameDown (white r) c d := by
  rcases (white_iff_pattern c).mp hc with ⟨hcr, hcc⟩ |
      ⟨i, hi, hcc, hcl, hch⟩ | ⟨i, hi, hcr, hcc⟩
  · let d := gridPoint r (2 * k) 2 (by omega) (by omega)
    have hd : d ∈ candidate r k := by
      simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨rfl, rfl⟩
    have hdw : d ∈ white r :=
      (white_iff_pattern d).mpr (Or.inl ⟨by dsimp [d, gridPoint]; omega, rfl⟩)
    refine ⟨d, hd, (same_down_iff hc hdw).mpr ?_⟩
    exact Or.inl ⟨hcc, rfl⟩
  · have hs : side i ≤ 4 := by
      have hh : side i = 1 ∨ side i = 3 := by simp [side]; omega
      omega
    by_cases hik : i < k
    · let d := gridPoint r (2 * i) (side i) (by omega) hs
      have hd : d ∈ candidate r k := by
        simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr (Or.inr ⟨i, hi, rfl, Or.inl ⟨hik, rfl⟩⟩)
      have hdw : d ∈ white r :=
        (white_iff_pattern d).mpr
          (Or.inr (Or.inl ⟨i, hi, rfl, by dsimp [d, gridPoint]; omega,
            by dsimp [d, gridPoint]; omega⟩))
      refine ⟨d, hd, (same_down_iff hc hdw).mpr ?_⟩
      exact Or.inr (Or.inl ⟨i, hi, hcc, rfl, hcl, hch,
        by dsimp [d, gridPoint]; omega, by dsimp [d, gridPoint]; omega⟩)
    · let d := gridPoint r (2 * i + 2) (side i) (by omega) hs
      have hd : d ∈ candidate r k := by
        simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr (Or.inr ⟨i, hi, rfl, Or.inr ⟨by omega, rfl⟩⟩)
      have hdw : d ∈ white r :=
        (white_iff_pattern d).mpr
          (Or.inr (Or.inl ⟨i, hi, rfl, by dsimp [d, gridPoint]; omega,
            by dsimp [d, gridPoint]; omega⟩))
      refine ⟨d, hd, (same_down_iff hc hdw).mpr ?_⟩
      exact Or.inr (Or.inl ⟨i, hi, hcc, rfl, hcl, hch,
        by dsimp [d, gridPoint]; omega, by dsimp [d, gridPoint]; omega⟩)
  · have hd : c ∈ candidate r k := by
      simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr (Or.inl ⟨i, hi, hcr, hcc⟩)
    exact ⟨c, hd, (same_down_iff hc hc).mpr (Or.inr (Or.inr rfl))⟩

/-- Each index `k < r` yields a complete non-attacking rook placement. -/
theorem candidate_is_placement {r k : ℕ} (hk : k < r) :
    IsRookPlacement (white r) (candidate r k) := by
  have hsubset : candidate r k ⊆ white r := by
    intro c hc
    simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    apply (white_iff_pattern c).mpr
    rcases hc with ⟨hrow, hcol⟩ | ⟨i, hi, hrow, hcol⟩ |
        ⟨i, hi, hcol, (⟨hik, hrow⟩ | ⟨hki, hrow⟩)⟩
    · exact Or.inl ⟨by omega, hcol⟩
    · exact Or.inr (Or.inr ⟨i, hi, hrow, hcol⟩)
    · exact Or.inr (Or.inl ⟨i, hi, hcol, by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨i, hi, hcol, by omega, by omega⟩)
  have hcentral (x : Cell (gridSize r)) (hx : x ∈ candidate r k)
      (hxcol : x.2.val = 2) : x.1.val = 2 * k := by
    simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨hrow, _⟩ | ⟨i, _, _, hcol⟩ | ⟨i, _, hcol, _⟩
    · exact hrow
    · have ht : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
      omega
    · have hs : side i = 1 ∨ side i = 3 := by simp [side]; omega
      omega
  refine ⟨hsubset, ?_, ?_⟩
  · intro c hc d hd hne
    constructor
    · intro hacross
      exact hne (candidate_row_unique hc hd hacross.1)
    · intro hdown
      rcases (same_down_iff (hsubset hc) (hsubset hd)).mp hdown with
          hspine | hside | heq
      · apply hne
        apply Prod.ext
        · apply Fin.ext
          have hcr := hcentral c hc hspine.1
          have hdr := hcentral d hd hspine.2
          omega
        · exact hdown.1
      · rcases hside with ⟨i, _, hcc, _, hcl, hch, hdl, hdh⟩
        have hcx := candidate_side_choice hc hcc ⟨hcl, hch⟩
        have hdx := candidate_side_choice hd (by simpa [hdown.1] using hcc)
          ⟨hdl, hdh⟩
        apply hne
        apply Prod.ext
        · apply Fin.ext
          rcases hcx with ⟨hik, hcr⟩ | ⟨hki, hcr⟩ <;>
            rcases hdx with ⟨_, hdr⟩ | ⟨_, hdr⟩ <;> omega
        · exact hdown.1
      · exact hne heq
  · intro c hc
    constructor
    · have hcr : c.1.val < 2 * r - 1 := by
        simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact hc.1
      obtain ⟨d, hd, hrow⟩ := candidate_row_exists hk c.1 hcr
      exact ⟨d, hd, white_same_across hc (hsubset hd) hrow.symm⟩
    · exact candidate_down_exists hk c hc

/-- Every side word before the central rook uses its top endpoint. -/
theorem placement_top_before_central {r k : ℕ} {R : Finset (Cell (gridSize r))}
    (hR : IsRookPlacement (white r) R)
    (u : Cell (gridSize r)) (hu : u ∈ R)
    (hurow : u.1.val = 2 * k) (hucol : u.2.val = 2) :
    ∀ i : ℕ, i + 1 < r → i < k →
      ∃ d ∈ R, d.1.val = 2 * i ∧ d.2.val = side i := by
  have down_unique {c d : Cell (gridSize r)} (hc : c ∈ R) (hd : d ∈ R)
      (hdown : SameDown (white r) c d) : c = d := by
    by_contra hne
    exact (hR.2.1 c hc d hd hne).2 hdown
  have hstep (i : ℕ) (hi : i + 1 < r) (hik : i < k)
      (hprev : i = 0 ∨
        ∃ p ∈ R, p.1.val = 2 * (i - 1) ∧ p.2.val = side (i - 1)) :
      ∃ d ∈ R, d.1.val = 2 * i ∧ d.2.val = side i := by
    let p := gridPoint r (2 * i) 2 (by omega) (by omega)
    have hp : p ∈ white r :=
      (white_iff_pattern p).mpr (Or.inl ⟨by dsimp [p, gridPoint]; omega, rfl⟩)
    obtain ⟨q, hq, hacross⟩ := (hR.2.2 p hp).1
    have hqrow : q.1.val = 2 * i := by rw [← hacross.1]; rfl
    have hqw := hR.1 hq
    simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at hqw
    have hqcols := (even_row_columns r i q.2.val (by omega)).mp (by
      rw [hqrow] at hqw
      exact hqw)
    rcases hqcols with hcentral | ⟨hipos, hprevious⟩ | ⟨_, hcurrent⟩
    · have hdown : SameDown (white r) q u :=
        (same_down_iff (hR.1 hq) (hR.1 hu)).mpr
          (Or.inl ⟨hcentral, hucol⟩)
      have heq := down_unique hq hu hdown
      have hrows : q.1.val = u.1.val :=
        congrArg (fun x : Cell (gridSize r) => x.1.val) heq
      omega
    · rcases hprev with hzero | ⟨p, hp, hprow, hpcol⟩
      · omega
      · have hdown : SameDown (white r) q p :=
          (same_down_iff (hR.1 hq) (hR.1 hp)).mpr
            (Or.inr (Or.inl ⟨i - 1, by omega, hprevious, hpcol,
              by omega, by omega, by omega, by omega⟩))
        have heq := down_unique hq hp hdown
        have hrows : q.1.val = p.1.val :=
          congrArg (fun x : Cell (gridSize r) => x.1.val) heq
        omega
    · exact ⟨q, hq, hqrow, hcurrent⟩
  intro i
  induction i with
  | zero =>
      intro hi hik
      exact hstep 0 hi hik (Or.inl rfl)
  | succ m ih =>
      intro hi hik
      obtain ⟨p, hp, hprow, hpcol⟩ := ih (by omega) (by omega)
      apply hstep (m + 1) hi hik
      right
      refine ⟨p, hp, ?_, ?_⟩
      · simpa using hprow
      · simpa using hpcol

/-- Every side word from the central rook onward uses its bottom endpoint. -/
theorem placement_bottom_after_central {r k : ℕ} {R : Finset (Cell (gridSize r))}
    (hR : IsRookPlacement (white r) R)
    (u : Cell (gridSize r)) (hu : u ∈ R)
    (hurow : u.1.val = 2 * k) (hucol : u.2.val = 2) :
    ∀ i : ℕ, i + 1 < r → k ≤ i →
      ∃ d ∈ R, d.1.val = 2 * i + 2 ∧ d.2.val = side i := by
  have hstep (i : ℕ) (hi : i + 1 < r)
      (q : Cell (gridSize r)) (hq : q ∈ R)
      (hqrow : q.1.val = 2 * i) (hqcol : q.2.val ≠ side i) :
      ∃ d ∈ R, d.1.val = 2 * i + 2 ∧ d.2.val = side i := by
    have hs : side i ≤ 4 := by
      have hh : side i = 1 ∨ side i = 3 := by simp [side]; omega
      omega
    let p := gridPoint r (2 * i + 1) (side i) (by omega) hs
    have hp : p ∈ white r :=
      (white_iff_pattern p).mpr
        (Or.inr (Or.inl ⟨i, hi, rfl, by dsimp [p, gridPoint]; omega,
          by dsimp [p, gridPoint]; omega⟩))
    obtain ⟨d, hd, hdown⟩ := (hR.2.2 p hp).2
    have hlocal := side_word_stays_in_block
      (c := p) (d := d) (by dsimp [p, gridPoint]; omega) rfl hdown
    have hdcol : d.2.val = side i := by rw [← hdown.1]; rfl
    have hrow : d.1.val = 2 * i ∨ d.1.val = 2 * i + 2 := by
      have hcases : d.1.val = 2 * i ∨ d.1.val = 2 * i + 1 ∨
          d.1.val = 2 * i + 2 := by omega
      rcases hcases with htop | hmid | hbot
      · exact Or.inl htop
      · have ht : tip i ≤ 4 := by
          have hh : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
          omega
        let t := gridPoint r (2 * i + 1) (tip i) (by omega) ht
        have htwhite : t ∈ white r :=
          (white_iff_pattern t).mpr (Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩))
        obtain ⟨e, he, hed⟩ := (hR.2.2 t htwhite).2
        have hte : t = e := tip_word_is_singleton rfl rfl hed
        have htR : t ∈ R := by simpa [hte] using he
        have htrow : t.1.val = 2 * i + 1 := rfl
        have htcol : t.2.val = tip i := rfl
        have hne : d ≠ t := by
          intro heq
          have hcols : d.2.val = t.2.val :=
            congrArg (fun x : Cell (gridSize r) => x.2.val) heq
          have htip : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
          have hside : side i = 1 ∨ side i = 3 := by simp [side]; omega
          omega
        have hacross : SameAcross (white r) d t :=
          white_same_across (hR.1 hd) (hR.1 htR) (Fin.ext (by omega))
        exact ((hR.2.1 d hd t htR hne).1 hacross).elim
      · exact Or.inr hbot
    rcases hrow with htop | hbot
    · have heq : d = q := by
        by_contra hne
        exact (hR.2.1 d hd q hq hne).1
          (white_same_across (hR.1 hd) (hR.1 hq) (Fin.ext (by omega)))
      have hcols : d.2.val = q.2.val :=
        congrArg (fun x : Cell (gridSize r) => x.2.val) heq
      exact (hqcol (by omega)).elim
    · exact ⟨d, hd, hbot, hdcol⟩
  have hflip (i : ℕ) : side (i + 1) ≠ side i := by
    by_cases hi : i % 2 = 0
    · have hi' : (i + 1) % 2 = 1 := by omega
      simp [side, hi, hi']
    · have hi' : (i + 1) % 2 = 0 := by omega
      simp [side, hi, hi']
  intro i
  induction i with
  | zero =>
      intro hi hki
      have hk0 : k = 0 := by omega
      have hurow0 : u.1.val = 0 := by omega
      have hne : u.2.val ≠ side 0 := by simp [side]; omega
      exact hstep 0 hi u hu hurow0 hne
  | succ m ih =>
      intro hi hki
      by_cases hkm : k = m + 1
      · have hqrow : u.1.val = 2 * (m + 1) := by omega
        have hne : u.2.val ≠ side (m + 1) := by
          have hs : side (m + 1) = 1 ∨ side (m + 1) = 3 := by
            simp [side]; omega
          omega
        exact hstep (m + 1) hi u hu hqrow hne
      · obtain ⟨p, hp, hprow, hpcol⟩ := ih (by omega) (by omega)
        have hqrow : p.1.val = 2 * (m + 1) := by omega
        have hne : p.2.val ≠ side (m + 1) := by
          rw [hpcol]
          exact (hflip m).symm
        exact hstep (m + 1) hi p hp hqrow hne

/-- Every valid placement is the uniquely indexed candidate determined by its central rook. -/
theorem placement_eq_candidate {r : ℕ} {R : Finset (Cell (gridSize r))}
    (hr : 0 < r) (hR : IsRookPlacement (white r) R) :
    ∃ k : ℕ, k < r ∧ R = candidate r k := by
  have tip_forced (i : ℕ) (hi : i + 1 < r) :
      ∃ d ∈ R, d.1.val = 2 * i + 1 ∧ d.2.val = tip i := by
    have ht : tip i ≤ 4 := by
      have hh : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
      omega
    let p := gridPoint r (2 * i + 1) (tip i) (by omega) ht
    have hp : p ∈ white r :=
      (white_iff_pattern p).mpr (Or.inr (Or.inr ⟨i, hi, rfl, rfl⟩))
    obtain ⟨d, hd, hdown⟩ := (hR.2.2 p hp).2
    have heq : p = d := tip_word_is_singleton rfl rfl hdown
    refine ⟨p, ?_, rfl, rfl⟩
    simpa [heq] using hd
  let p := gridPoint r 0 2 (by omega) (by omega)
  have hp : p ∈ white r :=
    (white_iff_pattern p).mpr (Or.inl ⟨by dsimp [p, gridPoint]; omega, rfl⟩)
  obtain ⟨u, hu, hdown⟩ := (hR.2.2 p hp).2
  have hucol : u.2.val = 2 := by rw [← hdown.1]; rfl
  have huwhite := hR.1 hu
  have hurow_bound : u.1.val < 2 * r - 1 := by
    simp only [white, Finset.mem_filter, Finset.mem_univ, true_and] at huwhite
    exact huwhite.1
  have hueven : u.1.val % 2 = 0 := by
    by_contra hodd
    let i := u.1.val / 2
    have hirow : u.1.val = 2 * i + 1 := by omega
    have hi : i + 1 < r := by omega
    obtain ⟨t, ht, htrow, htcol⟩ := tip_forced i hi
    by_cases heq : u = t
    · have hcols : u.2.val = t.2.val :=
        congrArg (fun x : Cell (gridSize r) => x.2.val) heq
      have htip : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
      omega
    · have hacross : SameAcross (white r) u t :=
        white_same_across (hR.1 hu) (hR.1 ht) (Fin.ext (by omega))
      exact ((hR.2.1 u hu t ht heq).1 hacross).elim
  let k := u.1.val / 2
  have hurow : u.1.val = 2 * k := by omega
  have hk : k < r := by omega
  have htop := placement_top_before_central hR u hu hurow hucol
  have hbottom := placement_bottom_after_central hR u hu hurow hucol
  have down_unique {c d : Cell (gridSize r)} (hc : c ∈ R) (hd : d ∈ R)
      (hdown : SameDown (white r) c d) : c = d := by
    by_contra hne
    exact (hR.2.1 c hc d hd hne).2 hdown
  have same_coords {c d : Cell (gridSize r)}
      (hrow : c.1.val = d.1.val) (hcol : c.2.val = d.2.val) : c = d :=
    Prod.ext (Fin.ext hrow) (Fin.ext hcol)
  refine ⟨k, hk, ?_⟩
  apply Finset.Subset.antisymm
  · intro c hc
    have hcwhite := hR.1 hc
    simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases (white_iff_pattern c).mp hcwhite with ⟨_, hc2⟩ |
        ⟨i, hi, hcs, hcl, hch⟩ | ⟨i, hi, hcr, hct⟩
    · have hdown : SameDown (white r) c u :=
        (same_down_iff hcwhite (hR.1 hu)).mpr (Or.inl ⟨hc2, hucol⟩)
      have heq := down_unique hc hu hdown
      exact Or.inl ⟨by rw [heq]; exact hurow, hc2⟩
    · by_cases hik : i < k
      · obtain ⟨d, hd, hdrow, hdcol⟩ := htop i hi hik
        have hdown : SameDown (white r) c d :=
          (same_down_iff hcwhite (hR.1 hd)).mpr
            (Or.inr (Or.inl ⟨i, hi, hcs, hdcol, hcl, hch,
              by omega, by omega⟩))
        have heq := down_unique hc hd hdown
        exact Or.inr (Or.inr ⟨i, hi, hcs, Or.inl ⟨hik,
          by rw [heq]; exact hdrow⟩⟩)
      · obtain ⟨d, hd, hdrow, hdcol⟩ := hbottom i hi (by omega)
        have hdown : SameDown (white r) c d :=
          (same_down_iff hcwhite (hR.1 hd)).mpr
            (Or.inr (Or.inl ⟨i, hi, hcs, hdcol, hcl, hch,
              by omega, by omega⟩))
        have heq := down_unique hc hd hdown
        exact Or.inr (Or.inr ⟨i, hi, hcs, Or.inr ⟨by omega,
          by rw [heq]; exact hdrow⟩⟩)
    · exact Or.inr (Or.inl ⟨i, hi, hcr, hct⟩)
  · intro c hc
    simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨hcr, hcc⟩ | ⟨i, hi, hcr, hcc⟩ |
        ⟨i, hi, hcc, (⟨hik, hcr⟩ | ⟨hki, hcr⟩)⟩
    · have heq : c = u := same_coords (by omega) (by omega)
      simpa [heq] using hu
    · obtain ⟨d, hd, hdrow, hdcol⟩ := tip_forced i hi
      have heq : c = d := same_coords (by omega) (by omega)
      simpa [heq] using hd
    · obtain ⟨d, hd, hdrow, hdcol⟩ := htop i hi hik
      have heq : c = d := same_coords (by omega) (by omega)
      simpa [heq] using hd
    · obtain ⟨d, hd, hdrow, hdcol⟩ := hbottom i hi hki
      have heq : c = d := same_coords (by omega) (by omega)
      simpa [heq] using hd

/-- Different central rows give different placements. -/
theorem candidate_injective {r k l : ℕ} (hk : k < r) (hl : l < r)
    (heq : candidate r k = candidate r l) : k = l := by
  let p := gridPoint r (2 * k) 2 (by omega) (by omega)
  have hp : p ∈ candidate r k := by
    simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨rfl, rfl⟩
  rw [heq] at hp
  simp only [candidate, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨hrow, _⟩ | ⟨i, _, _, hcol⟩ | ⟨i, _, hcol, _⟩
  · have hpval : p.1.val = 2 * k := rfl
    omega
  · have ht : tip i = 0 ∨ tip i = 4 := by simp [tip]; omega
    have hpcol : p.2.val = 2 := rfl
    omega
  · have hs : side i = 1 ∨ side i = 3 := by simp [side]; omega
    have hpcol : p.2.val = 2 := rfl
    omega

/-- The `3 × 3` grid with white rows `#..`, `.##`, `.##`. -/
def zeroWhite : Finset (Cell 3) :=
  {((0 : Fin 3), (1 : Fin 3)), ((0 : Fin 3), (2 : Fin 3)),
   ((1 : Fin 3), (0 : Fin 3)), ((2 : Fin 3), (0 : Fin 3))}

/-- The two singleton down words in the first row are incompatible. -/
theorem zero_rook_count : rookCount zeroWhite = 0 := by
  let a : Cell 3 := (0, 1)
  let b : Cell 3 := (0, 2)
  have ha : a ∈ zeroWhite := by decide
  have hb : b ∈ zeroWhite := by decide
  have hfirst (t : Fin 3) (hblack : ((1 : Fin 3), t) ∉ zeroWhite) :
      ∀ d : Cell 3, SameDown zeroWhite ((0 : Fin 3), t) d →
        d = ((0 : Fin 3), t) := by
    intro d hdown
    by_cases hzero : d.1.val = 0
    · apply Prod.ext
      · apply Fin.ext
        exact hzero
      · exact hdown.1.symm
    · have hmin : min (0 : Fin 3) d.1 ≤ (1 : Fin 3) := by
        change min (0 : ℕ) d.1.val ≤ 1
        omega
      have hmax : (1 : Fin 3) ≤ max (0 : Fin 3) d.1 := by
        change 1 ≤ max 0 d.1.val
        omega
      exact (hblack (hdown.2 1 hmin hmax)).elim
  have hda : ∀ d : Cell 3, SameDown zeroWhite a d → d = a :=
    hfirst 1 (by decide)
  have hdb : ∀ d : Cell 3, SameDown zeroWhite b d → d = b :=
    hfirst 2 (by decide)
  have hab : SameAcross zeroWhite a b := by
    refine ⟨rfl, ?_⟩
    intro j hmin hmax
    change min (1 : ℕ) 2 ≤ j.val at hmin
    change j.val ≤ max (1 : ℕ) 2 at hmax
    have hj : j.val = 1 ∨ j.val = 2 := by omega
    rcases hj with h | h
    · have : j = (1 : Fin 3) := Fin.ext h
      subst j
      decide
    · have : j = (2 : Fin 3) := Fin.ext h
      subst j
      decide
  have hne : a ≠ b := by decide
  classical
  have hnone (R : Finset (Cell 3)) : ¬ IsRookPlacement zeroWhite R := by
    intro hR
    obtain ⟨da, hdaR, hdaWord⟩ := (hR.2.2 a ha).2
    obtain ⟨db, hdbR, hdbWord⟩ := (hR.2.2 b hb).2
    have har : a ∈ R := by simpa [hda da hdaWord] using hdaR
    have hbr : b ∈ R := by simpa [hdb db hdbWord] using hdbR
    exact (hR.2.1 a har b hbr hne).1 hab
  unfold rookCount
  have hempty : (zeroWhite.powerset.filter
      (fun R => IsRookPlacement zeroWhite R)) = ∅ := by
    ext R
    simp [hnone R]
  rw [hempty]
  rfl

/-- Lewis–Won Question 4.2, existence part. -/
theorem result : claim := by
  intro r
  rcases r with _ | n
  · exact ⟨3, zeroWhite, zero_rook_count⟩
  · classical
    have hcard : (Finset.range (n + 1)).card =
        ((white (n + 1)).powerset.filter
          (fun R => IsRookPlacement (white (n + 1)) R)).card := by
      apply Finset.card_bij (fun k _ => candidate (n + 1) k)
      · intro k hk
        have hvalid := candidate_is_placement (Finset.mem_range.mp hk)
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hvalid.1, hvalid⟩
      · intro k hk l hl heq
        exact candidate_injective (Finset.mem_range.mp hk) (Finset.mem_range.mp hl) heq
      · intro R hR
        have hvalid : IsRookPlacement (white (n + 1)) R :=
          (Finset.mem_filter.mp hR).2
        obtain ⟨k, hk, heq⟩ := placement_eq_candidate (by omega) hvalid
        exact ⟨k, Finset.mem_range.mpr hk, heq.symm⟩
    exact ⟨gridSize (n + 1), white (n + 1), by
      simpa [rookCount] using hcard.symm⟩

#print axioms result

end D5.S3.Combinatorics.CrosswordRookCounts
