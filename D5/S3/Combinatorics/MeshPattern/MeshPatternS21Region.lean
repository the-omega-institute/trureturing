/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Region
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Region
   mirror-E: none(waiver:rank-three-moving-region)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Restricted row and column conservation preserves the active rectangle region. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Criteria
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

def active (n : ℕ) (p : List ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun maximum => 3 ≤ maximum ∧
    (rectangle p (n - maximum + 3) maximum).card = 3)

def activeRegion (n : ℕ) (p : List ℕ) : Set (ℕ × ℕ) :=
  {cell | 1 ≤ cell.1 ∧ 1 ≤ cell.2 ∧ ∃ maximum ∈ active n p,
    cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum}

open scoped Classical in
theorem active_geometry (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
    activeRegion n p ⊆ ferrersRegion n ∧
    (∀ x y smallerX smallerY, (x, y) ∈ activeRegion n p →
      1 ≤ smallerX → smallerX ≤ x → 1 ≤ smallerY → smallerY ≤ y →
      (smallerX, smallerY) ∈ activeRegion n p) ∧
    (∀ x y, x ≤ n → y ≤ n → x = 0 ∨ y = 0 ∨ (x, y) ∈ activeRegion n p →
      (rectangle p x y).card ≤ 3) ∧
    (∀ maximum ∈ active n p,
      (n - maximum + 3, maximum) ∈ activeRegion n p ∧
      (n - maximum + 4, maximum) ∉ activeRegion n p ∧
      (n - maximum + 3, maximum + 1) ∉ activeRegion n p) ∧
    (∀ left right : Finset (ℕ × ℕ),
      left.filter (fun cell => cell ∉ activeRegion n p) =
        right.filter (fun cell => cell ∉ activeRegion n p) →
      (∀ y, (left.filter (fun cell => cell ∈ activeRegion n p ∧ cell.2 = y)).card =
        (right.filter (fun cell => cell ∈ activeRegion n p ∧ cell.2 = y)).card) →
      (∀ x, (left.filter (fun cell => cell ∈ activeRegion n p ∧ cell.1 = x)).card =
        (right.filter (fun cell => cell ∈ activeRegion n p ∧ cell.1 = x)).card) →
      ∀ maximum, 3 ≤ maximum → maximum ≤ n →
        (left.filter (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum)).card =
          (right.filter (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum)).card ∧
        (left.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).card =
          (right.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).card ∧
        (left.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).card =
          (right.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).card) ∧
    (∀ q : List ℕ,
      (∀ maximum, 3 ≤ maximum → maximum ≤ n →
        (rectangle p (n - maximum + 3) maximum).card =
          (rectangle q (n - maximum + 3) maximum).card) →
      active n p = active n q ∧ activeRegion n p = activeRegion n q) ∧
    (n < 3 ∨ active n p = ∅ → ∀ inc : Bool, MeshPatternS21Defs.occ inc p = 0) := by
  have hactive : ∀ maximum, maximum ∈ active n p ↔
      3 ≤ maximum ∧ maximum ≤ n ∧
      (rectangle p (n - maximum + 3) maximum).card = 3 := by
    intro maximum
    simp only [active, Finset.mem_filter, Finset.mem_range]
    omega
  have hconservation : ∀ (region : Set (ℕ × ℕ))
    (hregion : region ⊆ ferrersRegion n) (left right : Finset (ℕ × ℕ))
    (houtside : left.filter (fun cell => cell ∉ region) =
      right.filter (fun cell => cell ∉ region))
    (hrows : ∀ y,
      (left.filter (fun cell => cell ∈ region ∧ cell.2 = y)).card =
        (right.filter (fun cell => cell ∈ region ∧ cell.2 = y)).card)
    (hcolumns : ∀ x,
      (left.filter (fun cell => cell ∈ region ∧ cell.1 = x)).card =
        (right.filter (fun cell => cell ∈ region ∧ cell.1 = x)).card),
    ∀ maximum, 3 ≤ maximum → maximum ≤ n →
      (left.filter (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum)).card =
        (right.filter (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum)).card ∧
      (left.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).card =
        (right.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).card ∧
      (left.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).card =
        (right.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).card := by
    intro region hregion left right houtside hrows hcolumns
    let leftInside := left.filter (fun cell => cell ∈ region)
    let rightInside := right.filter (fun cell => cell ∈ region)
    have hbounds : ∀ cell ∈ region,
        cell.1 ≤ n ∧ cell.2 ≤ n ∧ cell.1 + cell.2 ≤ n + 3 := by
      intro cell hcell
      obtain ⟨maximum, hthree, hbound, _, hx, _, hy⟩ := hregion hcell
      exact ⟨by omega, by omega, by omega⟩
    have hcoordinateCounts : ∀ projection : (ℕ × ℕ) → ℕ,
        (∀ cell ∈ region, projection cell ≤ n) →
        (∀ index, (leftInside.filter (fun cell => projection cell = index)).card =
          (rightInside.filter (fun cell => projection cell = index)).card) →
        ∀ (test : ℕ → Prop) [DecidablePred test],
          (leftInside.filter (fun cell => test (projection cell))).card =
            (rightInside.filter (fun cell => test (projection cell))).card := by
      intro projection hprojection hfibers test testDec
      let indices := (Finset.range (n + 1)).filter test
      have hleft : leftInside.filter (fun cell => projection cell ∈ indices) =
          leftInside.filter (fun cell => test (projection cell)) := by
        ext cell
        simp only [indices, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hcell, _, htest⟩
          exact ⟨hcell, htest⟩
        · rintro ⟨hcell, htest⟩
          have hbound := hprojection cell (Finset.mem_filter.mp hcell).2
          exact ⟨hcell, by omega, htest⟩
      have hright : rightInside.filter (fun cell => projection cell ∈ indices) =
          rightInside.filter (fun cell => test (projection cell)) := by
        ext cell
        simp only [indices, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hcell, _, htest⟩
          exact ⟨hcell, htest⟩
        · rintro ⟨hcell, htest⟩
          have hbound := hprojection cell (Finset.mem_filter.mp hcell).2
          exact ⟨hcell, by omega, htest⟩
      calc
        _ = ∑ index ∈ indices,
            (leftInside.filter (fun cell => projection cell = index)).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter, hleft]
        _ = ∑ index ∈ indices,
            (rightInside.filter (fun cell => projection cell = index)).card :=
          Finset.sum_congr rfl (fun index _ => hfibers index)
        _ = _ := by rw [Finset.sum_card_fiberwise_eq_card_filter, hright]
    have hrowCounts : ∀ (test : ℕ → Prop) [DecidablePred test],
        (leftInside.filter (fun cell => test cell.2)).card =
          (rightInside.filter (fun cell => test cell.2)).card := by
      apply hcoordinateCounts Prod.snd
      · exact fun cell hcell => (hbounds cell hcell).2.1
      · intro index
        simpa only [leftInside, rightInside, Finset.filter_filter] using hrows index
    have hcolumnCounts : ∀ (test : ℕ → Prop) [DecidablePred test],
        (leftInside.filter (fun cell => test cell.1)).card =
          (rightInside.filter (fun cell => test cell.1)).card := by
      apply hcoordinateCounts Prod.fst
      · exact fun cell hcell => (hbounds cell hcell).1
      · intro index
        simpa only [leftInside, rightInside, Finset.filter_filter] using hcolumns index
    have htotal : leftInside.card = rightInside.card := by
      simpa using hrowCounts (fun _ => True)
    have hsplit : ∀ (filling : Finset (ℕ × ℕ)) (test : (ℕ × ℕ) → Prop)
        [DecidablePred test],
        (filling.filter test).card =
          ((filling.filter (fun cell => cell ∈ region)).filter test).card +
          ((filling.filter (fun cell => cell ∉ region)).filter test).card := by
      intro filling test testDec
      have hcard := Finset.card_filter_add_card_filter_not
        (s := filling.filter test) (fun cell => cell ∈ region)
      simpa only [Finset.filter_filter, and_comm] using hcard.symm
    intro maximum hthree hbound
    let width := n - maximum + 3
    have hnoNE : ∀ cell ∈ region, width < cell.1 → cell.2 ≤ maximum := by
      intro cell hcell hx
      have := hbounds cell hcell
      dsimp [width] at *
      omega
    have hdecomposition : ∀ inside : Finset (ℕ × ℕ),
        (∀ cell ∈ inside, cell ∈ region) →
        (inside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card +
          (inside.filter (fun cell => maximum < cell.2)).card +
          (inside.filter (fun cell => width < cell.1)).card = inside.card := by
      intro inside hins
      have hvertical := Finset.card_filter_add_card_filter_not
        (s := inside) (fun cell => cell.2 ≤ maximum)
      have hhorizontal := Finset.card_filter_add_card_filter_not
        (s := inside.filter (fun cell => cell.2 ≤ maximum)) (fun cell => cell.1 ≤ width)
      have hrightStrip : inside.filter (fun cell => cell.2 ≤ maximum ∧ width < cell.1) =
          inside.filter (fun cell => width < cell.1) := by
        ext cell
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hcell, _, hx⟩
          exact ⟨hcell, hx⟩
        · rintro ⟨hcell, hx⟩
          exact ⟨hcell, hnoNE cell (hins cell hcell) hx, hx⟩
      simp only [Nat.not_le] at hvertical
      simp only [Finset.filter_filter, Nat.not_le] at hhorizontal
      rw [hrightStrip] at hhorizontal
      have hrect : inside.filter (fun cell => cell.2 ≤ maximum ∧ cell.1 ≤ width) =
          inside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum) := by
        simp only [and_comm]
      rw [hrect] at hhorizontal
      omega
    have hrectCounts :
        (leftInside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card =
          (rightInside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card := by
      have hleft := hdecomposition leftInside
        (fun _ hcell => (Finset.mem_filter.mp hcell).2)
      have hright := hdecomposition rightInside
        (fun _ hcell => (Finset.mem_filter.mp hcell).2)
      have hrowsAbove := hrowCounts (fun y => maximum < y)
      have hcolumnsRight := hcolumnCounts (fun x => width < x)
      omega
    have hrowCorner : ∀ filling : Finset (ℕ × ℕ),
        (filling.filter (fun cell => cell ∈ region ∧ cell.2 = maximum ∧ cell.1 ≤ width)) =
          filling.filter (fun cell => cell ∈ region ∧ cell.2 = maximum) := by
      intro filling
      ext cell
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hcell, hregionCell, hy, _⟩
        exact ⟨hcell, hregionCell, hy⟩
      · rintro ⟨hcell, hregionCell, hy⟩
        have := hbounds cell hregionCell
        refine ⟨hcell, hregionCell, hy, ?_⟩
        dsimp [width]
        omega
    have hcolumnCorner : ∀ filling : Finset (ℕ × ℕ),
        (filling.filter (fun cell => cell ∈ region ∧ cell.1 = width ∧ cell.2 ≤ maximum)) =
          filling.filter (fun cell => cell ∈ region ∧ cell.1 = width) := by
      intro filling
      ext cell
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hcell, hregionCell, hx, _⟩
        exact ⟨hcell, hregionCell, hx⟩
      · rintro ⟨hcell, hregionCell, hx⟩
        have := hbounds cell hregionCell
        refine ⟨hcell, hregionCell, hx, ?_⟩
        dsimp [width] at hx
        omega
    simp only [width] at hrowCorner hcolumnCorner
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit left (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum),
        hsplit right (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum), houtside]
      exact congrArg (fun count => count +
        ((right.filter (fun cell => cell ∉ region)).filter
          (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card) hrectCounts
    · rw [hsplit left (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3),
        hsplit right (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3), houtside]
      simp only [Finset.filter_filter, hrowCorner]
      simpa only [Finset.filter_filter] using congrArg (fun count => count +
        ((right.filter (fun cell => cell ∉ region)).filter
          (fun cell => cell.2 = maximum ∧ cell.1 ≤ width)).card) (hrows maximum)
    · rw [hsplit left (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum),
        hsplit right (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum), houtside]
      simp only [Finset.filter_filter, hcolumnCorner]
      simpa only [Finset.filter_filter] using congrArg (fun count => count +
        ((right.filter (fun cell => cell ∉ region)).filter
          (fun cell => cell.1 = width ∧ cell.2 ≤ maximum)).card) (hcolumns width)
  have hsub : activeRegion n p ⊆ ferrersRegion n := by
    rintro ⟨x, y⟩ ⟨hx, hy, maximum, hmaximum, hxbound, hybound⟩
    have hbound := (hactive maximum).mp hmaximum
    exact ⟨maximum, hbound.1, hbound.2.1, hx, hxbound, hy, hybound⟩
  refine ⟨hsub, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y smallerX smallerY hmem hsmallX hboundX hsmallY hboundY
    obtain ⟨_, _, maximum, hmaximum, hxbound, hybound⟩ := hmem
    exact ⟨hsmallX, hsmallY, maximum, hmaximum,
      le_trans hboundX hxbound, le_trans hboundY hybound⟩
  · intro x y hxlimit hylimit hvertex
    rcases hvertex with rfl | rfl | hmem
    · simp [rectangle]
    · have hzero : rectangle p x 0 = ∅ := by
        ext position
        simp only [rectangle, Finset.mem_filter, Finset.mem_range, Nat.le_zero,
          Finset.notMem_empty, iff_false, not_and]
        intro hposition hvalue
        have hlength : p.length = n := by simpa using hp.length_eq
        have hpositionbound : position < p.length := by omega
        have hmem := hp.mem_iff.mp (List.getElem_mem hpositionbound)
        rw [List.mem_range'_1] at hmem
        rw [List.getD_eq_getElem p 0 hpositionbound] at hvalue
        omega
      simp [hzero]
    · obtain ⟨_, _, maximum, hmaximum, hxbound, hybound⟩ := hmem
      have hsubset : rectangle p x y ⊆ rectangle p (n - maximum + 3) maximum := by
        intro position hposition
        simp only [rectangle, Finset.mem_filter, Finset.mem_range] at *
        exact ⟨lt_of_lt_of_le hposition.1 hxbound, le_trans hposition.2 hybound⟩
      have hcard := Finset.card_le_card hsubset
      simpa only [(hactive maximum).mp hmaximum |>.2.2] using hcard
  · intro maximum hmaximum
    have hbound := (hactive maximum).mp hmaximum
    refine ⟨⟨by omega, by omega, maximum, hmaximum, le_refl _, le_refl _⟩, ?_, ?_⟩
    · rintro ⟨_, _, other, hother, hx, hy⟩
      have hotherbound := (hactive other).mp hother
      omega
    · rintro ⟨_, _, other, hother, hx, hy⟩
      have hotherbound := (hactive other).mp hother
      omega
  · intro left right houtside hrows hcolumns
    exact hconservation (activeRegion n p) hsub left right houtside hrows hcolumns
  · intro q hcounts
    have heq : active n p = active n q := by
      ext maximum
      simp only [active, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hbound, hthree, hcard⟩
        exact ⟨hbound, hthree, (hcounts maximum hthree (by omega)).symm.trans hcard⟩
      · rintro ⟨hbound, hthree, hcard⟩
        exact ⟨hbound, hthree, (hcounts maximum hthree (by omega)).trans hcard⟩
    exact ⟨heq, by simp only [activeRegion, heq]⟩
  · intro hdegenerate inc
    have hnone : active n p = ∅ := by
      rcases hdegenerate with hsmall | hempty
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro maximum hmaximum
        have := (hactive maximum).mp hmaximum
        omega
      · exact hempty
    have hnoOccurrence : ∀ triple, ¬MeshPatternS21Defs.IsOccurrence inc p triple := by
      rintro ⟨first, middle, last⟩ hocc
      obtain ⟨hfirst, hmiddle, hlast, _, hrect, hsum⟩ :=
        ((rectangle_criterion n p hp).1 inc first middle last).mp hocc
      let maximum := max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0)
      have hlength : p.length = n := by simpa using hp.length_eq
      have hvalues : ∀ position < p.length, p.getD position 0 ≤ n := by
        intro position hposition
        have hmem := hp.mem_iff.mp (List.getElem_mem hposition)
        rw [List.mem_range'_1] at hmem
        rw [List.getD_eq_getElem p 0 hposition]
        omega
      have hfirstbound := hvalues first (by omega)
      have hmiddlebound := hvalues middle (by omega)
      have hlastbound := hvalues last hlast
      have hwidth : last + 1 = n - maximum + 3 := by dsimp [maximum]; omega
      have hcard : (rectangle p (n - maximum + 3) maximum).card = 3 := by
        rw [← hwidth]
        change (rectangle p (last + 1)
          (max (max (p.getD first 0) (p.getD middle 0)) (p.getD last 0))).card = 3
        rw [hrect]
        simp [Finset.card_insert_of_notMem, ne_of_lt hfirst, ne_of_lt hmiddle,
          ne_of_lt (lt_trans hfirst hmiddle)]
      have hmem : maximum ∈ active n p := (hactive maximum).mpr
        ⟨by dsimp [maximum]; omega, by dsimp [maximum]; omega, hcard⟩
      rw [hnone] at hmem
      exact Finset.notMem_empty maximum hmem
    have hempty : {triple | MeshPatternS21Defs.IsOccurrence inc p triple} = ∅ := by
      ext triple
      exact iff_of_false (hnoOccurrence triple) (Set.notMem_empty triple)
    simp only [MeshPatternS21Defs.occ, hempty, Set.ncard_empty]

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21
