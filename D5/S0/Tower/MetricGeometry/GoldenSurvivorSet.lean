/- GID: D5/S0/Tower/MetricGeometry/GoldenSurvivorSet
   generality: I
   mirror-B: D5/B/S0/Tower/MetricGeometry/GoldenSurvivorSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-survivor maximizers are exactly the midpoints of the largest internal gaps. -/

import D5.S0.Tower.GoldenGapWord
import D5.S0.Tower.MetricGeometry.GoldenSurvivor
import Mathlib.Data.Set.Card

/- Library-search audit trail (2026-08-16):
   * Repository searches found the frozen golden gap spectrum, frequency, word,
     and survivor upper-bound declarations, but no maximizer-set characterization.
   * Loogle found the generic `Metric.infDist` API, including `Metric.le_infDist`
     and `Metric.infDist_le_dist_of_mem`, but no finite ordered-grid maximizer theorem.
   * LeanSearch returned midpoint-distance and finite-separation results, but no
     theorem identifying maximum distance-to-set points with largest-gap midpoints.
   The exact ordered-grid argument is therefore proved locally below. -/

namespace D5.S0.Tower.MetricGeometry.GoldenSurvivorSet

open D5.S0.Tower.GoldenGapFrequency
open D5.S0.Tower.GoldenGaps
open D5.S0.Tower.GoldenGapWord
open D5.S0.Tower.MetricGeometry.GoldenSurvivor

local notation "φ" => Real.goldenRatio

/-- The midpoint of an internal adjacent golden-name gap. -/
noncomputable def goldenGapMidpoint
    (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) : Real :=
  (indexedNameValue Q (goldenGapLeft Q i) +
      indexedNameValue Q (goldenGapRight Q i)) / 2

/-- An internal adjacent gap has the largest level-`Q` golden length. -/
def IsGoldenLargeGap (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) : Prop :=
  indexedNameValue Q (goldenGapRight Q i) -
      indexedNameValue Q (goldenGapLeft Q i) = φ ^ (-(Q : Int))

/-- The finite index set of largest internal gaps. -/
noncomputable def goldenLargeGapIndices
    (Q : Nat) : Finset (Fin (Nat.fib (Q + 2) - 1)) := by
  classical
  exact Finset.univ.filter (IsGoldenLargeGap Q)

/-- Hull points attaining the normalized one-half ceiling. -/
def goldenSurvivorMaximizers (Q : Nat) : Set Real :=
  {x | x ∈ goldenNameHull Q ∧ goldenSurvivor Q x = 1 / 2}

/-- Midpoints inherit strict order from the frozen increasing grid enumeration. -/
theorem goldenGapMidpoint_strictMono (Q : Nat) :
    StrictMono (goldenGapMidpoint Q) := by
  intro i j hij
  let ai := indexedNameValue Q (goldenGapLeft Q i)
  let bi := indexedNameValue Q (goldenGapRight Q i)
  let aj := indexedNameValue Q (goldenGapLeft Q j)
  let bj := indexedNameValue Q (goldenGapRight Q j)
  have hai_bi : ai < bi := by
    apply indexed_nameValue_strictMono Q
    change i.1 < i.1 + 1
    omega
  have hbi_aj : bi ≤ aj := by
    apply (indexed_nameValue_strictMono Q).monotone
    change i.1 + 1 ≤ j.1
    exact Nat.succ_le_of_lt hij
  have haj_bj : aj < bj := by
    apply indexed_nameValue_strictMono Q
    change j.1 < j.1 + 1
    omega
  change (ai + bi) / 2 < (aj + bj) / 2
  linarith

/-- A hull point attains one half exactly when it is the midpoint of a largest gap. -/
theorem goldenSurvivor_eq_half_iff
    (Q : Nat) (x : Real) (hx : x ∈ goldenNameHull Q) :
    goldenSurvivor Q x = 1 / 2 ↔
      ∃ i : Fin (Nat.fib (Q + 2) - 1),
        IsGoldenLargeGap Q i ∧ x = goldenGapMidpoint Q i := by
  constructor
  · intro hsurvivor
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    let a := indexedNameValue Q (goldenGapLeft Q i)
    let b := indexedNameValue Q (goldenGapRight Q i)
    let large := φ ^ (-(Q : Int))
    let scale := φ ^ (Q : Int)
    let nearest := Metric.infDist x (goldenNameGrid Q)
    have hgap : b - a = large ∨
        b - a = φ ^ (-((Q + 1 : Nat) : Int)) := by
      simpa [a, b, large, goldenGapLeft, goldenGapRight] using
        consecutive_nameValue_gap Q i
    have hsmall_le : φ ^ (-((Q + 1 : Nat) : Int)) ≤ large := by
      dsimp [large]
      apply zpow_le_zpow_right₀ Real.one_lt_goldenRatio.le
      omega
    have hgap_le : b - a ≤ large := by
      rcases hgap with hgap | hgap
      · exact hgap.le
      · exact hgap.le.trans hsmall_le
    have hscale_pos : 0 < scale := by
      exact zpow_pos Real.goldenRatio_pos _
    have hcancel : scale * large = 1 := by
      dsimp [scale, large]
      rw [← zpow_add₀ Real.goldenRatio_ne_zero]
      simp
    have hnearest_scaled : scale * nearest = 1 / 2 := by
      simpa [goldenSurvivor, scale, nearest] using hsurvivor
    have hlarge_scaled : scale * (large / 2) = 1 / 2 := by
      rw [← mul_div_assoc, hcancel]
    have hnearest : nearest = large / 2 :=
      mul_left_cancel₀ hscale_pos.ne' (hnearest_scaled.trans hlarge_scaled.symm)
    have ha_mem : a ∈ goldenNameGrid Q := ⟨goldenGapLeft Q i, rfl⟩
    have hb_mem : b ∈ goldenNameGrid Q := ⟨goldenGapRight Q i, rfl⟩
    have hleft : large / 2 ≤ x - a := by
      rw [← hnearest]
      calc
        nearest ≤ dist x a := Metric.infDist_le_dist_of_mem ha_mem
        _ = x - a := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxi.1)]
    have hright : large / 2 ≤ b - x := by
      rw [← hnearest]
      calc
        nearest ≤ dist x b := Metric.infDist_le_dist_of_mem hb_mem
        _ = b - x := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxi.2)]
          ring
    have hlarge_le_gap : large ≤ b - a := by linarith
    have hlarge_gap : b - a = large := le_antisymm hgap_le hlarge_le_gap
    refine ⟨i, ?_, ?_⟩
    · change b - a = large
      exact hlarge_gap
    · dsimp [goldenGapMidpoint, a, b]
      linarith
  · rintro ⟨i, hlarge, rfl⟩
    let a := indexedNameValue Q (goldenGapLeft Q i)
    let b := indexedNameValue Q (goldenGapRight Q i)
    have hgap : b - a = φ ^ (-(Q : Int)) := by
      simpa [IsGoldenLargeGap, a, b] using hlarge
    have hgrid : (goldenNameGrid Q).Nonempty :=
      ⟨a, goldenGapLeft Q i, rfl⟩
    have hinf_lower : (b - a) / 2 ≤
        Metric.infDist (goldenGapMidpoint Q i) (goldenNameGrid Q) := by
      rw [Metric.le_infDist hgrid]
      intro y hy
      rcases hy with ⟨j, rfl⟩
      by_cases hj : j ≤ goldenGapLeft Q i
      · have hj_value : indexedNameValue Q j ≤ a :=
          (indexed_nameValue_strictMono Q).monotone hj
        change (b - a) / 2 ≤ dist ((a + b) / 2) (indexedNameValue Q j)
        rw [Real.dist_eq, abs_of_nonneg]
        · linarith
        · have hgap_pos : 0 < b - a := hgap.symm ▸ zpow_pos Real.goldenRatio_pos _
          linarith
      · have hj_right : goldenGapRight Q i ≤ j := by
          change i.1 + 1 ≤ j.1
          change ¬j.1 ≤ i.1 at hj
          omega
        have hj_value : b ≤ indexedNameValue Q j :=
          (indexed_nameValue_strictMono Q).monotone hj_right
        change (b - a) / 2 ≤ dist ((a + b) / 2) (indexedNameValue Q j)
        rw [Real.dist_eq, abs_of_nonpos]
        · linarith
        · have hgap_pos : 0 < b - a := hgap.symm ▸ zpow_pos Real.goldenRatio_pos _
          linarith
    have hinf_upper :
        Metric.infDist (goldenGapMidpoint Q i) (goldenNameGrid Q) ≤ (b - a) / 2 := by
      calc
        Metric.infDist (goldenGapMidpoint Q i) (goldenNameGrid Q) ≤
            dist (goldenGapMidpoint Q i) a :=
          Metric.infDist_le_dist_of_mem ⟨goldenGapLeft Q i, rfl⟩
        _ = (b - a) / 2 := by
          change dist ((a + b) / 2) a = (b - a) / 2
          rw [Real.dist_eq, abs_of_nonneg]
          · ring
          · have hgap_pos : 0 < b - a := hgap.symm ▸ zpow_pos Real.goldenRatio_pos _
            linarith
    have hinf :
        Metric.infDist (goldenGapMidpoint Q i) (goldenNameGrid Q) = (b - a) / 2 :=
      le_antisymm hinf_upper hinf_lower
    have hcancel : φ ^ (Q : Int) * φ ^ (-(Q : Int)) = 1 := by
      rw [← zpow_add₀ Real.goldenRatio_ne_zero]
      simp
    unfold goldenSurvivor
    rw [hinf, hgap, ← mul_div_assoc, hcancel]

/-- The maximizer set is the image of the finite largest-gap index set. -/
theorem goldenSurvivorMaximizers_eq_midpoint_image (Q : Nat) (hQ : 1 ≤ Q) :
    goldenSurvivorMaximizers Q =
      goldenGapMidpoint Q '' (goldenLargeGapIndices Q : Set _) := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    rcases (goldenSurvivor_eq_half_iff Q x hx).mp hmax with ⟨i, hi, rfl⟩
    exact ⟨i, by simp [goldenLargeGapIndices, hi], rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hlarge : IsGoldenLargeGap Q i := by
      simpa [goldenLargeGapIndices] using hi
    have hmid_mem : goldenGapMidpoint Q i ∈ goldenNameHull Q := by
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      have hgap_pos : 0 <
          indexedNameValue Q (goldenGapRight Q i) -
            indexedNameValue Q (goldenGapLeft Q i) :=
        hlarge.symm ▸ zpow_pos Real.goldenRatio_pos _
      constructor <;> dsimp [goldenGapMidpoint] <;> linarith
    exact ⟨hmid_mem,
      (goldenSurvivor_eq_half_iff Q _ hmid_mem).mpr ⟨i, hlarge, rfl⟩⟩

/-- Maximizers and largest internal gaps have exactly the same cardinality. -/
theorem golden_survivor_maximizer_ncard (Q : Nat) (hQ : 1 ≤ Q) :
    Set.ncard (goldenSurvivorMaximizers Q) = (goldenLargeGapIndices Q).card := by
  rw [goldenSurvivorMaximizers_eq_midpoint_image Q hQ,
    Set.ncard_image_of_injective _ (goldenGapMidpoint_strictMono Q).injective,
    Set.ncard_coe_finset]

/-- Embed an internal gap index into the boundary-completed gap indexing. -/
def goldenGapFullIndex
    (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) : Fin (Nat.fib (Q + 2)) :=
  ⟨i.1, by
    have hi := i.2
    have hpos : 0 < Nat.fib (Q + 2) := Nat.fib_pos.2 (by omega)
    omega⟩

/-- The final boundary-completed gap index. -/
def goldenTerminalIndex (Q : Nat) : Fin (Nat.fib (Q + 2)) :=
  ⟨Nat.fib (Q + 2) - 1, Nat.sub_lt (Nat.fib_pos.2 (by omega)) (by omega)⟩

/-- The internal-gap embedding is injective. -/
theorem goldenGapFullIndex_injective (Q : Nat) :
    Function.Injective (goldenGapFullIndex Q) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun k : Fin (Nat.fib (Q + 2)) => k.1) hij

/-- On internal indices, the completed gap is the ordinary adjacent gap. -/
theorem fullGap_goldenGapFullIndex
    (Q : Nat) (i : Fin (Nat.fib (Q + 2) - 1)) :
    fullGap Q (goldenGapFullIndex Q i) =
      indexedNameValue Q (goldenGapRight Q i) -
        indexedNameValue Q (goldenGapLeft Q i) := by
  have hi : i.1 + 1 < Nat.fib (Q + 2) := by
    have := i.2
    omega
  simp [fullGap, goldenGapFullIndex, goldenGapLeft, goldenGapRight, hi]

/-- Filtering internal large gaps is filtering all large gaps and deleting the terminal one. -/
theorem goldenLargeGapIndices_map_eq_full_erase (Q : Nat) :
    (goldenLargeGapIndices Q).map
        ⟨goldenGapFullIndex Q, goldenGapFullIndex_injective Q⟩ =
      ((Finset.univ : Finset (Fin (Nat.fib (Q + 2)))).filter fun i =>
        fullGap Q i = φ ^ (-(Q : Int))).erase (goldenTerminalIndex Q) := by
  classical
  ext j
  simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hlarge : IsGoldenLargeGap Q i := by
      simpa [goldenLargeGapIndices] using hi
    constructor
    · intro heq
      have hval := congrArg Fin.val heq
      have hi_bound := i.2
      dsimp [goldenGapFullIndex, goldenTerminalIndex] at hval
      omega
    · change fullGap Q (goldenGapFullIndex Q i) = φ ^ (-(Q : Int))
      rw [fullGap_goldenGapFullIndex]
      exact hlarge
  · rintro ⟨hj_terminal, hj_large⟩
    have hj_ne : j.1 ≠ Nat.fib (Q + 2) - 1 := by
      intro hj
      apply hj_terminal
      apply Fin.ext
      simpa [goldenTerminalIndex] using hj
    have hj_internal : j.1 < Nat.fib (Q + 2) - 1 := by
      have hj_bound := j.2
      have hpos : 0 < Nat.fib (Q + 2) := Nat.fib_pos.2 (by omega)
      omega
    let i : Fin (Nat.fib (Q + 2) - 1) := ⟨j.1, hj_internal⟩
    have hi_full : goldenGapFullIndex Q i = j := by
      apply Fin.ext
      rfl
    refine ⟨i, ?_, hi_full⟩
    simp only [goldenLargeGapIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsGoldenLargeGap
    rw [← fullGap_goldenGapFullIndex, hi_full]
    exact hj_large

/-- Internal large gaps plus a possible large terminal gap have the frozen Fibonacci count. -/
theorem golden_internal_large_gap_count (Q : Nat) (hQ : 2 ≤ Q) :
    (goldenLargeGapIndices Q).card +
        (if fullGap Q (goldenTerminalIndex Q) = φ ^ (-(Q : Int)) then 1 else 0) =
      Nat.fib (Q + 1) := by
  classical
  let allLarge :=
    (Finset.univ : Finset (Fin (Nat.fib (Q + 2)))).filter fun i =>
      fullGap Q i = φ ^ (-(Q : Int))
  have hmap := goldenLargeGapIndices_map_eq_full_erase Q
  have hcard : (goldenLargeGapIndices Q).card =
      (allLarge.erase (goldenTerminalIndex Q)).card := by
    rw [← Finset.card_map ⟨goldenGapFullIndex Q, goldenGapFullIndex_injective Q⟩,
      hmap]
  have hfull : allLarge.card = Nat.fib (Q + 1) := by
    simpa [allLarge, largeGapCount] using (golden_full_gap_counts Q hQ).1
  by_cases hterminal :
      fullGap Q (goldenTerminalIndex Q) = φ ^ (-(Q : Int))
  · have hmem : goldenTerminalIndex Q ∈ allLarge := by
      simp only [allLarge, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hterminal
    rw [if_pos hterminal, hcard, Finset.card_erase_add_one hmem, hfull]
  · have hnotmem : goldenTerminalIndex Q ∉ allLarge := by
      intro hmem
      apply hterminal
      simpa only [allLarge, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    rw [if_neg hterminal, add_zero, hcard,
      Finset.erase_eq_of_notMem hnotmem, hfull]

/-- At level four the terminal gap is large, as read from the frozen Fibonacci gap word. -/
theorem golden_terminal_gap_four_large :
    fullGap 4 (goldenTerminalIndex 4) = φ ^ (-4 : Int) := by
  have hword := golden_full_gap_word 4 (by omega)
  have hletter := congrArg (fun w : List Bool => w[7]?) hword
  simp only [goldenGapWord, List.getElem?_ofFn] at hletter
  norm_num [fibWord, subst] at hletter
  rw [zpow_neg]
  rw [show goldenTerminalIndex 4 =
      (⟨7, by norm_num [Nat.fib]⟩ : Fin (Nat.fib 6)) by
    apply Fin.ext
    norm_num [goldenTerminalIndex, Nat.fib]]
  exact hletter

/-- The level-four golden survivor has exactly four maximizing hull points. -/
theorem golden_survivor_four_point_ncard :
    Set.ncard (goldenSurvivorMaximizers 4) = 4 := by
  rw [golden_survivor_maximizer_ncard 4 (by omega)]
  have hcount := golden_internal_large_gap_count 4 (by omega)
  have hterminal :
      fullGap 4 (goldenTerminalIndex 4) = φ ^ (-((4 : Nat) : Int)) := by
    simpa only [Nat.cast_ofNat] using golden_terminal_gap_four_large
  rw [if_pos hterminal] at hcount
  norm_num [Nat.fib] at hcount ⊢
  omega

/-- At the champion's level six, the frozen Fibonacci gap word also ends in a large gap. -/
theorem golden_terminal_gap_six_large :
    fullGap 6 (goldenTerminalIndex 6) = φ ^ (-6 : Int) := by
  have hword := golden_full_gap_word 6 (by omega)
  have hletter := congrArg (fun w : List Bool => w[20]?) hword
  simp only [goldenGapWord, List.getElem?_ofFn] at hletter
  norm_num [fibWord, subst] at hletter
  rw [zpow_neg]
  rw [show goldenTerminalIndex 6 =
      (⟨20, by norm_num [Nat.fib]⟩ : Fin (Nat.fib 8)) by
    apply Fin.ext
    norm_num [goldenTerminalIndex, Nat.fib]]
  exact hletter

/-- The level-six metric survivor has twelve, rather than four, maximizing hull points. -/
theorem golden_survivor_champion_level_ncard :
    Set.ncard (goldenSurvivorMaximizers 6) = 12 := by
  rw [golden_survivor_maximizer_ncard 6 (by omega)]
  have hcount := golden_internal_large_gap_count 6 (by omega)
  have hterminal :
      fullGap 6 (goldenTerminalIndex 6) = φ ^ (-((6 : Nat) : Int)) := by
    simpa only [Nat.cast_ofNat] using golden_terminal_gap_six_large
  rw [if_pos hterminal] at hcount
  norm_num [Nat.fib] at hcount ⊢
  omega

end D5.S0.Tower.MetricGeometry.GoldenSurvivorSet
