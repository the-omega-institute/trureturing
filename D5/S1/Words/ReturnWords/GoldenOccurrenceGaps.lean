/- GID: D5/S1/Words/ReturnWords/GoldenOccurrenceGaps
   generality: I
   mirror-B: none(waiver:formal-interface-awaits-first-return-dichotomy)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden factor cylinders control equality and give finite adjacent-gap spectra. -/

import D5.S1.Words.ReturnWords.GoldenReturnWords

namespace D5.S1.Words

open Set

/-- Distances between adjacent starts of the same length-`n` golden factor. -/
def goldenOccurrenceGapSet (n : Nat) (w : List Bool) : Set Nat :=
  {d | ∃ i j, AdjacentGoldenOccurrences n w i j ∧ d = j - i}

private theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  simp

private noncomputable def goldenCylinderBreakpoint (m : Nat) : Real :=
  1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)

private noncomputable def goldenCylinderBreakpoints (n : Nat) : Finset Real :=
  (Finset.range n).image goldenCylinderBreakpoint

/-- The fractional mechanical phase at the start of a golden factor. -/
noncomputable def goldenPhase (i : Nat) : Real :=
  Int.fract (((i + 1 : Nat) : Real) * goldenMechanicalSlope)

/-- The numbered cylinder containing the phase of the factor starting at `i`. -/
noncomputable def goldenCylinderRank (n i : Nat) : Nat :=
  ((goldenCylinderBreakpoints n).filter fun x => x ≤ goldenPhase i).card

private theorem floor_add_sub_floor (x t : Real) :
    ⌊x + t⌋ - ⌊x⌋ = ⌊Int.fract x + t⌋ := by
  have hx : (⌊x⌋ : Real) + (Int.fract x + t) = x + t := by
    calc
      (⌊x⌋ : Real) + (Int.fract x + t) = ((⌊x⌋ : Real) + Int.fract x) + t := by ring
      _ = x + t := by rw [Int.floor_add_fract]
  rw [← hx, Int.floor_intCast_add]
  omega

private theorem floor_fract_add_indicator (x t : Real) :
    ⌊Int.fract x + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ Int.fract x then 1 else 0 := by
  have hdecomp : (⌊t⌋ : Real) + (Int.fract x + Int.fract t) = Int.fract x + t := by
    calc
      (⌊t⌋ : Real) + (Int.fract x + Int.fract t) =
          Int.fract x + ((⌊t⌋ : Real) + Int.fract t) := by ring
      _ = Int.fract x + t := by rw [Int.floor_add_fract]
  rw [← hdecomp, Int.floor_intCast_add]
  congr 1
  by_cases h : 1 - Int.fract t ≤ Int.fract x
  · rw [if_pos h, Int.floor_eq_iff]
    norm_num
    constructor
    · linarith
    · linarith [Int.fract_lt_one x, Int.fract_lt_one t]
  · rw [if_neg h, Int.floor_eq_iff]
    norm_num
    constructor
    · linarith [Int.fract_nonneg x, Int.fract_nonneg t]
    · have : Int.fract x < 1 - Int.fract t := lt_of_not_ge h
      linarith

private theorem window_count_eq_cylinder_indicator (i m : Nat) :
    (goldenWindowTrueCount i (m + 1) : Int) =
      ⌊(((m + 1 : Nat) : Real) * goldenMechanicalSlope)⌋ +
        if goldenCylinderBreakpoint m ≤ goldenPhase i then 1 else 0 := by
  rw [goldenWindowTrueCount_eq_floor]
  have hend : (((i + (m + 1) + 1 : Nat) : Real) * goldenMechanicalSlope) =
      (((i + 1 : Nat) : Real) * goldenMechanicalSlope) +
        (((m + 1 : Nat) : Real) * goldenMechanicalSlope) := by
    push_cast
    ring
  change ⌊((i + (m + 1) + 1 : Nat) : Real) * goldenMechanicalSlope⌋ -
      ⌊((i + 1 : Nat) : Real) * goldenMechanicalSlope⌋ = _
  rw [hend, floor_add_sub_floor, floor_fract_add_indicator]
  rfl

private theorem window_count_succ (i m : Nat) :
    goldenWindowTrueCount i (m + 1) = goldenWindowTrueCount i m +
      if goldenWord (i + m) = true then 1 else 0 := by
  classical
  by_cases h : goldenWord (i + m) = true <;>
    simp [goldenWindowTrueCount, Finset.range_add_one, Finset.filter_insert, h]

private theorem selected_eq_of_cylinder_rank_eq {n i j : Nat}
    (h : goldenCylinderRank n i = goldenCylinderRank n j) :
    (goldenCylinderBreakpoints n).filter (fun x => x ≤ goldenPhase i) =
      (goldenCylinderBreakpoints n).filter (fun x => x ≤ goldenPhase j) := by
  rcases le_total (goldenPhase i) (goldenPhase j) with hij | hji
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hij⟩
    · exact h.ge
  · symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hji⟩
    · exact h.le

private theorem window_counts_eq_of_selected_eq {n i j m : Nat} (hm : m ≤ n)
    (h : (goldenCylinderBreakpoints n).filter (fun x => x ≤ goldenPhase i) =
      (goldenCylinderBreakpoints n).filter (fun x => x ≤ goldenPhase j)) :
    goldenWindowTrueCount i m = goldenWindowTrueCount j m := by
  rcases m with _ | m
  · simp [goldenWindowTrueCount]
  have hm' : m < n := by omega
  have hmem : goldenCylinderBreakpoint m ∈ goldenCylinderBreakpoints n :=
    Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm', rfl⟩
  have hiff : goldenCylinderBreakpoint m ≤ goldenPhase i ↔
      goldenCylinderBreakpoint m ≤ goldenPhase j := by
    have := Finset.ext_iff.mp h (goldenCylinderBreakpoint m)
    simpa [hmem] using this
  rw [← Nat.cast_inj (R := Int), window_count_eq_cylinder_indicator,
    window_count_eq_cylinder_indicator]
  by_cases hi : goldenCylinderBreakpoint m ≤ goldenPhase i
  · have hj := hiff.mp hi
    simp [hi, hj]
  · have hj : ¬goldenCylinderBreakpoint m ≤ goldenPhase j := fun hj => hi (hiff.mpr hj)
    simp [hi, hj]

private theorem factor_eq_of_cylinder_rank_eq {n i j : Nat}
    (h : goldenCylinderRank n i = goldenCylinderRank n j) :
    goldenFactor n i = goldenFactor n j := by
  unfold goldenFactor
  congr 1
  funext k
  have hselected := selected_eq_of_cylinder_rank_eq h
  have hbase := window_counts_eq_of_selected_eq k.isLt.le hselected
  have hnext := window_counts_eq_of_selected_eq (Nat.succ_le_of_lt k.isLt) hselected
  rw [window_count_succ, window_count_succ] at hnext
  have hindicator : (if goldenWord (i + k) = true then 1 else 0) =
      if goldenWord (j + k) = true then 1 else 0 := by omega
  by_cases hi : goldenWord (i + k) = true <;>
    by_cases hj : goldenWord (j + k) = true <;> simp_all

private theorem window_counts_eq_of_factor_eq {n i j m : Nat} (hm : m ≤ n)
    (h : goldenFactor n i = goldenFactor n j) :
    goldenWindowTrueCount i m = goldenWindowTrueCount j m := by
  have hletters : (fun k : Fin n => goldenWord (i + k)) =
      fun k : Fin n => goldenWord (j + k) := List.ofFn_inj.mp h
  unfold goldenWindowTrueCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hw⟩
    refine ⟨hk, ?_⟩
    rw [← congrFun hletters ⟨k, hk.trans_le hm⟩]
    exact hw
  · rintro ⟨hk, hw⟩
    refine ⟨hk, ?_⟩
    rw [congrFun hletters ⟨k, hk.trans_le hm⟩]
    exact hw

private theorem selected_eq_of_factor_eq {n i j : Nat}
    (h : goldenFactor n i = goldenFactor n j) :
    (goldenCylinderBreakpoints n).filter (fun x => x ≤ goldenPhase i) =
      (goldenCylinderBreakpoints n).filter (fun x => x ≤ goldenPhase j) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxi⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hm' : m + 1 ≤ n := Finset.mem_range.mp hm
    have hc := congrArg (fun q : Nat => (q : Int))
      (window_counts_eq_of_factor_eq hm' h)
    rw [window_count_eq_cylinder_indicator, window_count_eq_cylinder_indicator] at hc
    have hxj : goldenCylinderBreakpoint m ≤ goldenPhase j := by
      by_contra hxj
      simp [hxi, hxj] at hc
    exact ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hxj⟩
  · rintro ⟨hx, hxj⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    have hm' : m + 1 ≤ n := Finset.mem_range.mp hm
    have hc := congrArg (fun q : Nat => (q : Int))
      (window_counts_eq_of_factor_eq hm' h)
    rw [window_count_eq_cylinder_indicator, window_count_eq_cylinder_indicator] at hc
    have hxi : goldenCylinderBreakpoint m ≤ goldenPhase i := by
      by_contra hxi
      simp [hxi, hxj] at hc
    exact ⟨Finset.mem_image.mpr ⟨m, hm, rfl⟩, hxi⟩

private theorem cylinder_rank_eq_of_factor_eq {n i j : Nat}
    (h : goldenFactor n i = goldenFactor n j) :
    goldenCylinderRank n i = goldenCylinderRank n j := by
  exact congrArg Finset.card (selected_eq_of_factor_eq h)

/-- Equal golden factors are exactly the starts lying in the same rotation cylinder. -/
theorem golden_factor_eq_iff_cylinder_rank_eq (n i j : Nat) :
    goldenFactor n i = goldenFactor n j ↔
      goldenCylinderRank n i = goldenCylinderRank n j :=
  ⟨cylinder_rank_eq_of_factor_eq, factor_eq_of_cylinder_rank_eq⟩

/-- Every occurring golden factor has at least one adjacent-occurrence gap. -/
theorem golden_occurrence_gap_set_nonempty {n : Nat} {w : List Bool}
    (hw : w ∈ goldenFactorSet n) : (goldenOccurrenceGapSet n w).Nonempty := by
  obtain ⟨r, i, j, hadj, _⟩ := golden_return_words_nonempty hw
  exact ⟨j - i, i, j, hadj, rfl⟩

/-- An adjacent-occurrence gap obeys the explicit linear recurrence bound. -/
theorem golden_occurrence_gap_le {n : Nat} (hn : 0 < n) {w : List Bool}
    (hw : w ∈ goldenFactorSet n) {d : Nat} (hd : d ∈ goldenOccurrenceGapSet n w) :
    d ≤ 38 * n + 1 := by
  obtain ⟨i, j, hadj, rfl⟩ := hd
  have hs := adjacent_golden_occurrences_iff.mp hadj
  obtain ⟨k, hik, hkend, hfactor⟩ :=
    golden_factor_uniformly_recurrent_linear hn hw (i + 1)
  have hjk : j ≤ k := by
    by_contra hnot
    have hmem : k ∈ (Finset.Ioo i j).filter (fun l => goldenFactor n l = w) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_Ioo.mpr ⟨by omega, Nat.lt_of_not_ge hnot⟩, hfactor.symm⟩
    rw [hs.2.2.2] at hmem
    simp at hmem
  have hkbound : k ≤ i + 1 + 38 * n := by omega
  omega

/-- The gap spectrum of a positive-length occurring factor is finite. -/
theorem golden_occurrence_gap_set_finite {n : Nat} (hn : 0 < n) {w : List Bool}
    (hw : w ∈ goldenFactorSet n) : (goldenOccurrenceGapSet n w).Finite := by
  apply (Set.finite_Iic (38 * n + 1)).subset
  intro d hd
  exact golden_occurrence_gap_le hn hw hd

/-- The empty factor occurs at every start, so its adjacent-gap spectrum is the singleton one. -/
theorem golden_occurrence_gap_set_zero : goldenOccurrenceGapSet 0 [] = {1} := by
  ext d
  constructor
  · rintro ⟨i, j, hadj, rfl⟩
    have hs := adjacent_golden_occurrences_iff.mp hadj
    have hle : j ≤ i + 1 := by
      by_contra hnot
      have hmem : i + 1 ∈
          (Finset.Ioo i j).filter (fun k => goldenFactor 0 k = ([] : List Bool)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, by
          simp [goldenFactor]⟩
      rw [hs.2.2.2] at hmem
      simp at hmem
    have hgap : j - i = 1 := by omega
    simp [hgap]
  · intro hd
    have hd : d = 1 := by simpa using hd
    subst d
    exact ⟨0, 1, by decide, rfl⟩

private def successiveGaps : List Nat → Finset Nat
  | i :: j :: tail => insert (j - i) (successiveGaps (j :: tail))
  | _ => ∅

private def goldenOccurrenceGapsBelow (n : Nat) (w : List Bool) (bound : Nat) :
    Finset Nat :=
  successiveGaps ((List.range bound).filter fun i => goldenFactor n i = w)

private def factorsBelow (n bound : Nat) : Finset (List Bool) :=
  (Finset.range bound).image (goldenFactor n)

set_option maxRecDepth 100000 in
private theorem golden_occurrence_gap_small_factor_types :
    factorsBelow 2 128 = {[true, false], [false, true], [true, true]} ∧
      factorsBelow 3 128 =
        {[true, false, true], [false, true, true], [true, true, false],
          [false, true, false]} := by
  decide

set_option maxRecDepth 100000 in
private theorem golden_occurrence_gap_small_cases :
    goldenOccurrenceGapsBelow 2 [true, false] 128 = {2, 3} ∧
      goldenOccurrenceGapsBelow 2 [false, true] 128 = {2, 3} ∧
      goldenOccurrenceGapsBelow 2 [true, true] 128 = {3, 5} ∧
      goldenOccurrenceGapsBelow 3 [true, false, true] 128 = {2, 3} ∧
      goldenOccurrenceGapsBelow 3 [false, true, true] 128 = {3, 5} ∧
      goldenOccurrenceGapsBelow 3 [true, true, false] 128 = {3, 5} ∧
      goldenOccurrenceGapsBelow 3 [false, true, false] 128 = {5, 8} := by
  decide

#print axioms golden_factor_eq_iff_cylinder_rank_eq
#print axioms golden_occurrence_gap_set_nonempty
#print axioms golden_occurrence_gap_le
#print axioms golden_occurrence_gap_set_finite
#print axioms golden_occurrence_gap_set_zero

end D5.S1.Words
