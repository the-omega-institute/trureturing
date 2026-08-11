/- GID: D5/S1/Words/ReturnWords/GoldenGapFirstReturn
   generality: I
   mirror-B: none(waiver:formal-interface-awaits-first-return-dichotomy)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden occurrence gaps are cylinder first returns, with complete length-two spectra. -/

import D5.S1.Words.ReturnWords.GoldenOccurrenceGaps

namespace D5.S1.Words

open Set

private theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  simp

/-- Positive first-return times to a numbered golden factor cylinder. -/
def goldenRankFirstReturnGapSet (n r : Nat) : Set Nat :=
  {d | 0 < d ∧ ∃ i, goldenCylinderRank n i = r ∧
    goldenCylinderRank n (i + d) = r ∧
      ∀ e, 0 < e → e < d → goldenCylinderRank n (i + e) ≠ r}

/-- Factor-occurrence gaps are exactly first-return times to the corresponding cylinder. -/
theorem golden_occurrence_gap_set_eq_rank_first_return_gap_set {n i₀ : Nat}
    {w : List Bool} (hw : goldenFactor n i₀ = w) :
    goldenOccurrenceGapSet n w =
      goldenRankFirstReturnGapSet n (goldenCylinderRank n i₀) := by
  ext d
  constructor
  · rintro ⟨i, j, hadj, rfl⟩
    have hs := adjacent_golden_occurrences_iff.mp hadj
    refine ⟨Nat.sub_pos_of_lt hs.1, i, ?_, ?_, ?_⟩
    · exact (golden_factor_eq_iff_cylinder_rank_eq n i i₀).mp
        (hs.2.1.trans hw.symm)
    · rw [Nat.add_sub_of_le hs.1.le]
      exact (golden_factor_eq_iff_cylinder_rank_eq n j i₀).mp
        (hs.2.2.1.trans hw.symm)
    · intro e hepos helt hrank
      have hfactor : goldenFactor n (i + e) = w :=
        ((golden_factor_eq_iff_cylinder_rank_eq n (i + e) i₀).mpr hrank).trans hw
      have hmem : i + e ∈ (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hfactor⟩
      rw [hs.2.2.2] at hmem
      simp at hmem
  · rintro ⟨hdpos, i, hstart, hend, hfirst⟩
    refine ⟨i, i + d, adjacent_golden_occurrences_iff.mpr ?_, by omega⟩
    refine ⟨by omega, ?_, ?_, Finset.filter_eq_empty_iff.mpr ?_⟩
    · exact ((golden_factor_eq_iff_cylinder_rank_eq n i i₀).mpr hstart).trans hw
    · exact ((golden_factor_eq_iff_cylinder_rank_eq n (i + d) i₀).mpr hend).trans hw
    · intro k hk hfactor
      have hk' := Finset.mem_Ioo.mp hk
      have hrank : goldenCylinderRank n k = goldenCylinderRank n i₀ :=
        (golden_factor_eq_iff_cylinder_rank_eq n k i₀).mp (hfactor.trans hw.symm)
      apply hfirst (k - i)
      · omega
      · omega
      · simpa [Nat.add_sub_of_le hk'.1.le] using hrank

private theorem golden_mechanical_slope_eq_goldenRatio_sub_one :
    goldenMechanicalSlope = Real.goldenRatio - 1 := by
  rw [goldenMechanicalSlope, Real.inv_goldenRatio, ← Real.one_sub_goldenConj]
  ring

private theorem golden_mechanical_slope_bounds :
    0 < goldenMechanicalSlope ∧
      1 < 2 * goldenMechanicalSlope ∧
      3 * goldenMechanicalSlope < 2 ∧
      3 < 5 * goldenMechanicalSlope ∧
      goldenMechanicalSlope < 1 := by
  rw [golden_mechanical_slope_eq_goldenRatio_sub_one, Real.goldenRatio]
  have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem fract_golden_mechanical_slope :
    Int.fract goldenMechanicalSlope = goldenMechanicalSlope := by
  exact Int.fract_eq_self.mpr
    ⟨golden_mechanical_slope_bounds.1.le, golden_mechanical_slope_bounds.2.2.2.2⟩

private theorem fract_two_mul_golden_mechanical_slope :
    Int.fract (2 * goldenMechanicalSlope) = 2 * goldenMechanicalSlope - 1 := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by linarith [golden_mechanical_slope_bounds.2.1],
    by linarith [golden_mechanical_slope_bounds.2.2.1], 1, ?_⟩
  norm_num

private theorem golden_cylinder_breakpoints_two_order :
    0 < 1 - goldenMechanicalSlope ∧
      1 - goldenMechanicalSlope < 2 - 2 * goldenMechanicalSlope ∧
      2 - 2 * goldenMechanicalSlope < 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    linarith [golden_mechanical_slope_bounds.2.1,
      golden_mechanical_slope_bounds.2.2.2.2]

private theorem golden_cylinder_rank_two (i : Nat) :
    goldenCylinderRank 2 i =
      if 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i then 2
      else if 1 - goldenMechanicalSlope ≤ goldenPhase i then 1 else 0 := by
  classical
  change
    (((Finset.range 2).image fun m : Nat =>
      1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)).filter
        (fun x => x ≤ goldenPhase i)).card = _
  have hzero :
      1 - Int.fract ((((0 + 1 : Nat) : Real) * goldenMechanicalSlope)) =
        1 - goldenMechanicalSlope := by
    norm_num [fract_golden_mechanical_slope]
  have hone :
      1 - Int.fract ((((1 + 1 : Nat) : Real) * goldenMechanicalSlope)) =
        2 - 2 * goldenMechanicalSlope := by
    norm_num [fract_two_mul_golden_mechanical_slope]
    ring
  have hbreak :
      (Finset.range 2).image (fun m : Nat =>
        1 - Int.fract (((m + 1 : Nat) : Real) * goldenMechanicalSlope)) =
          {1 - goldenMechanicalSlope, 2 - 2 * goldenMechanicalSlope} := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have hm' : m = 0 ∨ m = 1 := by
        have := Finset.mem_range.mp hm
        omega
      rcases hm' with rfl | rfl
      · rw [hzero]
        simp
      · rw [hone]
        simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, by decide, hzero⟩
      · exact Finset.mem_image.mpr ⟨1, by decide, hone⟩
  rw [hbreak]
  have hne : 1 - goldenMechanicalSlope ≠ 2 - 2 * goldenMechanicalSlope :=
    ne_of_lt golden_cylinder_breakpoints_two_order.2.1
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i :=
      golden_cylinder_breakpoints_two_order.2.1.le.trans hhigh
    simp only [Finset.filter_insert, Finset.filter_singleton]
    simp [hhigh, hlow, hne]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i
    · simp only [Finset.filter_insert, Finset.filter_singleton]
      simp [hhigh, hlow]
    · simp only [Finset.filter_insert, Finset.filter_singleton]
      simp [hhigh, hlow]

private theorem golden_cylinder_rank_two_eq_zero_iff (i : Nat) :
    goldenCylinderRank 2 i = 0 ↔ goldenPhase i < 1 - goldenMechanicalSlope := by
  rw [golden_cylinder_rank_two]
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i :=
      golden_cylinder_breakpoints_two_order.2.1.le.trans hhigh
    simp [hhigh, hlow]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i
    · simp [hhigh, hlow]
    · simp [hhigh, hlow, lt_of_not_ge hlow]

private theorem golden_cylinder_rank_two_eq_one_iff (i : Nat) :
    goldenCylinderRank 2 i = 1 ↔
      goldenPhase i ∈ Ico (1 - goldenMechanicalSlope)
        (2 - 2 * goldenMechanicalSlope) := by
  rw [golden_cylinder_rank_two]
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i :=
      golden_cylinder_breakpoints_two_order.2.1.le.trans hhigh
    simp [hhigh, hlow]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i
    · simp [hhigh, hlow, lt_of_not_ge hhigh]
    · simp [hhigh, hlow]

private theorem golden_cylinder_rank_two_eq_two_iff (i : Nat) :
    goldenCylinderRank 2 i = 2 ↔ 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i := by
  rw [golden_cylinder_rank_two]
  by_cases hhigh : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase i
  · simp [hhigh]
  · by_cases hlow : 1 - goldenMechanicalSlope ≤ goldenPhase i <;>
      simp [hhigh, hlow]

private theorem golden_phase_add (i d : Nat) :
    goldenPhase (i + d) =
      Int.fract (goldenPhase i + (d : Real) * goldenMechanicalSlope) := by
  rw [goldenPhase, goldenPhase]
  have harg : (((i + d + 1 : Nat) : Real) * goldenMechanicalSlope) =
      (((i + 1 : Nat) : Real) * goldenMechanicalSlope) +
        (d : Real) * goldenMechanicalSlope := by
    push_cast
    ring
  rw [harg]
  conv_lhs =>
    enter [1, 1]
    rw [← Int.floor_add_fract (((i + 1 : Nat) : Real) * goldenMechanicalSlope)]
  rw [add_assoc, Int.fract_intCast_add]

private theorem golden_phase_add_eq_sub_nat (i d z : Nat)
    (hnonneg : 0 ≤ goldenPhase i + (d : Real) * goldenMechanicalSlope - z)
    (hlt : goldenPhase i + (d : Real) * goldenMechanicalSlope - z < 1) :
    goldenPhase (i + d) =
      goldenPhase i + (d : Real) * goldenMechanicalSlope - z := by
  rw [golden_phase_add]
  apply Int.fract_eq_iff.mpr
  refine ⟨hnonneg, hlt, (z : Int), ?_⟩
  push_cast
  ring

private theorem rank_first_return_time_unique {n r i d e : Nat}
    (hdpos : 0 < d) (hdreturn : goldenCylinderRank n (i + d) = r)
    (hdfirst : ∀ k, 0 < k → k < d → goldenCylinderRank n (i + k) ≠ r)
    (hepos : 0 < e) (hereturn : goldenCylinderRank n (i + e) = r)
    (hefirst : ∀ k, 0 < k → k < e → goldenCylinderRank n (i + k) ≠ r) :
    d = e := by
  rcases lt_trichotomy d e with hde | hde | hed
  · exact False.elim (hefirst d hdpos hde hdreturn)
  · exact hde
  · exact False.elim (hdfirst e hepos hed hereturn)

private theorem golden_phase_nonneg (i : Nat) : 0 ≤ goldenPhase i := by
  exact Int.fract_nonneg _

private theorem golden_phase_lt_one (i : Nat) : goldenPhase i < 1 := by
  exact Int.fract_lt_one _

private theorem golden_rank_two_zero_first_return_cases (i : Nat)
    (hi : goldenCylinderRank 2 i = 0) :
    (goldenCylinderRank 2 (i + 2) = 0 ∧ goldenCylinderRank 2 (i + 1) ≠ 0) ∨
      (goldenCylinderRank 2 (i + 3) = 0 ∧ goldenCylinderRank 2 (i + 1) ≠ 0 ∧
        goldenCylinderRank 2 (i + 2) ≠ 0) := by
  have hxlt := (golden_cylinder_rank_two_eq_zero_iff i).mp hi
  have hphase1 : goldenPhase (i + 1) =
      goldenPhase i + goldenMechanicalSlope := by
    simpa using golden_phase_add_eq_sub_nat i 1 0
      (by norm_num; linarith [golden_phase_nonneg i, golden_mechanical_slope_bounds.1])
      (by norm_num; linarith)
  have hnot1 : goldenCylinderRank 2 (i + 1) ≠ 0 := by
    intro hrank
    have hphase := (golden_cylinder_rank_two_eq_zero_iff _).mp hrank
    rw [hphase1] at hphase
    linarith [golden_phase_nonneg i, golden_mechanical_slope_bounds.2.1]
  have hphase2 : goldenPhase (i + 2) =
      goldenPhase i + 2 * goldenMechanicalSlope - 1 := by
    simpa using golden_phase_add_eq_sub_nat i 2 1
      (by norm_num; linarith [golden_phase_nonneg i, golden_mechanical_slope_bounds.2.1])
      (by norm_num; linarith [golden_mechanical_slope_bounds.2.2.2.2])
  by_cases hreturn2 : goldenCylinderRank 2 (i + 2) = 0
  · exact Or.inl ⟨hreturn2, hnot1⟩
  · have hphase2_ge : 1 - goldenMechanicalSlope ≤ goldenPhase (i + 2) := by
      exact not_lt.mp (fun h => hreturn2 ((golden_cylinder_rank_two_eq_zero_iff _).mpr h))
    have hphase3 : goldenPhase (i + 3) =
        goldenPhase i + 3 * goldenMechanicalSlope - 2 := by
      simpa using golden_phase_add_eq_sub_nat i 3 2
        (by norm_num; linarith)
        (by norm_num; linarith [golden_mechanical_slope_bounds.2.2.2.2])
    have hreturn3 : goldenCylinderRank 2 (i + 3) = 0 := by
      rw [golden_cylinder_rank_two_eq_zero_iff, hphase3]
      linarith [golden_mechanical_slope_bounds.2.2.1]
    exact Or.inr ⟨hreturn3, hnot1, hreturn2⟩

private theorem golden_rank_two_one_first_return_cases (i : Nat)
    (hi : goldenCylinderRank 2 i = 1) :
    (goldenCylinderRank 2 (i + 2) = 1 ∧ goldenCylinderRank 2 (i + 1) ≠ 1) ∨
      (goldenCylinderRank 2 (i + 3) = 1 ∧ goldenCylinderRank 2 (i + 1) ≠ 1 ∧
        goldenCylinderRank 2 (i + 2) ≠ 1) := by
  have hx := (golden_cylinder_rank_two_eq_one_iff i).mp hi
  have hxlow := hx.1
  have hxhigh := hx.2
  have hphase1 : goldenPhase (i + 1) =
      goldenPhase i + goldenMechanicalSlope - 1 := by
    simpa using golden_phase_add_eq_sub_nat i 1 1
      (by norm_num; linarith [hxlow])
      (by norm_num; linarith [hxhigh, golden_mechanical_slope_bounds.1])
  have hnot1 : goldenCylinderRank 2 (i + 1) ≠ 1 := by
    intro hrank
    have hphase := (golden_cylinder_rank_two_eq_one_iff _).mp hrank
    rw [hphase1] at hphase
    linarith [hphase.1, hxhigh]
  have hphase2 : goldenPhase (i + 2) =
      goldenPhase i + 2 * goldenMechanicalSlope - 1 := by
    simpa using golden_phase_add_eq_sub_nat i 2 1
      (by norm_num; linarith [hxlow, golden_mechanical_slope_bounds.1])
      (by norm_num; linarith [hxhigh])
  by_cases hreturn2 : goldenCylinderRank 2 (i + 2) = 1
  · exact Or.inl ⟨hreturn2, hnot1⟩
  · have hphase2_ge : 2 - 2 * goldenMechanicalSlope ≤ goldenPhase (i + 2) := by
      have hlow : 1 - goldenMechanicalSlope ≤ goldenPhase (i + 2) := by
        rw [hphase2]
        linarith [hxlow, golden_mechanical_slope_bounds.2.1]
      by_contra hhigh
      exact hreturn2 ((golden_cylinder_rank_two_eq_one_iff _).mpr
        ⟨hlow, lt_of_not_ge hhigh⟩)
    have hphase3 : goldenPhase (i + 3) =
        goldenPhase i + 3 * goldenMechanicalSlope - 2 := by
      simpa using golden_phase_add_eq_sub_nat i 3 2
        (by norm_num; linarith [hxlow, golden_mechanical_slope_bounds.2.1])
        (by norm_num; linarith [hxhigh, golden_mechanical_slope_bounds.2.2.2.2])
    have hreturn3 : goldenCylinderRank 2 (i + 3) = 1 := by
      rw [golden_cylinder_rank_two_eq_one_iff, hphase3]
      constructor
      · linarith [hphase2_ge]
      · linarith [hxhigh, golden_mechanical_slope_bounds.2.2.1]
    exact Or.inr ⟨hreturn3, hnot1, hreturn2⟩

private theorem golden_rank_two_two_first_return_cases (i : Nat)
    (hi : goldenCylinderRank 2 i = 2) :
    (goldenCylinderRank 2 (i + 3) = 2 ∧
        goldenCylinderRank 2 (i + 1) ≠ 2 ∧ goldenCylinderRank 2 (i + 2) ≠ 2) ∨
      (goldenCylinderRank 2 (i + 5) = 2 ∧
        goldenCylinderRank 2 (i + 1) ≠ 2 ∧ goldenCylinderRank 2 (i + 2) ≠ 2 ∧
        goldenCylinderRank 2 (i + 3) ≠ 2 ∧ goldenCylinderRank 2 (i + 4) ≠ 2) := by
  have hxge := (golden_cylinder_rank_two_eq_two_iff i).mp hi
  have hphase1 : goldenPhase (i + 1) =
      goldenPhase i + goldenMechanicalSlope - 1 := by
    simpa using golden_phase_add_eq_sub_nat i 1 1
      (by norm_num; linarith [hxge, golden_mechanical_slope_bounds.2.2.2.2])
      (by norm_num; linarith [golden_phase_lt_one i,
        golden_mechanical_slope_bounds.2.2.2.2])
  have hnot1 : goldenCylinderRank 2 (i + 1) ≠ 2 := by
    intro hrank
    have hphase := (golden_cylinder_rank_two_eq_two_iff _).mp hrank
    rw [hphase1] at hphase
    linarith [golden_phase_lt_one i, golden_mechanical_slope_bounds.2.2.1]
  have hphase2 : goldenPhase (i + 2) =
      goldenPhase i + 2 * goldenMechanicalSlope - 2 := by
    simpa using golden_phase_add_eq_sub_nat i 2 2
      (by norm_num; linarith)
      (by norm_num; linarith [golden_phase_lt_one i, golden_mechanical_slope_bounds.2.1,
        golden_mechanical_slope_bounds.2.2.2.2])
  have hnot2 : goldenCylinderRank 2 (i + 2) ≠ 2 := by
    intro hrank
    have hphase := (golden_cylinder_rank_two_eq_two_iff _).mp hrank
    rw [hphase2] at hphase
    linarith [golden_phase_lt_one i, golden_mechanical_slope_bounds.2.2.1]
  have hphase3 : goldenPhase (i + 3) =
      goldenPhase i + 3 * goldenMechanicalSlope - 2 := by
    simpa using golden_phase_add_eq_sub_nat i 3 2
      (by norm_num; linarith [golden_mechanical_slope_bounds.1])
      (by norm_num; linarith [golden_phase_lt_one i,
        golden_mechanical_slope_bounds.2.2.1])
  by_cases hreturn3 : goldenCylinderRank 2 (i + 3) = 2
  · exact Or.inl ⟨hreturn3, hnot1, hnot2⟩
  · have hphase3_lt : goldenPhase (i + 3) < 2 - 2 * goldenMechanicalSlope := by
      exact lt_of_not_ge (fun h => hreturn3 ((golden_cylinder_rank_two_eq_two_iff _).mpr h))
    have hphase4 : goldenPhase (i + 4) =
        goldenPhase i + 4 * goldenMechanicalSlope - 3 := by
      simpa using golden_phase_add_eq_sub_nat i 4 3
        (by norm_num; linarith [golden_mechanical_slope_bounds.2.1])
        (by norm_num; linarith [golden_phase_lt_one i,
          golden_mechanical_slope_bounds.2.2.1])
    have hnot4 : goldenCylinderRank 2 (i + 4) ≠ 2 := by
      intro hrank
      have hphase := (golden_cylinder_rank_two_eq_two_iff _).mp hrank
      rw [hphase4] at hphase
      linarith [golden_phase_lt_one i, golden_mechanical_slope_bounds.2.2.1]
    have hphase5 : goldenPhase (i + 5) =
        goldenPhase i + 5 * goldenMechanicalSlope - 3 := by
      simpa using golden_phase_add_eq_sub_nat i 5 3
        (by norm_num; linarith [golden_mechanical_slope_bounds.2.2.2.1])
        (by norm_num; rw [hphase3] at hphase3_lt; linarith)
    have hreturn5 : goldenCylinderRank 2 (i + 5) = 2 := by
      rw [golden_cylinder_rank_two_eq_two_iff, hphase5]
      linarith [golden_mechanical_slope_bounds.2.2.2.1]
    exact Or.inr ⟨hreturn5, hnot1, hnot2, hreturn3, hnot4⟩

private theorem golden_rank_first_return_gap_two_zero_cases {d : Nat}
    (hd : d ∈ goldenRankFirstReturnGapSet 2 0) : d = 2 ∨ d = 3 := by
  obtain ⟨hdpos, i, hstart, hdreturn, hdfirst⟩ := hd
  rcases golden_rank_two_zero_first_return_cases i hstart with htwo | hthree
  · left
    apply rank_first_return_time_unique hdpos hdreturn hdfirst (by decide) htwo.1
    intro k hkpos hklt
    have hk : k = 1 := by omega
    subst k
    exact htwo.2
  · right
    apply rank_first_return_time_unique hdpos hdreturn hdfirst (by decide) hthree.1
    intro k hkpos hklt
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · exact hthree.2.1
    · exact hthree.2.2

private theorem golden_rank_first_return_gap_two_one_cases {d : Nat}
    (hd : d ∈ goldenRankFirstReturnGapSet 2 1) : d = 2 ∨ d = 3 := by
  obtain ⟨hdpos, i, hstart, hdreturn, hdfirst⟩ := hd
  rcases golden_rank_two_one_first_return_cases i hstart with htwo | hthree
  · left
    apply rank_first_return_time_unique hdpos hdreturn hdfirst (by decide) htwo.1
    intro k hkpos hklt
    have hk : k = 1 := by omega
    subst k
    exact htwo.2
  · right
    apply rank_first_return_time_unique hdpos hdreturn hdfirst (by decide) hthree.1
    intro k hkpos hklt
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · exact hthree.2.1
    · exact hthree.2.2

private theorem golden_rank_first_return_gap_two_two_cases {d : Nat}
    (hd : d ∈ goldenRankFirstReturnGapSet 2 2) : d = 3 ∨ d = 5 := by
  obtain ⟨hdpos, i, hstart, hdreturn, hdfirst⟩ := hd
  rcases golden_rank_two_two_first_return_cases i hstart with hthree | hfive
  · left
    apply rank_first_return_time_unique hdpos hdreturn hdfirst (by decide) hthree.1
    intro k hkpos hklt
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · exact hthree.2.1
    · exact hthree.2.2
  · right
    apply rank_first_return_time_unique hdpos hdreturn hdfirst (by decide) hfive.1
    intro k hkpos hklt
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · exact hfive.2.1
    · exact hfive.2.2.1
    · exact hfive.2.2.2.1
    · exact hfive.2.2.2.2

private theorem fract_three_mul_golden_mechanical_slope :
    Int.fract (3 * goldenMechanicalSlope) = 3 * goldenMechanicalSlope - 1 := by
  apply Int.fract_eq_iff.mpr
  refine ⟨by linarith [golden_mechanical_slope_bounds.2.1],
    by linarith [golden_mechanical_slope_bounds.2.2.1], 1, ?_⟩
  norm_num

private theorem golden_cylinder_rank_two_zero : goldenCylinderRank 2 1 = 0 := by
  rw [golden_cylinder_rank_two_eq_zero_iff]
  simp [goldenPhase, fract_two_mul_golden_mechanical_slope]
  linarith [golden_mechanical_slope_bounds.2.2.1]

private theorem golden_cylinder_rank_two_one : goldenCylinderRank 2 0 = 1 := by
  rw [golden_cylinder_rank_two_eq_one_iff]
  simp [goldenPhase, fract_golden_mechanical_slope]
  constructor <;> linarith [golden_mechanical_slope_bounds.2.1,
    golden_mechanical_slope_bounds.2.2.1]

private theorem golden_cylinder_rank_two_two : goldenCylinderRank 2 2 = 2 := by
  rw [golden_cylinder_rank_two_eq_two_iff]
  simp [goldenPhase, fract_three_mul_golden_mechanical_slope]
  linarith [golden_mechanical_slope_bounds.2.2.2.1]

/-- The `TF` factor has adjacent-start gaps exactly two and three. -/
theorem golden_occurrence_gap_set_two_true_false :
    goldenOccurrenceGapSet 2 [true, false] = {2, 3} := by
  have hfactor : goldenFactor 2 0 = [true, false] := by decide
  ext d
  constructor
  · intro hd
    have hrank : d ∈ goldenRankFirstReturnGapSet 2 1 := by
      rw [← golden_cylinder_rank_two_one,
        ← golden_occurrence_gap_set_eq_rank_first_return_gap_set hfactor]
      exact hd
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      golden_rank_first_return_gap_two_one_cases hrank
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact ⟨3, 5, by decide, by decide⟩
    · exact ⟨0, 3, by decide, by decide⟩

/-- The `FT` factor has adjacent-start gaps exactly two and three. -/
theorem golden_occurrence_gap_set_two_false_true :
    goldenOccurrenceGapSet 2 [false, true] = {2, 3} := by
  have hfactor : goldenFactor 2 1 = [false, true] := by decide
  ext d
  constructor
  · intro hd
    have hrank : d ∈ goldenRankFirstReturnGapSet 2 0 := by
      rw [← golden_cylinder_rank_two_zero,
        ← golden_occurrence_gap_set_eq_rank_first_return_gap_set hfactor]
      exact hd
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      golden_rank_first_return_gap_two_zero_cases hrank
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact ⟨4, 6, by decide, by decide⟩
    · exact ⟨1, 4, by decide, by decide⟩

/-- The `TT` factor has adjacent-start gaps exactly three and five. -/
theorem golden_occurrence_gap_set_two_true_true :
    goldenOccurrenceGapSet 2 [true, true] = {3, 5} := by
  have hfactor : goldenFactor 2 2 = [true, true] := by decide
  ext d
  constructor
  · intro hd
    have hrankRaw :
        d ∈ goldenRankFirstReturnGapSet 2 (goldenCylinderRank 2 2) := by
      rw [← golden_occurrence_gap_set_eq_rank_first_return_gap_set hfactor]
      exact hd
    have hrank : d ∈ goldenRankFirstReturnGapSet 2 2 := by
      simpa only [golden_cylinder_rank_two_two] using hrankRaw
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      golden_rank_first_return_gap_two_two_cases hrank
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact ⟨7, 10, by decide, by decide⟩
    · exact ⟨2, 7, by decide, by decide⟩

private theorem golden_factor_set_two :
    goldenFactorSet 2 = {[true, false], [false, true], [true, true]} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact mem_goldenFactorSet.mpr ⟨0, by decide⟩
    · exact mem_goldenFactorSet.mpr ⟨1, by decide⟩
    · exact mem_goldenFactorSet.mpr ⟨2, by decide⟩
  · rw [golden_factor_complexity]
    decide

/-- Every occurring length-two golden factor has exactly two adjacent-gap values. -/
theorem golden_occurrence_gap_set_two_encard_eq_two {w : List Bool}
    (hw : w ∈ goldenFactorSet 2) : (goldenOccurrenceGapSet 2 w).encard = 2 := by
  rw [golden_factor_set_two] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · rw [golden_occurrence_gap_set_two_true_false]
    exact Set.encard_pair (by decide)
  · rw [golden_occurrence_gap_set_two_false_true]
    exact Set.encard_pair (by decide)
  · rw [golden_occurrence_gap_set_two_true_true]
    exact Set.encard_pair (by decide)

#print axioms golden_occurrence_gap_set_eq_rank_first_return_gap_set
#print axioms golden_occurrence_gap_set_two_true_false
#print axioms golden_occurrence_gap_set_two_false_true
#print axioms golden_occurrence_gap_set_two_true_true
#print axioms golden_occurrence_gap_set_two_encard_eq_two

end D5.S1.Words
