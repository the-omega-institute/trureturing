/- GID: D5/S3/ArithSums/GiniStationaryTest/Result
   generality: I
   mirror-B: D5/B/S3/ArithSums/GiniStationaryTest/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithSums/GiniStationaryTest/Defs.claim; result=D5/S3/ArithSums/GiniStationaryTest/Result.result; claim=D5/S3/ArithSums/GiniStationaryTest/Defs.claim
   digest: Stationary tests do not characterize Gini comparisons on the positive half-line. -/

import D5.S3.ArithSums.GiniStationaryTest.Stationary
import D5.S3.ArithSums.GiniStationaryTest.Witness

/-! A stationary-test family that contradicts universal Gini comparison. -/

noncomputable section
open D5.S3.ArithSums.GiniStationaryTest.Defs

namespace D5.S3.ArithSums.GiniStationaryTest.Result

/-- In every dimension at least three the stationary test holds but comparison fails. -/
theorem counterexample_family (n : ℕ) (hn : 3 ≤ n) :
    stationaryTest n 1 0 2 (-1) ∧
      (((1, 0), (2, -1)) : (ℝ × ℝ) × (ℝ × ℝ)) ∉ Gamma n (Set.Ioi 0) := by
  exact ⟨Stationary.stationaryTest_one_zero_two_negOne n (by omega),
    Witness.not_mem_Gamma n hn⟩

/-- The stationary characterization of Gini comparisons is false. -/
theorem result : ¬ claim := by
  intro h
  have hInf : sInf ((fun z : ℝ × ℝ => z.1 / z.2) ''
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi 0)) = 0 := by
    have he : ((fun z : ℝ × ℝ => z.1 / z.2) ''
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi 0)) = Set.Ioi 0 := by
      ext y
      constructor
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        change 0 < a at ha
        change 0 < b at hb
        change 0 < a / b
        exact div_pos ha hb
      · intro hy
        exact ⟨(y, 1), ⟨hy, by norm_num⟩, by simp⟩
    rw [he]
    exact csInf_Ioi
  have hiff := h 3 le_rfl (Set.Ioi 0) (fun _ hx => hx) (inferInstance)
    ⟨1, by norm_num⟩ hInf 1 0 2 (-1)
  obtain ⟨hstationary, hfailure⟩ := counterexample_family 3 le_rfl
  exact hfailure (hiff.mpr hstationary)

end D5.S3.ArithSums.GiniStationaryTest.Result
