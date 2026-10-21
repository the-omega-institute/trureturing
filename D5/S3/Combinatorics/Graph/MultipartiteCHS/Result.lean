/- GID: D5/S3/Combinatorics/Graph/MultipartiteCHS/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MultipartiteCHS/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: The complete multipartite CHS norm has strict fixed-part-count extrema. -/

import D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
import D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal

/-! The fixed-part-count complete multipartite CHS norm extremum. -/

namespace D5.S3.Combinatorics.Graph.MultipartiteCHS.Result

open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal

theorem result : claim := by
  intro r n m hr hrn hm a ha hsum
  have hminparts : ∀ i, 0 < minParts r n i := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · simp [minParts, hi]
    · simp [minParts, hi]
  have hbalparts : ∀ i, 0 < balancedParts r n i := by
    intro i
    simp only [balancedParts]
    have hdiv : 1 ≤ n / r :=
      (Nat.le_div_iff_mul_le (by omega : 0 < r)).2 (by simpa using hrn)
    omega
  have hminpos : 0 < recH (minParts r n) (2 * m) :=
    recH_two_mul_pos hr _ hminparts hm
  have haposh : 0 < recH a (2 * m) := recH_two_mul_pos hr a ha hm
  have hbalpos : 0 < recH (balancedParts r n) (2 * m) :=
    recH_two_mul_pos hr _ hbalparts hm
  have hex := recH_extremal hr hrn hm a ha hsum
  have hexp : 0 < (1 : ℝ) / (2 * m : ℝ) := by positivity
  have rpow_inj : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y →
      x ^ ((1 : ℝ) / (2 * m : ℝ)) = y ^ ((1 : ℝ) / (2 * m : ℝ)) → x = y := by
    intro x y hx hy hxy
    have hd : (2 * m : ℝ) ≠ 0 := by positivity
    have hmul : (1 : ℝ) / (2 * m : ℝ) * (2 * m : ℝ) = 1 := by
      field_simp
    have hpow := congrArg (fun z : ℝ => z ^ (2 * m : ℝ)) hxy
    rw [← Real.rpow_mul hx, ← Real.rpow_mul hy, hmul] at hpow
    simpa only [Real.rpow_one] using hpow
  constructor
  · constructor
    · dsimp [chsNorm]
      rw [chs_eq_recH, chs_eq_recH]
      have hexp' : 0 ≤ (1 : ℝ) / (↑(2 * m) : ℝ) := by positivity
      exact Real.rpow_le_rpow (le_of_lt hminpos) hex.1.1 hexp'
    · intro heq
      apply hex.1.2
      apply rpow_inj (le_of_lt haposh) (le_of_lt hminpos)
      simpa [chsNorm, chs_eq_recH] using heq
  · constructor
    · dsimp [chsNorm]
      rw [chs_eq_recH, chs_eq_recH]
      have hexp' : 0 ≤ (1 : ℝ) / (↑(2 * m) : ℝ) := by positivity
      exact Real.rpow_le_rpow (le_of_lt haposh) hex.2.1 hexp'
    · intro heq
      apply hex.2.2
      apply rpow_inj (le_of_lt haposh) (le_of_lt hbalpos)
      simpa [chsNorm, chs_eq_recH] using heq

end D5.S3.Combinatorics.Graph.MultipartiteCHS.Result
