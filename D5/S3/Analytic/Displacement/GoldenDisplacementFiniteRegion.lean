/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementFiniteRegion
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves positive slope is necessary and reduces convergence to finitely many tests. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementSurfaceExactRegion

open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDisplacementEulerProduct
open GoldenDisplacementSurfaceExactRegion
open GoldenSubstStartSharpness

namespace GoldenDisplacementFiniteRegion

noncomputable section

/-- Summability forces positive displacement slope along the golden ray. -/
theorem dTerm_summable_slope_pos {s w : ℝ} (hsum : Summable (dTerm s w)) :
    0 < s * Real.goldenRatio + w := by
  have hexact := (dTerm_summable_iff s w).mp hsum
  by_cases hs : 0 ≤ s
  · have htwo := hexact 1
    have hstart : goldenSubstStart 2 = 3 := by decide
    have hphi : (3 : ℝ) / 2 < Real.goldenRatio := by
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
        Real.goldenRatio_lt_two]
    norm_num [hstart] at htwo
    nlinarith
  · have hsneg : s < 0 := lt_of_not_ge hs
    by_contra hnot
    have hcle : s * Real.goldenRatio + w ≤ 0 := le_of_not_gt hnot
    obtain ⟨v, hv⟩ := golden_subst_start_error_upper_sharp
      Real.goldenRatio⁻¹ (inv_pos.mpr Real.goldenRatio_pos)
    have herr :
        0 < (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) := by
      linarith
    cases v with
    | zero => simp [goldenSubstStart_zero] at herr
    | succ k =>
        have hscaled :
            (s * Real.goldenRatio + w) * ((k + 1 : ℕ) : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hcle (by positivity)
        have herror : s *
            ((goldenSubstStart (k + 1) : ℝ) -
              Real.goldenRatio * ((k + 1 : ℕ) : ℝ)) < 0 :=
          mul_neg_of_neg_of_pos hsneg herr
        have hexponent := hexact k
        norm_num [Nat.cast_add, Nat.cast_one] at hscaled herror hexponent
        nlinarith

/-! SEARCH RECEIPT

For the forward implication below, exact-word search found
`GoldenDisplacementSurfaceExactRegion.dTerm_summable_iff`, whose forward implication gives every
constraint and hence the initial block. For the reverse implication, exact-word searches for
`dTerm_summable_iff_finite_of_slope_pos`, `summable_iff_finite`, `not_summable`, `divergent`, and
`diverges` found no supplied-threshold finite theorem. The same exact criterion reduces that
direction to the omitted tail, while `golden_subst_start_error_window` supplies its quantitative
bound. The frozen theorem `dTerm_not_summable_of_two_mul_add_le_one` only yields the necessary
condition `1 < 2 * s + w` by contraposition, not the reverse implication needed here.
-/

/-- A positive golden slope makes every constraint past the explicit threshold automatic. -/
theorem dTerm_constraint_of_slope_pos_of_threshold {s w : ℝ}
    (hc : 0 < s * Real.goldenRatio + w) (k : ℕ)
    (hk : (1 + |s| * Real.goldenRatio⁻¹) /
      (s * Real.goldenRatio + w) < (k + 1 : ℝ)) :
    1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1) := by
  let c : ℝ := s * Real.goldenRatio + w
  let q : ℝ := Real.goldenRatio⁻¹
  have hc' : 0 < c := by simpa [c] using hc
  have hqpos : 0 < q := by
    simpa [q] using inv_pos.mpr Real.goldenRatio_pos
  have hqle : q ≤ 1 := by
    exact (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio).le
  have hqsq : q ^ 2 ≤ q := by nlinarith
  let e : ℝ :=
    (goldenSubstStart (k + 1) : ℝ) -
      Real.goldenRatio * ((k + 1 : ℕ) : ℝ)
  have hwindow := golden_subst_start_error_window (k + 1)
  have helower : -q ≤ e := by
    dsimp [e, q]
    dsimp [q] at hqsq
    nlinarith [hwindow.1]
  have heupper : e ≤ q := by
    simpa [e, q] using hwindow.2
  have heabs : |e| ≤ q := abs_le.mpr ⟨helower, heupper⟩
  have hprodAbs : |s * e| ≤ |s| * q := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left heabs (abs_nonneg s)
  have hprodLower : -(|s| * q) ≤ s * e := (abs_le.mp hprodAbs).1
  have hthreshold : (1 + |s| * q) / c < ((k + 1 : ℕ) : ℝ) := by
    simpa [c, q] using hk
  have hlinear : 1 + |s| * q < c * ((k + 1 : ℕ) : ℝ) := by
    have := (div_lt_iff₀ hc').mp hthreshold
    nlinarith
  have heq :
      s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1) =
        c * ((k + 1 : ℕ) : ℝ) + s * e := by
    dsimp [c, e]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  rw [heq]
  nlinarith

/-- A supplied cutoff meeting the explicit bound reduces summability to its initial block. -/
theorem dTerm_summable_iff_finite_of_slope_pos {s w : ℝ}
    (hc : 0 < s * Real.goldenRatio + w) (N : ℕ)
    (hN : (1 + |s| * Real.goldenRatio⁻¹) /
      (s * Real.goldenRatio + w) ≤ (N + 1 : ℝ)) :
    Summable (dTerm s w) ↔
      ∀ k ≤ N, 1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1) := by
  rw [dTerm_summable_iff]
  constructor
  · intro hall k _
    exact hall k
  · intro hfinite k
    by_cases hk : k ≤ N
    · exact hfinite k hk
    · have hNk : N + 1 < k + 1 := Nat.add_lt_add_right (Nat.lt_of_not_ge hk) 1
      have hNkReal : (N + 1 : ℝ) < (k + 1 : ℝ) := by exact_mod_cast hNk
      exact dTerm_constraint_of_slope_pos_of_threshold hc k (hN.trans_lt hNkReal)

end

end GoldenDisplacementFiniteRegion
