/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementRedundantConstraint
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves a positive-slope golden displacement constraint is redundant. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementFiniteRegion
import D5.S3.Analytic.Displacement.GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

open D5.S1.Words
open D5.S1.Words.Powers
open D5.S0.Tower.GoldenGapWord
open GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

namespace GoldenDisplacementRedundantConstraint

/-- Discrete concavity is the general mechanism making the middle affine constraint
follow from its neighbors when the scale is nonnegative. -/
theorem golden_displacement_constraint_of_neighbors
    {s w : ℝ} (hs : 0 ≤ s) (v : ℕ)
    (hconcave :
      (goldenSubstStart v : ℝ) + (goldenSubstStart (v + 2) : ℝ) ≤
        2 * (goldenSubstStart (v + 1) : ℝ))
    (hleft : 1 < s * (goldenSubstStart v : ℝ) + w * v)
    (hright :
      1 < s * (goldenSubstStart (v + 2) : ℝ) + w * (v + 2)) :
    1 < s * (goldenSubstStart (v + 1) : ℝ) + w * (v + 1) := by
  have hgain : 0 ≤ s *
      (2 * (goldenSubstStart (v + 1) : ℝ) -
        ((goldenSubstStart v : ℝ) + (goldenSubstStart (v + 2) : ℝ))) :=
    mul_nonneg hs (by linarith)
  nlinarith

/-- For `goldenSubstStart`, concavity makes the right-neighbor premise redundant. -/
theorem goldenSubstStart_constraint_of_left
    {s w : ℝ} (hs : 0 ≤ s) (v : ℕ)
    (hconcave :
      (goldenSubstStart v : ℝ) + (goldenSubstStart (v + 2) : ℝ) ≤
        2 * (goldenSubstStart (v + 1) : ℝ))
    (hleft : 1 < s * (goldenSubstStart v : ℝ) + w * v) :
    1 < s * (goldenSubstStart (v + 1) : ℝ) + w * (v + 1) := by
  cases v with
  | zero =>
      norm_num [goldenSubstStart, goldenWindowTrueCount] at hleft
  | succ k =>
      let v := k + 1
      have hvNat : 1 ≤ v := by
        dsimp [v]
        omega
      have hleftV :
          1 < s * (goldenSubstStart v : ℝ) + w * v := by
        simpa [v] using hleft
      have hconcaveNat :
          goldenSubstStart v + goldenSubstStart (v + 2) ≤
            2 * goldenSubstStart (v + 1) := by
        exact_mod_cast hconcave
      have hfirst := goldenSubstStart_succ v
      have hsecond :
          goldenSubstStart (v + 2) = goldenSubstStart (v + 1) +
            (subst (goldenWord (v + 1))).length := by
        simpa [Nat.add_assoc] using goldenSubstStart_succ (v + 1)
      have hfirstLen : (subst (goldenWord v)).length = 2 := by
        by_cases hword : goldenWord v = true
        · simp [hword, subst]
        · have hfalse : goldenWord v = false := by
            simpa using hword
          have hnext := golden_no_two_false hfalse
          simp [hfalse, hnext, subst] at hfirst hsecond
          omega
      have hstepNat : goldenSubstStart (v + 1) = goldenSubstStart v + 2 := by
        simpa [hfirstLen] using hfirst
      have hstep :
          (goldenSubstStart (v + 1) : ℝ) = (goldenSubstStart v : ℝ) + 2 := by
        exact_mod_cast hstepNat
      have hgNat : goldenSubstStart v ≤ 2 * v :=
        goldenSubstStart_le_two_mul v
      have hg : (goldenSubstStart v : ℝ) ≤ 2 * (v : ℝ) := by
        exact_mod_cast hgNat
      have hgain :
          0 ≤ s * (2 * (v : ℝ) - (goldenSubstStart v : ℝ)) :=
        mul_nonneg hs (by linarith)
      have hidentity :
          (v : ℝ) *
                (s * (goldenSubstStart (v + 1) : ℝ) + w * (v + 1)) -
              ((v + 1 : ℕ) : ℝ) *
                (s * (goldenSubstStart v : ℝ) + w * v) =
            s * (2 * (v : ℝ) - (goldenSubstStart v : ℝ)) := by
        rw [hstep]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      have hscaled :
          ((v + 1 : ℕ) : ℝ) *
                (s * (goldenSubstStart v : ℝ) + w * v) ≤
            (v : ℝ) *
              (s * (goldenSubstStart (v + 1) : ℝ) + w * (v + 1)) := by
        nlinarith [hidentity, hgain]
      have hvPos : (0 : ℝ) < v := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hvNat)
      have hvSuccPos : (0 : ℝ) < (v + 1 : ℕ) := by
        positivity
      have hleftScaled := mul_lt_mul_of_pos_left hleftV hvSuccPos
      norm_num [Nat.cast_add, Nat.cast_one] at hleftScaled hscaled
      have hresult :
          1 < s * (goldenSubstStart (v + 1) : ℝ) + w * (v + 1) := by
        nlinarith
      simpa [v] using hresult

/-- Direct evaluation of the substitution starts used to exhibit a concrete witness. -/
theorem goldenSubstStart_one_through_eight :
    (List.range 8).map (fun i => goldenSubstStart (i + 1)) =
      [2, 3, 5, 7, 8, 10, 11, 13] := by
  decide

/-- The substitution-start sequence is strictly discretely concave at index four. -/
theorem goldenSubstStart_strict_concave_at_four :
    goldenSubstStart 3 + goldenSubstStart 5 < 2 * goldenSubstStart 4 := by
  decide

/-- At criterion index `3`, the affine criterion is exactly twice criterion `0` plus criterion
`1`. This elementary identity, rather than concavity, explains the index-`3` corollaries below. -/
theorem criterion_three_eq_two_smul_zero_add_one (s w : ℝ) :
    s * (goldenSubstStart 4 : ℝ) + w * 4 =
      2 * (s * (goldenSubstStart 1 : ℝ) + w * 1) +
        (s * (goldenSubstStart 2 : ℝ) + w * 2) := by
  have hone : goldenSubstStart 1 = 2 := by decide
  have htwo : goldenSubstStart 2 = 3 := by decide
  have hfour : goldenSubstStart 4 = 7 := by decide
  rw [hone, htwo, hfour]
  ring

/-- In any finite block, criterion index `3` may be omitted: when it occurs in the block,
criteria `0` and `1` imply it by an elementary linear combination. This is specific to index `3`
and does not show that concavity is required. -/
theorem finite_constraint_block_of_omitting_four
    {s w : ℝ} {N : ℕ}
    (homit : ∀ k ≤ N, k ≠ 3 →
      1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1)) :
    ∀ k ≤ N, 1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1) := by
  intro k hk
  by_cases hcenter : k = 3
  · subst k
    have hzero := homit 0 (by omega) (by omega)
    have hone := homit 1 (by omega) (by omega)
    norm_num at hzero hone ⊢
    rw [criterion_three_eq_two_smul_zero_add_one]
    linarith
  · exact homit k hk hcenter

/-- In a finite block reaching criterion index `1`, criteria `0` and `1` imply the omitted
actual-index-`4` constraint by an elementary linear combination. This index-specific fact is not
evidence that concavity is required. -/
theorem omitted_four_constraint_follows_from_finite_block
    {s w : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (homit : ∀ k ≤ N, k ≠ 3 →
      1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1)) :
    1 < s * (goldenSubstStart 4 : ℝ) + w * 4 := by
  have hzero := homit 0 (by omega) (by omega)
  have hone := homit 1 (by omega) (by omega)
  norm_num at hzero hone
  rw [criterion_three_eq_two_smul_zero_add_one]
  linarith

end GoldenDisplacementRedundantConstraint
