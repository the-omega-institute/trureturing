/- GID: D5/S3/Observer/Residuals/InfiniteCompletionDefect
   generality: G
   mirror-B: D5/B/S3/Observer/Residuals/InfiniteCompletionDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive weighted defect series vanishes exactly when every finite defect vanishes. -/

import Mathlib.Analysis.SpecificLimits.Basic

/- Library-search audit trail (2026-08-29):
   * Repository name and body-shape searches found no existing construction
     summing normalized nonnegative defects with inverse powers of two.
   * Pinned Mathlib exact component hits `summable_geometric_of_lt_one`,
     `Summable.of_nonneg_of_le`, and `Summable.sum_le_tsum` provide convergence
     and isolate each nonnegative summand; no packaged theorem states the
     constructed completion-defect equivalence. -/

namespace D5.S3.Observer.Residuals.InfiniteCompletionDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The infinite completion defect constructed from the finite nonnegative
defects by normalized inverse-binary weighting. -/
noncomputable def infiniteCompletionDefect {State : Type*}
    (defect : State -> Nat -> Real) (state : State) : Real :=
  ∑' n : Nat, (1 / 2 : Real) ^ (n + 1) *
    (defect state n / (1 + defect state n))

/-- The constructed infinite defect vanishes exactly when every finite-layer
defect vanishes. -/
theorem infinite_completion_defect_eq_zero_iff
    {State : Type*} (defect : State -> Nat -> Real) (state : State)
    (hdefect : forall n : Nat, 0 <= defect state n) :
    infiniteCompletionDefect defect state = 0 <->
      forall n : Nat, defect state n = 0 := by
  have hhalf_nonneg : (0 : Real) <= 1 / 2 := by norm_num
  have hhalf_lt_one : (1 / 2 : Real) < 1 := by norm_num
  have hmajorant : Summable (fun n : Nat => (1 / 2 : Real) ^ (n + 1)) := by
    simpa only [pow_succ', Nat.succ_eq_add_one] using
      (summable_geometric_of_lt_one hhalf_nonneg hhalf_lt_one).mul_left
        (1 / 2 : Real)
  have hterm_nonneg : forall n : Nat, 0 <=
      (1 / 2 : Real) ^ (n + 1) *
        (defect state n / (1 + defect state n)) := by
    intro n
    exact mul_nonneg (pow_nonneg hhalf_nonneg _) <|
      div_nonneg (hdefect n) (by linarith [hdefect n])
  have hsum : Summable (fun n : Nat =>
      (1 / 2 : Real) ^ (n + 1) *
        (defect state n / (1 + defect state n))) := by
    apply Summable.of_nonneg_of_le hterm_nonneg _ hmajorant
    intro n
    apply mul_le_of_le_one_right (by positivity)
    exact (div_le_one (by linarith [hdefect n])).2 (by linarith [hdefect n])
  constructor
  · intro hzero n
    have hterm_zero : (1 / 2 : Real) ^ (n + 1) *
        (defect state n / (1 + defect state n)) = 0 := by
      apply le_antisymm
      · have hsingle := hsum.sum_le_tsum {n} (by
          intro i _
          exact hterm_nonneg i)
        have hsingle' : (1 / 2 : Real) ^ (n + 1) *
            (defect state n / (1 + defect state n)) <=
              infiniteCompletionDefect defect state := by
          simpa [infiniteCompletionDefect] using hsingle
        simpa only [hzero] using hsingle'
      · exact hterm_nonneg n
    rcases mul_eq_zero.mp hterm_zero with hweight | hquotient
    · norm_num at hweight
    · exact (div_eq_zero_iff.mp hquotient).resolve_right
        (by linarith [hdefect n])
  · intro hall
    simp [infiniteCompletionDefect, hall]

#print axioms infinite_completion_defect_eq_zero_iff

end D5.S3.Observer.Residuals.InfiniteCompletionDefect
