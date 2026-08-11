/- GID: D5/S3/Entropy/Feedback/DemonIdentity
   generality: I
   mirror-B: D5/B/S3/Entropy/Feedback/DemonIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The average posterior-to-reference divergence of a finite joint law decomposes as its mutual information plus the divergence of the input marginal from the reference: klDivergence P (u times the output marginal) = mutualInformation P + klDivergence (marginal P) u, for a nonnegative joint law P and a positive reference u. -/

import D5.S3.Entropy.MutualInformation
import Mathlib

namespace D5.S3.Entropy.Feedback.DemonIdentity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation

/-- The feedback (demon) identity for a finite joint law `P : ι × κ → ℝ` with positive reference
`u : ι → ℝ`. Writing `mY y = ∑ x, P (x, y)` for the output marginal, the average posterior-to-reference
divergence `∑_y mY y · D(p̂_y‖u)` — assembled here in joint form as
`klDivergence P (fun q => u q.1 * mY q.2)` — equals the mutual information of `P` plus the divergence of
the input marginal `marginal P` from `u`:
`klDivergence P (u ⊗ mY) = mutualInformation P + klDivergence (marginal P) u`.
On the support `P q > 0` all three of `u q.1`, `marginal P q.1`, `mY q.2` are positive, so the pointwise
logarithm splits; off the support the `P q` weight kills the term. Summing the `κ`-fibre collapses the
input-marginal weight `∑_y P (x, y) = marginal P x`. -/
theorem demon_average_divergence_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] (P : ι × κ → ℝ) (u : ι → ℝ)
    (hP : ∀ q, 0 ≤ P q) (hu : ∀ x, 0 < u x) :
    klDivergence P (fun q => u q.1 * marginal (fun r : κ × ι => P (r.2, r.1)) q.2)
      = mutualInformation P + klDivergence (marginal P) u := by
  classical
  rw [mutualInformation]
  simp only [klDivergence]
  have key : ∀ q : ι × κ,
      P q * Real.log (P q / (u q.1 * marginal (fun r : κ × ι => P (r.2, r.1)) q.2))
        = P q * Real.log (P q / (marginal P q.1 * marginal (fun r : κ × ι => P (r.2, r.1)) q.2))
          + P q * Real.log (marginal P q.1 / u q.1) := by
    intro q
    rcases eq_or_lt_of_le (hP q) with h0 | hpos
    · simp [← h0]
    · have hmXpos : 0 < marginal P q.1 := by
        simp only [marginal]
        exact Finset.sum_pos' (fun j _ => hP _) ⟨q.2, Finset.mem_univ _, hpos⟩
      have hmYpos : 0 < marginal (fun r : κ × ι => P (r.2, r.1)) q.2 := by
        simp only [marginal]
        refine Finset.sum_pos' (fun j _ => hP _) ⟨q.1, Finset.mem_univ _, ?_⟩
        simpa using hpos
      have hux : 0 < u q.1 := hu q.1
      rw [Real.log_div (ne_of_gt hpos) (mul_ne_zero (ne_of_gt hux) (ne_of_gt hmYpos)),
          Real.log_div (ne_of_gt hpos) (mul_ne_zero (ne_of_gt hmXpos) (ne_of_gt hmYpos)),
          Real.log_mul (ne_of_gt hux) (ne_of_gt hmYpos),
          Real.log_mul (ne_of_gt hmXpos) (ne_of_gt hmYpos),
          Real.log_div (ne_of_gt hmXpos) (ne_of_gt hux)]
      ring
  rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [marginal]
  rw [Finset.sum_mul]

end D5.S3.Entropy.Feedback.DemonIdentity
