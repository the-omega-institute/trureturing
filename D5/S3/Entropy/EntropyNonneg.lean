/- GID: D5/S3/Entropy/EntropyNonneg
   generality: G
   mirror-B: D5/B/S3/Entropy/EntropyNonneg
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite entropy lower bounds, completing the bracket [0, log card]. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `shannonEntropy`, `shannon_entropy`,
     `finiteEntropy`, `entropy_nonneg`, `entropy.*nonneg`, `nonneg.*entropy`,
     and `negMulLog_nonneg`, including reversed inequality forms.
   * Pinned mathlib provides the scalar theorem `Real.negMulLog_nonneg` and nonnegativity
     for binary, q-ary, and dynamical entropy, but no finite Shannon-sum nonnegativity theorem.
   * Repository-wide `D5/` grep covered the Shannon- and conditional-entropy names,
     `entropy_nonneg`, nonnegative/nonnegativity wording, inequalities in both orientations,
     and uses of `Real.negMulLog_nonneg`. No duplicate or rearranged equivalent was found.
   * The proofs below therefore reuse the repository's `shannonEntropy`, `conditionalEntropy`,
     `marginal`, and `conditional`, plus mathlib's scalar `Real.negMulLog_nonneg`.
     Units are nats because `shannonEntropy` uses the natural logarithm through
     `Real.negMulLog`.
   * Program significance: the Entropy bucket already proves `H ≤ log card` but had no lower
     bound, so it did not rule out negative entropy for a probability distribution. This result
     brackets finite Shannon entropy in `[0, log card]` and supplies the matching conditional
     lower bound.
-/

import D5.S3.Entropy.ConditionalEntropy

namespace D5.S3.Entropy.EntropyNonneg

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy

/-- Finite Shannon entropy of a probability distribution is nonnegative. -/
theorem shannon_entropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) : 0 ≤ shannonEntropy p := by
  classical
  rw [shannonEntropy]
  exact Finset.sum_nonneg fun i _ =>
    Real.negMulLog_nonneg (hp.1 i) (by
      calc
        p i ≤ ∑ j, p j :=
          Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
        _ = 1 := hp.2)

/-- Finite conditional entropy with nonnegative joint weights is nonnegative. -/
theorem conditional_entropy_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) : 0 ≤ conditionalEntropy p := by
  classical
  rw [conditionalEntropy]
  exact Finset.sum_nonneg fun i _ => by
    have hmarginal_nonneg : 0 ≤ marginal p i := by
      rw [marginal]
      exact Finset.sum_nonneg fun j _ => hp (i, j)
    by_cases hmarginal : marginal p i = 0
    · simp [hmarginal]
    · apply mul_nonneg hmarginal_nonneg
      apply shannon_entropy_nonneg
      constructor
      · intro j
        exact div_nonneg (hp (i, j)) hmarginal_nonneg
      · simp only [conditional]
        rw [← Finset.sum_div, ← marginal]
        exact div_self hmarginal

end D5.S3.Entropy.EntropyNonneg
