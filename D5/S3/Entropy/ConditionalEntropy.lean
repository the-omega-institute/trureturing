/- GID: D5/S3/Entropy/ConditionalEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/ConditionalEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite conditional entropy in nats and prove the entropy chain rule. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `conditionalEntropy`, `conditional_entropy`,
     `condEntropy`, `entropy.*conditional`, `conditional.*entropy`,
     `entropy.*chain`, `chain.*entropy`, `shannonEntropy`, `finiteEntropy`,
     `negMulLog_mul`, `Fintype.sum_prod_type`, and `Real.log_mul`.
   * Pinned mathlib's information theory is measure-valued: its finite-information files provide
     KL divergence and KL chain rules, while `Real.negMulLog_mul` provides the scalar product
     identity. No finite conditional-entropy definition, entropy chain rule, or bridge to the
     repository's real-valued finite sums was found.
   * Repository-wide `D5/` grep covered conditional-entropy names in both orders, entropy chain-rule
     names in both orders, `shannonEntropy` adjacent to `marginal`, and `negMulLog` adjacent to
     `conditional`. No duplicate or rearranged equivalent was found.
   * The definition and theorem below therefore reuse the repository's `marginal`, `conditional`,
     and `shannonEntropy`. Units are nats because `shannonEntropy` uses `Real.log` through
     `Real.negMulLog`.
-/

import D5.S3.Divergence.ChainRule
import D5.S3.Entropy.MaxEntropy

namespace D5.S3.Entropy.ConditionalEntropy

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy

/-- Finite conditional entropy in nats, weighted by the first-coordinate marginal. -/
noncomputable def conditionalEntropy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) : ℝ :=
  ∑ i, marginal p i * shannonEntropy (conditional p i)

/-- Finite Shannon entropy satisfies the chain rule under first-coordinate conditioning. -/
theorem entropy_chain_rule {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) :
    shannonEntropy p = shannonEntropy (marginal p) + conditionalEntropy p := by
  classical
  have hslice (i : ι) :
      (∑ j, Real.negMulLog (p (i, j))) =
        Real.negMulLog (marginal p i) +
          marginal p i * shannonEntropy (conditional p i) := by
    by_cases hmi : marginal p i = 0
    · have hcell (j : κ) : p (i, j) = 0 := by
        apply le_antisymm
        · calc
            p (i, j) ≤ marginal p i := by
              rw [marginal]
              exact Finset.single_le_sum
                (fun j' _ => hp (i, j')) (Finset.mem_univ j)
            _ = 0 := hmi
        · exact hp (i, j)
      simp [hcell, hmi]
    · have hfactor (j : κ) :
          marginal p i * conditional p i j = p (i, j) := by
        simp only [conditional]
        field_simp [hmi]
      have hconditional_sum : ∑ j, conditional p i j = 1 := by
        simp only [conditional]
        rw [← Finset.sum_div, ← marginal]
        exact div_self hmi
      have hterm (j : κ) :
          Real.negMulLog (p (i, j)) =
            conditional p i j * Real.negMulLog (marginal p i) +
              marginal p i * Real.negMulLog (conditional p i j) := by
        by_cases hpij : p (i, j) = 0
        · simp [hpij, conditional]
        · calc
            Real.negMulLog (p (i, j)) =
                Real.negMulLog (marginal p i * conditional p i j) := by
                  rw [hfactor]
            _ = conditional p i j * Real.negMulLog (marginal p i) +
                  marginal p i * Real.negMulLog (conditional p i j) :=
                Real.negMulLog_mul _ _
      rw [shannonEntropy]
      calc
        (∑ j, Real.negMulLog (p (i, j))) =
            ∑ j, (conditional p i j * Real.negMulLog (marginal p i) +
              marginal p i * Real.negMulLog (conditional p i j)) := by
                exact Finset.sum_congr rfl fun j _ => hterm j
        _ = (∑ j, conditional p i j) * Real.negMulLog (marginal p i) +
              marginal p i * ∑ j, Real.negMulLog (conditional p i j) := by
                rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        _ = Real.negMulLog (marginal p i) +
              marginal p i * ∑ j, Real.negMulLog (conditional p i j) := by
                rw [hconditional_sum, one_mul]
  calc
    shannonEntropy p = ∑ i, ∑ j, Real.negMulLog (p (i, j)) := by
      rw [shannonEntropy, Fintype.sum_prod_type]
    _ = ∑ i, (Real.negMulLog (marginal p i) +
          marginal p i * shannonEntropy (conditional p i)) := by
      exact Finset.sum_congr rfl fun i _ => hslice i
    _ = (∑ i, Real.negMulLog (marginal p i)) +
          ∑ i, marginal p i * shannonEntropy (conditional p i) := by
      rw [Finset.sum_add_distrib]
    _ = shannonEntropy (marginal p) + conditionalEntropy p := by
      rfl

end D5.S3.Entropy.ConditionalEntropy
