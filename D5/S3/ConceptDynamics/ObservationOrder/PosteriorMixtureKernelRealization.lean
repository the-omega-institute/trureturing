/- GID: D5/S3/ConceptDynamics/ObservationOrder/PosteriorMixtureKernelRealization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/PosteriorMixtureKernelRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Bayes-plausible finite posterior mixture is realized by its canonical signal kernel. -/

import D5.S3.ConceptDynamics.ObservationOrder.BayesPlausibility

/-! Library-search audit trail (2026-08-29):
* `rg -n "posterior.*mixture|mixture.*posterior|Bayes|bayes|kernel" D5 -g '*.lean'`
  found the forward theorem `BayesPlausibility.bayes_plausibility`, but no reverse theorem
  constructing the source kernel and verifying all three realization clauses.
* Body-shape searches for the finite joint law and its two coordinate operations found the
  canonical `D5.S3.Divergence.ChainRule.marginal` and `conditional`; both are reused below.
* Pinned Mathlib exact hits `PMF.tsum_coe`, `PMF.apply_ne_top`, and `ENNReal.toReal_sum`
  provide posterior normalization on the finite carrier. The remaining steps are finite-sum
  and field identities for the source's displayed kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.ConceptDynamics.ObservationOrder.PosteriorMixtureKernelRealization

open D5.S3.Divergence.ChainRule

/-- A positive finite prior and a Bayes-plausible weighted posterior family determine the
displayed signal kernel. It is nonnegative and normalized at every world, its induced signal
marginal is the prescribed weight, and conditioning on every positive-weight signal recovers
the prescribed posterior. -/
theorem posterior_mixture_kernel_realization
    {World Signal : Type*} [Fintype World] [Fintype Signal]
    (prior : PMF World) (posterior : Signal → PMF World) (weight : PMF Signal)
    (priorPositive : ∀ world, 0 < (prior world).toReal)
    (mixture : ∀ world,
      ∑ signal, (weight signal).toReal * (posterior signal world).toReal =
        (prior world).toReal) :
    let kernel : World → Signal → Real := fun world signal =>
      (weight signal).toReal * (posterior signal world).toReal /
        (prior world).toReal
    let jointLaw : Signal × World → Real := fun q =>
      (prior q.2).toReal * kernel q.2 q.1
    (∀ world signal, 0 ≤ kernel world signal) ∧
      (∀ world, ∑ signal, kernel world signal = 1) ∧
      marginal jointLaw = (fun signal => (weight signal).toReal) ∧
      ∀ signal, 0 < (weight signal).toReal →
        conditional jointLaw signal =
          fun world => (posterior signal world).toReal := by
  classical
  dsimp only
  have posteriorSum (signal : Signal) :
      ∑ world : World, (posterior signal world).toReal = 1 := by
    have hsum : (∑ world : World, posterior signal world) = 1 := by
      simpa using (posterior signal).tsum_coe
    calc
      (∑ world : World, (posterior signal world).toReal) =
          (∑ world : World, posterior signal world).toReal := by
        symm
        exact ENNReal.toReal_sum
          (fun world _ => PMF.apply_ne_top (posterior signal) world)
      _ = 1 := by rw [hsum]; simp
  have kernelNonnegative (world : World) (signal : Signal) :
      0 ≤ (weight signal).toReal * (posterior signal world).toReal /
        (prior world).toReal := by
    exact div_nonneg
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (priorPositive world).le
  have kernelSum (world : World) :
      ∑ signal : Signal,
          (weight signal).toReal * (posterior signal world).toReal /
            (prior world).toReal = 1 := by
    rw [← Finset.sum_div, mixture world]
    exact div_self (ne_of_gt (priorPositive world))
  have jointFactor (signal : Signal) (world : World) :
      (prior world).toReal *
          ((weight signal).toReal * (posterior signal world).toReal /
            (prior world).toReal) =
        (weight signal).toReal * (posterior signal world).toReal := by
    field_simp [ne_of_gt (priorPositive world)]
  have signalMarginal (signal : Signal) :
      marginal
          (fun q : Signal × World =>
            (prior q.2).toReal *
              ((weight q.1).toReal * (posterior q.1 q.2).toReal /
                (prior q.2).toReal)) signal =
        (weight signal).toReal := by
    rw [marginal]
    calc
      (∑ world : World,
          (prior world).toReal *
            ((weight signal).toReal * (posterior signal world).toReal /
              (prior world).toReal)) =
          ∑ world : World,
            (weight signal).toReal * (posterior signal world).toReal := by
        apply Finset.sum_congr rfl
        intro world _
        exact jointFactor signal world
      _ = (weight signal).toReal *
          ∑ world : World, (posterior signal world).toReal := by
        rw [Finset.mul_sum]
      _ = (weight signal).toReal := by rw [posteriorSum, mul_one]
  have posteriorRecovery (signal : Signal) (signalPositive : 0 < (weight signal).toReal) :
      conditional
          (fun q : Signal × World =>
            (prior q.2).toReal *
              ((weight q.1).toReal * (posterior q.1 q.2).toReal /
                (prior q.2).toReal)) signal =
        fun world => (posterior signal world).toReal := by
    funext world
    rw [conditional, signalMarginal, jointFactor]
    exact mul_div_cancel_left₀ _ (ne_of_gt signalPositive)
  exact ⟨kernelNonnegative, kernelSum, funext signalMarginal, posteriorRecovery⟩

#print axioms posterior_mixture_kernel_realization

end D5.S3.ConceptDynamics.ObservationOrder.PosteriorMixtureKernelRealization
