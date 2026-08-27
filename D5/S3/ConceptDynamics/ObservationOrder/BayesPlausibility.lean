/- GID: D5/S3/ConceptDynamics/ObservationOrder/BayesPlausibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/BayesPlausibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite posterior mixtures reconstruct their prior distribution. -/

import D5.S3.Divergence.ChainRule

/- Library-search audit trail (2026-08-27):
   * Repository searches for Bayes plausibility, posterior mixtures, and a
     prior reconstructed from signal conditionals found no exact theorem.
   * The related repository primitives `D5.S3.Divergence.ChainRule.marginal`
     and `conditional` are the canonical real-valued marginal and conditional
     constructions and are imported rather than redeclared.
   * The related Mathlib theorem `ProbabilityTheory.sum_meas_smul_cond_fiber`
     concerns conditional measures, but does not state this finite PMF/kernel
     reconstruction on the source carrier.
   * Exact pinned Mathlib hits `PMF.tsum_coe`, `PMF.apply_ne_top`,
     `ENNReal.toReal_sum`, and `Finset.sum_eq_zero_iff_of_nonneg` supply the
     finite normalization and zero-marginal steps and are applied below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.ConceptDynamics.ObservationOrder.BayesPlausibility

open D5.S3.Divergence.ChainRule

/-- For the joint law constructed from a finite prior and signal kernel, the
signal-weighted posterior mixture is the prior, both as a function and at each
world. -/
theorem bayes_plausibility
    {World Signal : Type*} [Fintype World] [Fintype Signal]
    (prior : PMF World) (kernel : World -> PMF Signal) :
    let jointLaw : Signal × World -> Real := fun q =>
      (prior q.2).toReal * (kernel q.2 q.1).toReal
    let signalWeight : Signal -> Real := marginal jointLaw
    let posterior : Signal -> World -> Real := conditional jointLaw
    ((fun world =>
        ∑ signal, signalWeight signal * posterior signal world) =
      fun world => (prior world).toReal) ∧
      ∀ world,
        ∑ signal, signalWeight signal * posterior signal world =
          (prior world).toReal := by
  classical
  dsimp only
  have kernelSum (world : World) :
      ∑ signal : Signal, (kernel world signal).toReal = 1 := by
    have hsum : (∑ signal : Signal, kernel world signal) = 1 := by
      simpa using (kernel world).tsum_coe
    calc
      (∑ signal : Signal, (kernel world signal).toReal) =
          (∑ signal : Signal, kernel world signal).toReal := by
        symm
        exact ENNReal.toReal_sum
          (fun signal _ => PMF.apply_ne_top (kernel world) signal)
      _ = 1 := by rw [hsum]; simp
  have jointNonneg (signal : Signal) (world : World) :
      0 ≤ (prior world).toReal * (kernel world signal).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have jointFactor (signal : Signal) (world : World) :
      marginal
          (fun q : Signal × World =>
            (prior q.2).toReal * (kernel q.2 q.1).toReal) signal *
        conditional
          (fun q : Signal × World =>
            (prior q.2).toReal * (kernel q.2 q.1).toReal) signal world =
      (prior world).toReal * (kernel world signal).toReal := by
    by_cases hweight :
        marginal
          (fun q : Signal × World =>
            (prior q.2).toReal * (kernel q.2 q.1).toReal) signal = 0
    · have hjoint :
          (prior world).toReal * (kernel world signal).toReal = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun otherWorld _ => jointNonneg signal otherWorld)).mp
          (by simpa only [marginal] using hweight)
        exact Finset.mem_univ world
      simp [conditional, hweight, hjoint]
    · simp only [conditional]
      field_simp [hweight]
  have pointwise (world : World) :
      ∑ signal,
          marginal
              (fun q : Signal × World =>
                (prior q.2).toReal * (kernel q.2 q.1).toReal) signal *
            conditional
              (fun q : Signal × World =>
                (prior q.2).toReal * (kernel q.2 q.1).toReal) signal world =
        (prior world).toReal := by
    calc
      _ = ∑ signal : Signal,
          (prior world).toReal * (kernel world signal).toReal := by
        apply Finset.sum_congr rfl
        intro signal _
        exact jointFactor signal world
      _ = (prior world).toReal *
          ∑ signal : Signal, (kernel world signal).toReal := by
        rw [Finset.mul_sum]
      _ = (prior world).toReal := by rw [kernelSum, mul_one]
  exact ⟨funext pointwise, pointwise⟩

#print axioms bayes_plausibility

end D5.S3.ConceptDynamics.ObservationOrder.BayesPlausibility
