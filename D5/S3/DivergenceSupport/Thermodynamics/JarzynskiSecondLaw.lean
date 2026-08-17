/- GID: D5/S3/DivergenceSupport/Thermodynamics/JarzynskiSecondLaw
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/Thermodynamics/JarzynskiSecondLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Jarzynski equality and Jensen convexity imply the mean-work lower bound. -/

/- Library-search audit (2026-08-17):
   * Pinned mathlib supplies `ConvexOn.map_sum_le` and `convexOn_exp`; these exact Jensen
     ingredients are imported and applied below.
   * Loogle returned Jensen-related declarations. LeanSearch's `/api/search` returned 404.
   * No exact theorem packaging the Jarzynski-to-mean-work implication was found locally.
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring

namespace D5.S3.DivergenceSupport.Thermodynamics.JarzynskiSecondLaw

/-- For a finite probability law, the Jarzynski exponential identity implies that free energy
is at most mean work. This is the finite weighted Jensen inequality for the exponential. -/
theorem jarzynski_implies_mean_work_lower_bound
    {ι : Type*} (s : Finset ι) (probability work : ι → ℝ) (beta freeEnergy : ℝ)
    (hprobability_nonneg : ∀ i ∈ s, 0 ≤ probability i)
    (hprobability_total : ∑ i ∈ s, probability i = 1) (hbeta : 0 < beta)
    (hjarzynski :
      ∑ i ∈ s, probability i * Real.exp (-beta * work i) =
        Real.exp (-beta * freeEnergy)) :
    freeEnergy ≤ ∑ i ∈ s, probability i * work i := by
  have hjensen := convexOn_exp.map_sum_le hprobability_nonneg hprobability_total
    (fun i _ => Set.mem_univ (-beta * work i))
  simp only [smul_eq_mul] at hjensen
  have hsum :
      ∑ i ∈ s, probability i * (-beta * work i) =
        -beta * ∑ i ∈ s, probability i * work i := by
    calc
      ∑ i ∈ s, probability i * (-beta * work i) =
          ∑ i ∈ s, -beta * (probability i * work i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = -beta * ∑ i ∈ s, probability i * work i := by rw [Finset.mul_sum]
  have hexp :
      Real.exp (-beta * ∑ i ∈ s, probability i * work i) ≤
        Real.exp (-beta * freeEnergy) := by
    rw [← hsum, ← hjarzynski]
    exact hjensen
  have hscaled :
      beta * freeEnergy ≤ beta * ∑ i ∈ s, probability i * work i := by
    have hneg := neg_le_neg ((Real.exp_le_exp).mp hexp)
    simpa only [neg_mul, neg_neg] using hneg
  exact le_of_mul_le_mul_left hscaled hbeta

#print axioms jarzynski_implies_mean_work_lower_bound

end D5.S3.DivergenceSupport.Thermodynamics.JarzynskiSecondLaw
