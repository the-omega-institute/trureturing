/- GID: D5/S3/Entropy/Thermodynamics/JarzynskiSecondLaw
   generality: G
   mirror-B: D5/B/S3/Entropy/Thermodynamics/JarzynskiSecondLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Jensen turns the Jarzynski equality into a mean-work lower bound. -/

/- Library-search audit trail (2026-08-17):
   * The pinned-mathlib search query `weighted Jensen exponential finite sum` returned no
     declaration-name result.
   * Local pinned-mathlib grep found `Real.convexOn_exp` and `ConvexOn.map_sum_le` in
     `Mathlib.Analysis.Convex.Jensen`; the proof below applies that Jensen theorem directly.
   * `Mathlib.Analysis.MeanInequalities` supplies an existing weighted-exponential application
     pattern. LeanSearch and Loogle network endpoints were not tested.
   * Repository-wide `D5/` searches for Jarzynski, average work, free energy, and the weighted
     exponential statement found no equivalent declaration.
-/

import Mathlib.Analysis.MeanInequalities

namespace D5.S3.Entropy.Thermodynamics.JarzynskiSecondLaw

/-- The Jarzynski equality at positive inverse temperature implies the mean-work lower bound. -/
theorem jarzynski_implies_second_law {ι : Type*} [Fintype ι]
    (probability work : ι → ℝ) (beta freeEnergyDifference : ℝ)
    (hprobability : ∀ i, 0 ≤ probability i)
    (hprobability_sum : ∑ i, probability i = 1)
    (hbeta : 0 < beta)
    (hjarzynski :
      ∑ i, probability i * Real.exp (-beta * work i) =
        Real.exp (-beta * freeEnergyDifference)) :
    freeEnergyDifference ≤ ∑ i, probability i * work i := by
  classical
  have hjensen :
      Real.exp (∑ i, probability i • (-beta * work i)) ≤
        ∑ i, probability i • Real.exp (-beta * work i) := by
    exact convexOn_exp.map_sum_le
      (fun i _ => hprobability i)
      (by simpa using hprobability_sum)
      (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  rw [hjarzynski] at hjensen
  have hscaled := Real.exp_le_exp.mp hjensen
  have hweighted :
      (∑ i, probability i * (-beta * work i)) =
        -beta * ∑ i, probability i * work i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hweighted] at hscaled
  nlinarith

end D5.S3.Entropy.Thermodynamics.JarzynskiSecondLaw
