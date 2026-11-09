/- GID: D5/S0/Asymptotics/GeometricScaleRigidity
   generality: G
   mirror-B: D5/B/S0/Asymptotics/GeometricScaleRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A continuous profile constant on a shrinking geometric orbit takes its value at zero. -/

import Mathlib.Analysis.SpecificLimits.Normed

/-! Geometric shrinking-orbit rigidity for continuous real profiles. -/

namespace D5.S0.Asymptotics.GeometricScaleRigidity

open Filter

/-!
proof_shape: content.
admission_basis: escape-witness.
escape_witness: the live limit-chain construction composes the geometric power
limit with continuity at zero and transports the orbit equality to a second
limit at h M; uniqueness then produces the conclusion. This chain is not a
projection, normalization, or direct instantiation of a frozen repository
declaration.
-/
/-- Constancy along a geometric orbit forces a continuous profile to agree with
its value at the limiting point.  This is the scaling-limit step used in the
Continuation XII contradiction. -/
theorem geometric_scale_rigidity
    {h : ℝ → ℝ} {rho M : ℝ}
    (hcont : ContinuousAt h 0)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hscale : ∀ n : ℕ, h (rho ^ n * M) = h M) :
    h M = h 0 := by
  have hpow : Tendsto (fun n : ℕ => rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1
  have hscaled : Tendsto (fun n : ℕ => rho ^ n * M) atTop (nhds 0) := by
    simpa using hpow.mul_const M
  have hlimit_zero : Tendsto (fun n : ℕ => h (rho ^ n * M)) atTop (nhds (h 0)) :=
    hcont.tendsto.comp hscaled
  have hlimit_M : Tendsto (fun n : ℕ => h (rho ^ n * M)) atTop (nhds (h M)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => h M) atTop (nhds (h M))) using 1
    funext n
    exact hscale n
  exact tendsto_nhds_unique hlimit_M hlimit_zero

#print axioms geometric_scale_rigidity

end D5.S0.Asymptotics.GeometricScaleRigidity
