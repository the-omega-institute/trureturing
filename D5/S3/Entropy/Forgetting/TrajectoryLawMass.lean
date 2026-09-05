/- GID: D5/S3/Entropy/Forgetting/TrajectoryLawMass
   generality: I
   mirror-B: D5/B/S3/Entropy/Forgetting/TrajectoryLawMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic trajectory laws conserve total mass and preserve nonnegativity. -/

import D5.S3.Entropy.Forgetting.TrajectoryEntropyTelescoping

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Entropy.Forgetting.TrajectoryLawMass

open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.TrajectoryEntropyTelescoping

open scoped Classical in
/-- The total mass of a deterministic trajectory law is the total mass of the initial
weighting, at every time.  Beyond `[Fintype Y]`, which the finite sums need, there
is no hypothesis: neither nonnegativity nor normalisation of `initial` is used,
nothing is assumed about `update`, and the equality holds for an arbitrary real
weighting.  The step is `Finset.sum_fiberwise` from mathlib, restated in the
indicator-weighted form `pushforward` is written in. -/
theorem trajectoryLaw_sum_eq {Y : Type*} [Fintype Y] (update : Y -> Y)
    (initial : Y -> Real) :
    ∀ k, (∑ y, trajectoryLaw update initial k y) = ∑ y, initial y := by
  classical
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have step : (∑ y, trajectoryLaw update initial (k + 1) y)
          = ∑ y, trajectoryLaw update initial k y := by
        simp only [trajectoryLaw, pushforward]
        simpa [Finset.sum_filter] using
          Finset.sum_fiberwise (Finset.univ : Finset Y) update
            (trajectoryLaw update initial k)
      exact step.trans ih

open scoped Classical in
/-- A deterministic trajectory law is pointwise nonnegative whenever the initial
weighting is.  Beyond `[Fintype Y]`, pointwise nonnegativity of `initial` is the
only hypothesis: no normalisation is needed, and nothing is assumed about
`update`. -/
theorem trajectoryLaw_nonneg {Y : Type*} [Fintype Y] (update : Y -> Y)
    (initial : Y -> Real) (hinitial : ∀ y, 0 ≤ initial y) :
    ∀ k y, 0 ≤ trajectoryLaw update initial k y := by
  classical
  intro k
  induction k with
  | zero => exact hinitial
  | succ k ih =>
      intro y
      simp only [trajectoryLaw, pushforward]
      exact Finset.sum_nonneg fun x _ => by
        by_cases h : update x = y <;> simp [h, ih x]

end D5.S3.Entropy.Forgetting.TrajectoryLawMass
