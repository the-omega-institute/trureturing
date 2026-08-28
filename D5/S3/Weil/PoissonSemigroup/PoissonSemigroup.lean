/- GID: D5/S3/Weil/PoissonSemigroup/PoissonSemigroup
   generality: G
   mirror-B: D5/B/S3/Weil/PoissonSemigroup/PoissonSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A convolution semigroup transports a Poisson-smoothed source profile from sigma to sigma plus eta. -/

import Mathlib

namespace D5.S3.Weil.PoissonSemigroup

open scoped BigOperators

/-!
The source profiles and kernels are real-line functions.  The operation `star` is the
source convolution channel; its associativity, kernel scale law, and representation of
the observed profile are stated as independent model laws.
-/

theorem coarse_poisson_semigroup
    (star : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ))
    (P d : ℝ → (ℝ → ℝ)) (source : ℝ → ℝ)
    (hassoc : ∀ f g h, star f (star g h) = star (star f g) h)
    (hkernel : ∀ σ η, 1 < σ → 0 < η → star (P η) (P σ) = P (σ + η))
    (hprofile : ∀ σ, d σ = star (P σ) source)
    {σ η : ℝ} (hσ : 1 < σ) (hη : 0 < η) :
    d (σ + η) = star (P η) (d σ) := by
  rw [hprofile, hprofile, ← hkernel σ η hσ hη]
  exact (hassoc (P η) (P σ) source).symm

end D5.S3.Weil.PoissonSemigroup
