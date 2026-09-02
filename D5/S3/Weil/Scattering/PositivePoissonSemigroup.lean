/- GID: D5/S3/Weil/Scattering/PositivePoissonSemigroup
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/PositivePoissonSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive completion depths form a source-free Poisson smoothing semigroup. -/

import D5.S3.Weil.Scattering.PoissonSemigroup

/-!
# Positive Poisson semigroup

The real-line kernel family, completion profiles, boundary source, and
convolution channel are the source objects.  Their independent associativity,
kernel semigroup, and profile-representation laws construct the propagation
at every positive depth.  The frozen coarse theorem is reused after a positive
rescaling of its depth coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Scattering.PositivePoissonSemigroup

open D5.S3.Weil.Scattering.PoissonSemigroup

/-- Under the positive-scale Poisson kernel law, every deeper completion
profile is obtained by applying only the additional Poisson smoothing to the
shallower profile. -/
theorem positive_poisson_semigroup
    (star : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ))
    (P completion : ℝ → (ℝ → ℝ)) (source : ℝ → ℝ)
    (starAssociative : ∀ f g k, star f (star g k) = star (star f g) k)
    (kernelSemigroup : ∀ x h, 0 < x → 0 < h →
      star (P h) (P x) = P (x + h))
    (completionRepresentation : ∀ x, completion x = star (P x) source)
    {x h : ℝ} (xPositive : 0 < x) (hPositive : 0 < h) :
    completion (x + h) = star (P h) (completion x) := by
  let scale : ℝ := x / 2
  have scalePositive : 0 < scale := by
    dsimp [scale]
    positivity
  have rescaledKernelSemigroup :
      ∀ sigma eta, 1 < sigma → 0 < eta →
        star (P (scale * eta)) (P (scale * sigma)) =
          P (scale * (sigma + eta)) := by
    intro sigma eta sigmaLower etaPositive
    rw [kernelSemigroup (scale * sigma) (scale * eta)
      (mul_pos scalePositive (lt_trans (by norm_num) sigmaLower))
      (mul_pos scalePositive etaPositive)]
    congr 1
    ring
  have transported := coarse_poisson_semigroup
    star (fun sigma => P (scale * sigma))
    (fun sigma => completion (scale * sigma)) source
    starAssociative rescaledKernelSemigroup
    (fun sigma => completionRepresentation (scale * sigma))
    (σ := 2) (η := 2 * h / x) (by norm_num) (by positivity)
  convert transported using 1 <;> dsimp [scale] <;> field_simp

#print axioms positive_poisson_semigroup

end D5.S3.Weil.Scattering.PositivePoissonSemigroup
