/- GID: D5/S3/Analytic/Curvature/PoissonScaleDipole
   generality: G
   mirror-B: D5/B/S3/Analytic/Curvature/PoissonScaleDipole
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The off-line curvature dipole is the scale derivative of the Poisson kernel. -/

import D5.S3.Analytic.Adelic.OffLineCurvatureDipole
import Mathlib.Tactic

/-!
# Poisson scale dipole

The reflected off-line curvature profile already frozen in
`OffLineCurvatureDipole` is exactly the derivative, in the positive scale
parameter, of the real Poisson kernel.  This identifies the zero-mass dipole
with an infinitesimal change of harmonic resolution rather than introducing a
second curvature formula.

Library-search audit trail (2026-08-30):

* Exact-name and body-shape searches found no frozen owner identifying the
  rational off-line curvature profile with a Poisson-scale derivative.
* `OffLineCurvatureDipole` supplies the source curvature formula and its
  integrability and zero-total-mass clauses.  This module reuses those clauses
  rather than re-proving the improper integral.
* Pinned Mathlib supplies the quotient derivative and the nonvanishing of
  `Real.pi`; the pointwise bridge is proved directly from those facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Curvature.PoissonScaleDipole

open Filter MeasureTheory

private theorem poisson_kernel_scale_derivative
    (delta x : ℝ) (hdelta : 0 < delta) :
    HasDerivAt
      (fun scale : ℝ => scale / (Real.pi * (scale ^ 2 + x ^ 2)))
      ((x ^ 2 - delta ^ 2) /
        (Real.pi * (delta ^ 2 + x ^ 2) ^ 2))
      delta := by
  have hsum : 0 < delta ^ 2 + x ^ 2 := by
    nlinarith [sq_pos_of_pos hdelta, sq_nonneg x]
  have hden : Real.pi * (delta ^ 2 + x ^ 2) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero hsum.ne'
  have hnum : HasDerivAt (fun scale : ℝ => scale) 1 delta :=
    hasDerivAt_id delta
  have hinner :
      HasDerivAt (fun scale : ℝ => scale ^ 2 + x ^ 2)
        (2 * delta) delta := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one] using
      ((hasDerivAt_id delta).pow 2).add_const (x ^ 2)
  have hdenDerivative :
      HasDerivAt
        (fun scale : ℝ => Real.pi * (scale ^ 2 + x ^ 2))
        (Real.pi * (2 * delta)) delta := by
    exact hinner.const_mul Real.pi
  have hraw := hnum.div hdenDerivative hden
  refine hraw.congr_deriv ?_
  field_simp [Real.pi_ne_zero, hsum.ne']
  ring

/--
The curvature of a reflected off-line pair is twice pi times the scale
 derivative of the Poisson kernel.  The same constructed dipole is integrable
and has zero total mass, so the bridge preserves the meaningful global clause
of the source theorem.
-/
theorem poisson_scale_dipole (delta gamma : ℝ) (hdelta : 0 < delta) :
    let poissonKernel := fun scale x : ℝ =>
      scale / (Real.pi * (scale ^ 2 + x ^ 2))
    let curvatureDipole := fun t : ℝ =>
      2 * (((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2)
    (∀ t, curvatureDipole t =
      2 * Real.pi *
        deriv (fun scale => poissonKernel scale (t - gamma)) delta) ∧
      Integrable curvatureDipole ∧
      (∫ t : ℝ, curvatureDipole t) = 0 := by
  dsimp only
  constructor
  · intro t
    have hsum : 0 < delta ^ 2 + (t - gamma) ^ 2 := by
      nlinarith [sq_pos_of_pos hdelta, sq_nonneg (t - gamma)]
    rw [(poisson_kernel_scale_derivative
      delta (t - gamma) hdelta).deriv]
    field_simp [Real.pi_ne_zero, hsum.ne']
    ring
  · have hsource :=
      D5.S3.Analytic.Adelic.OffLineCurvatureDipole.off_line_curvature_dipole
        delta gamma hdelta
    dsimp only at hsource
    rcases hsource with
      ⟨hformula, _, _, hintegrable, hmass, _, _⟩
    constructor
    · exact hintegrable.congr (ae_of_all _ fun t => hformula t)
    · calc
        (∫ t : ℝ, 2 * (((t - gamma) ^ 2 - delta ^ 2) /
          ((t - gamma) ^ 2 + delta ^ 2) ^ 2)) =
            ∫ t : ℝ, deriv
              (deriv (fun u : ℝ =>
                Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
                  Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2)) 0 := by
              apply integral_congr_ae
              exact ae_of_all _ fun t => (hformula t).symm
        _ = 0 := hmass

#print axioms poisson_scale_dipole

end D5.S3.Analytic.Curvature.PoissonScaleDipole
