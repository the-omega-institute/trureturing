/- GID: D5/S3/Weil/Pick/HardyPolarizedCriterion
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/HardyPolarizedCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite Hardy Hankel block vanishes exactly when its negative-frequency coefficients vanish. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.HardyPolarizedCriterion

/-! The finite Hankel block records the negative-frequency tail of a Laurent
symbol. The offset by one separates this tail from the analytic (nonnegative)
part. -/

def hardyHankelBlock {n : ℕ} (coeff : ℕ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => coeff (i.val + j.val + 1)

theorem hardy_polarized_criterion
    {n : ℕ} (coeff : ℕ → ℂ) :
    hardyHankelBlock (n := n) coeff = 0 ↔
      ∀ i j : Fin n, coeff (i.val + j.val + 1) = 0 := by
  constructor
  · intro h i j
    have hentry := congrFun (congrFun h i) j
    simpa [hardyHankelBlock] using hentry
  · intro h
    ext i j
    simp [hardyHankelBlock, h i j]

theorem hardy_nonzero_of_negative_coefficient
    {n : ℕ} (coeff : ℕ → ℂ) (i j : Fin n)
    (hcoeff : coeff (i.val + j.val + 1) ≠ 0) :
    hardyHankelBlock (n := n) coeff ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero i) j
  apply hcoeff
  simpa [hardyHankelBlock] using hentry

#print axioms hardy_polarized_criterion
#print axioms hardy_nonzero_of_negative_coefficient

end D5.S3.Weil.Pick.HardyPolarizedCriterion
