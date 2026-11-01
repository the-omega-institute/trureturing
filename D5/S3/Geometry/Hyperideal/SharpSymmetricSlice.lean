/- GID: D5/S3/Geometry/Hyperideal/SharpSymmetricSlice
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SharpSymmetricSlice
   mirror-E: none(waiver:sharp-symmetric-slice-identity)
   anchors: []
   utility: none
   digest: Exact sharp symmetric slice identities for the six-length determinant stability bound. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/25065
-/

import D5.S3.Geometry.Hyperideal.SixIndependentLengthStability
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Geometry.Hyperideal.SharpSymmetricSlice

open D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder
open D5.S3.Geometry.Hyperideal.SixIndependentLengthStability

/-! The asymmetric remainder and radius simplify exactly on the slice
    o = r, A = B = h, zeta = 0. -/
theorem sharp_symmetric_slice (r h xi : Real) (hr : 1 < r) (hh : 1 < h) :
    Xi r r h h xi 0 = 2 * (r ^ 2 - 1) * (xi ^ 2) + (xi ^ 2) ^ 2 ∧
      Real.sqrt ((r ^ 2 - 1) ^ 2 + L r r h h * M r r h h) -
          (r ^ 2 - 1) = (r + 1) * (1 + 2 * h - r) := by
  constructor
  · unfold Xi
    ring
  · have hrpos : 0 < r + 1 := by linarith
    have hidentity :
        (r ^ 2 - 1) ^ 2 + L r r h h * M r r h h =
          (2 * h * (r + 1)) ^ 2 := by
      simp [L, M]
      ring
    have hprod : 0 < 2 * h * (r + 1) := by positivity
    rw [hidentity, Real.sqrt_sq_eq_abs, abs_of_pos hprod]
    ring

#print axioms sharp_symmetric_slice

end D5.S3.Geometry.Hyperideal.SharpSymmetricSlice
