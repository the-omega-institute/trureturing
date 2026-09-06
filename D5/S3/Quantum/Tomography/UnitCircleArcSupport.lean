/- GID: D5/S3/Quantum/Tomography/UnitCircleArcSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/UnitCircleArcSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A rational endpoint dual bounds a linear observation of a genuine unit-circle arc while retaining the relation between its real and imaginary coordinates. -/

import D5.S3.Quantum.Tomography.CayleyCoverAnalysis

/- Reuse audit (2026-09-06): CayleyCoverAnalysis owns the compact signed chart
   and root-transport statements. No second Cayley map or interval type is
   introduced here. The added calculation is the circular-cap support bound
   used by the concrete partial-constellation checker. Standard nonnegative
   squares and real polynomial tactics are reused. This is classical convex
   geometry, not a claim of a new general optimization theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.UnitCircleArcSupport

private theorem minor_arc_mem_cap
    (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (hxy : x ^ 2 + y ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 < b) (hy : 0 ≤ y)
    (hwedge : 0 ≤ b * x - a * y) :
    1 + a ≤ (1 + a) * x + b * y := by
  have hx : 0 ≤ x := by
    by_contra hneg
    have hxb : x * b < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hb
    have hay : 0 ≤ a * y := mul_nonneg ha hy
    nlinarith
  have hh : 0 < 1 + a := by linarith
  have ht : 0 ≤ (1 + a) * x + b * y :=
    add_nonneg (mul_nonneg hh.le hx) (mul_nonneg hb.le hy)
  have hid :
      ((1 + a) * x + b * y) ^ 2 - (1 + a) ^ 2 =
        2 * (1 + a) * y * (b * x - a * y) := by
    linear_combination (1 + a) ^ 2 * hxy + y ^ 2 * hab
  have hprod : 0 ≤ 2 * (1 + a) * y * (b * x - a * y) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh.le) hy) hwedge
  nlinarith [sq_nonneg (((1 + a) * x + b * y) - (1 + a))]

/-- In coordinates where the lower endpoint is `(1,0)` and the upper endpoint
is `(a,b)`, the two wedge inequalities specify a short counterclockwise arc.
Every nonnegative rational endpoint dual yields a certified projection bound.

The checker rotates arbitrary complex endpoints to these coordinates. Its
endpoint identity is `g = lambda * e - mu * ((1,0)+(a,b))`. Real and imaginary
coordinates of the observed point remain tied by `x^2+y^2=1`. The alternative
interior-direction bound is ordinary Cauchy--Schwarz, not an extra oracle.
No particular MUB branch or external interval output is assumed here. -/
theorem unit_circle_minor_arc_projection_upper
    (a b x y ex ey gx gy lam mu : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (hxy : x ^ 2 + y ^ 2 = 1)
    (ha : 0 ≤ a) (hb : 0 < b) (hy : 0 ≤ y)
    (hwedge : 0 ≤ b * x - a * y)
    (he : (ex = 1 ∧ ey = 0) ∨ (ex = a ∧ ey = b))
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (hgx : gx = lam * ex - mu * (1 + a))
    (hgy : gy = lam * ey - mu * b) :
    gx * x + gy * y ≤ lam - mu * (1 + a) := by
  have hcap := minor_arc_mem_cap a b x y hab hxy ha hb hy hwedge
  have heunit : ex ^ 2 + ey ^ 2 = 1 := by
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · norm_num
    · exact hab
  have hdot : ex * x + ey * y ≤ 1 := by
    nlinarith [sq_nonneg (x - ex), sq_nonneg (y - ey)]
  have hfirst : 0 ≤ lam * (1 - (ex * x + ey * y)) :=
    mul_nonneg hlam (sub_nonneg.mpr hdot)
  have hsecond : 0 ≤ mu * ((1 + a) * x + b * y - (1 + a)) :=
    mul_nonneg hmu (sub_nonneg.mpr hcap)
  rw [hgx, hgy]
  nlinarith

#print axioms unit_circle_minor_arc_projection_upper

end D5.S3.Quantum.Tomography.UnitCircleArcSupport
