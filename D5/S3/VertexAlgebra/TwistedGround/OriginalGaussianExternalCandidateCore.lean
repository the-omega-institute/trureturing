/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalCandidateCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rational reflection certificate for the original signed J/T candidate kernel. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums

/-! The algebraic core is kept separate from the analytic square-root factors. -/

noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalCandidateCore

def nPoly (x t s : ℂ) : ℂ :=
  t * s * (t + s) - 2 * (2 - x) * t * s + (1 - x) * (t + s)

def qPoly (x t s : ℂ) : ℂ := nPoly x t s / (2 * (t - s) ^ 2)

/-! The numerator is the cubic-curve numerator from the source reconstruction.

For `lambda = 1 - x`, the source expression
`p*r*(p+r) - 2*(1+lambda)*p*r + lambda*(p+r)`
is exactly `nPoly x p r`.  The diagonal identities below expose its principal
part without silently cancelling any denominator. -/

theorem nPoly_comm (x t s : ℂ) :
    nPoly x t s = nPoly x s t := by
  unfold nPoly
  ring

theorem nPoly_diagonal (x t : ℂ) :
    nPoly x t t = 2 * t * (t - 1) * (t - (1 - x)) := by
  unfold nPoly
  ring

theorem nPoly_sub_diagonal_factor (x t s : ℂ) :
    nPoly x t s - nPoly x s s =
      (t - s) * (s * t + 2 * s ^ 2 - 2 * (2 - x) * s + (1 - x)) := by
  unfold nPoly
  ring

theorem nPoly_first_diagonal (x s : ℂ) :
    s * s + 2 * s ^ 2 - 2 * (2 - x) * s + (1 - x) =
      3 * s ^ 2 - 2 * (2 - x) * s + (1 - x) := by
  ring

theorem nPoly_source_curve (x t s : ℂ) :
    nPoly x t s =
      t * s * (t + s) - 2 * (1 + (1 - x)) * t * s +
        (1 - x) * (t + s) := by
  unfold nPoly
  ring

/-! The two rational charts used by the finite candidate certificate. -/

def rightChart (out : Bool) (u : ℂ) : ℂ := if out then 1 / u else u

def leftChart (out : Bool) (x u : ℂ) : ℂ :=
  if out then (1 - (1 - x) * u) / (1 - u) else ((1 - x) - u) / (1 - u)

/-- The complementary rational kernels differ by the constant half. -/
theorem complementary_kernel_reflection {x t s : ℂ} (h : t ≠ s) :
    qPoly x t s + qPoly (1 - x) (1 - t) (1 - s) = (1 / 2 : ℂ) := by
  unfold qPoly nPoly
  have h' : 1 - t - (1 - s) = s - t := by ring
  rw [h']
  field_simp [h]
  ring_nf

/-! The same rational kernel is unchanged when both local charts are reflected. -/

theorem reflected_positive_positive {x u v : ℂ}
    (hx : x ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : 1 - u ≠ 0) (hv1 : 1 - v ≠ 0)
    (hrs : 1 / u - 1 / v ≠ 0)
    (hls : (1 - (1 - x) * u) / (1 - u) -
      (1 - (1 - x) * v) / (1 - v) ≠ 0) :
    qPoly x (leftChart true x u) (leftChart true x v) =
      qPoly x (rightChart true u) (rightChart true v) := by
  simp only [leftChart, rightChart, ite_true]
  unfold qPoly nPoly
  field_simp [hx, hu, hv, hu1, hv1, hrs, hls]
  ring_nf
  field_simp [hx]
  ring

theorem reflected_negative_negative {x u v : ℂ}
    (hx : x ≠ 0) (hu1 : 1 - u ≠ 0) (hv1 : 1 - v ≠ 0)
    (hrs : u - v ≠ 0)
    (hls : ((1 - x) - u) / (1 - u) - ((1 - x) - v) / (1 - v) ≠ 0) :
    qPoly x (leftChart false x u) (leftChart false x v) =
      qPoly x (rightChart false u) (rightChart false v) := by
  have hD : -(u * v * 2) + u ^ 2 + v ^ 2 ≠ 0 := by
    intro hzero
    apply (pow_ne_zero 2 hrs)
    calc
      (u - v) ^ 2 = -(u * v * 2) + u ^ 2 + v ^ 2 := by ring
      _ = 0 := hzero
  simp only [leftChart, rightChart, Bool.false_eq_true, ite_false]
  unfold qPoly nPoly
  field_simp [hx, hu1, hv1, hrs, hls, hD]
  ring_nf
  have hXDform : -(x ^ 2 * u * v * 2) + x ^ 2 * u ^ 2 + x ^ 2 * v ^ 2 =
      x ^ 2 * (u - v) ^ 2 := by ring
  rw [hXDform]
  field_simp [hx, hrs]
  ring

theorem reflected_positive_negative {x u v : ℂ}
    (hx : x ≠ 0) (hu : u ≠ 0) (hv1 : 1 - v ≠ 0)
    (hrs : 1 / u - v ≠ 0)
    (hls : (1 - (1 - x) * u) / (1 - u) - ((1 - x) - v) / (1 - v) ≠ 0)
    (hu1 : 1 - u ≠ 0) :
    qPoly x (leftChart true x u) (leftChart false x v) =
      qPoly x (rightChart true u) (rightChart false v) := by
  simp only [leftChart, rightChart, ite_true, Bool.false_eq_true, ite_false]
  unfold qPoly nPoly
  field_simp [hx, hu, hv1, hu1, hrs, hls]
  ring_nf
  field_simp [hx]
  ring

theorem reflected_negative_positive {x u v : ℂ}
    (hx : x ≠ 0) (hu1 : 1 - u ≠ 0) (hv : v ≠ 0)
    (hrs : u - 1 / v ≠ 0)
    (hls : ((1 - x) - u) / (1 - u) -
      (1 - (1 - x) * v) / (1 - v) ≠ 0)
    (hv1 : 1 - v ≠ 0) :
    qPoly x (leftChart false x u) (leftChart true x v) =
      qPoly x (rightChart false u) (rightChart true v) := by
  simp only [leftChart, rightChart, Bool.false_eq_true, ite_false, ite_true]
  unfold qPoly nPoly
  field_simp [hx, hu1, hv, hv1, hrs, hls]
  ring_nf
  field_simp [hx]
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalCandidateCore
