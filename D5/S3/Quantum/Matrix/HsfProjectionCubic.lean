/- GID: D5/S3/Quantum/Matrix/HsfProjectionCubic
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfProjectionCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Dimension-free projection trace SOS and signed involution cubic compatibility. -/

/-
admission_basis: escape-witness
proof_shape: projection_cubic_compatibility: content
escape_witness: projection_certificate; eleven positive rational trace localizers
The exact certificate and all algebraic and positivity helpers are consumed by
the projection derivative bound and the signed involution estimate. The actual
CFC derivatives are supplied by HsfIdentityCubicDerivatives. General contraction
directions and independent denominator centers remain open.
-/

module

public import D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives

@[expose] public section
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.HsfProjectionCubic

variable {n : Type*} [Fintype n] [DecidableEq n]
open HsfQubitMixedCubic

/-- A PSD-weighted trace square; the product inside the trace need not be PSD. -/
def traceLocalizer (A B q : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (A * qᴴ * B * q)).re

private theorem trace_localizer_nonneg {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (q : Matrix n n ℂ) :
    0 ≤ traceLocalizer A B q := by
  let R := CFC.sqrt A
  have hR : Rᴴ = R := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hs : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hp := (hB.conjTranspose_mul_mul_same (q * R)).trace_nonneg
  have he : Matrix.trace ((q * R)ᴴ * B * (q * R)) =
      Matrix.trace (A * qᴴ * B * q) := by
    rw [Matrix.conjTranspose_mul, hR]
    calc
      _ = Matrix.trace (R * (qᴴ * B * q) * R) := by congr 1 <;> noncomm_ring
      _ = Matrix.trace (R * R * (qᴴ * B * q)) :=
        Matrix.trace_mul_cycle R (qᴴ * B * q) R
      _ = _ := by rw [hs]; simp only [Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (he ▸ hp)).1

/-- The eleven rank-one localizers of the exact projection certificate. -/
def projectionSOS (H G P : Matrix n n ℂ) : ℝ :=
  84 * traceLocalizer P H ((1-P)*H - (31/84 : ℝ) • G - (11/84 : ℝ) • (P*G)) +
  (4247/84) * traceLocalizer P H (G + (5707/4247 : ℝ) • (P*G)) +
  (107292/4247) * traceLocalizer P H (P*G) +
  30 * traceLocalizer P G ((1-P)*H - (4/5 : ℝ) • G - (13/30 : ℝ) • (P*G)) +
  (729/5) * traceLocalizer P G (G + (388/729 : ℝ) • (P*G)) +
  (24881/1458) * traceLocalizer P G (P*G) +
  60 * traceLocalizer (1-P) H (P*H - (7/20 : ℝ) • (P*G)) +
  (1053/20) * traceLocalizer (1-P) H (P*G) +
  81 * traceLocalizer (1-P) G (H - (20/81 : ℝ) • (P*H) - (43/81 : ℝ) • (P*G)) +
  (1382/81) * traceLocalizer (1-P) G (P*H - (187/691 : ℝ) • (P*G)) +
  (11003/691) * traceLocalizer (1-P) G (P*G)

private theorem projection_posSemidef {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P*P = P) : P.PosSemidef := by
  simpa only [hP.eq, hPP] using Matrix.posSemidef_conjTranspose_mul_self P

private theorem complement_projection {P : Matrix n n ℂ} (hPP : P*P = P) :
    (1-P)*(1-P) = 1-P := by
  noncomm_ring [hPP]

private theorem projection_sos_nonneg {H G P : Matrix n n ℂ}
    (hH : H.PosSemidef) (hG : G.PosSemidef)
    (hP : P.IsHermitian) (hPP : P*P = P) : 0 ≤ projectionSOS H G P := by
  have hp := projection_posSemidef hP hPP
  have hl := projection_posSemidef (Matrix.isHermitian_one.sub hP)
    (complement_projection hPP)
  have hh (q : Matrix n n ℂ) := trace_localizer_nonneg hp hH q
  have hg (q : Matrix n n ℂ) := trace_localizer_nonneg hp hG q
  have lh (q : Matrix n n ℂ) := trace_localizer_nonneg hl hH q
  have lg (q : Matrix n n ℂ) := trace_localizer_nonneg hl hG q
  unfold projectionSOS
  positivity

end D5.S3.Quantum.Matrix.HsfProjectionCubic
