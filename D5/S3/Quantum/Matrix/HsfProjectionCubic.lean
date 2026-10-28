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

/-! Projection-direction compatibility at the identity denominator, in every finite dimension. -/

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

set_option maxHeartbeats 1000000 in
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
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 84) (hh _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4247/84) (hh _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 107292/4247) (hh _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 30) (hg _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 729/5) (hg _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 24881/1458) (hg _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 60) (lh _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1053/20) (lh _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (lg _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1382/81) (lg _)
  · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 11003/691) (lg _)



section Words
variable (H G P : Matrix n n ℂ) (hH : H.IsHermitian) (hG : G.IsHermitian)
  (hP : P.IsHermitian) (hPP : P*P = P)

private theorem projection_mul_assoc (P M : Matrix n n ℂ) (hPP : P*P = P) :
    P*(P*M) = P*M := by rw [← Matrix.mul_assoc, hPP]

include hH hG hP hPP in
private theorem w_hgh : (Matrix.trace (H*(G*(H)))).re = (Matrix.trace (G*(H*(H)))).re := by
  calc
    (Matrix.trace (H*(G*(H)))).re = (Matrix.trace (G*(H*(H)))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H) (G*(H))))

include hH hG hP hPP in
private theorem w_hhg : (Matrix.trace (H*(H*(G)))).re = (Matrix.trace (G*(H*(H)))).re := by
  calc
    (Matrix.trace (H*(H*(G)))).re = (Matrix.trace (G*(H*(H)))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H)) (G)))

include hH hG hP hPP in
private theorem w_gpgh : (Matrix.trace (G*(P*(G*(H))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
  calc
    (Matrix.trace (G*(P*(G*(H))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (G*(P)) (G*(H))))

include hH hG hP hPP in
private theorem w_hggp : (Matrix.trace (H*(G*(G*(P))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(G*(G*(P))))).re = (Matrix.trace (P*(H*(G*(G))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G*(G))) (P)))
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(G*(G))))ᴴ = G*(G*(H*(P))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hghp : (Matrix.trace (H*(G*(H*(P))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (H*(G*(H*(P))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H) (G*(H*(P)))))

include hH hG hP hPP in
private theorem w_hgpg : (Matrix.trace (H*(G*(P*(G))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
  calc
    (Matrix.trace (H*(G*(P*(G))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G*(P))) (G)))

include hH hG hP hPP in
private theorem w_hgph : (Matrix.trace (H*(G*(P*(H))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(G*(P*(H))))).re = (Matrix.trace (P*(H*(H*(G))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G)) (P*(H))))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(H*(G))))ᴴ = G*(H*(H*(P))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hhgp : (Matrix.trace (H*(H*(G*(P))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(G*(P))))).re = (Matrix.trace (P*(H*(H*(G))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(G))) (P)))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(H*(G))))ᴴ = G*(H*(H*(P))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hhpg : (Matrix.trace (H*(H*(P*(G))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(P*(G))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(P))) (G)))

include hH hG hP hPP in
private theorem w_hhph : (Matrix.trace (H*(H*(P*(H))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(P*(H))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(P))) (H)))

include hH hG hP hPP in
private theorem w_hpgg : (Matrix.trace (H*(P*(G*(G))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(P*(G*(G))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (G*(G))))

include hH hG hP hPP in
private theorem w_hpgh : (Matrix.trace (H*(P*(G*(H))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(P*(G*(H))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (G*(H))))

include hH hG hP hPP in
private theorem w_hphg : (Matrix.trace (H*(P*(H*(G))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (H*(P*(H*(G))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(H))) (G)))

include hH hG hP hPP in
private theorem w_hphh : (Matrix.trace (H*(P*(H*(H))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(P*(H*(H))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (H*(H))))

include hH hG hP hPP in
private theorem w_pggg : (Matrix.trace (P*(G*(G*(G))))).re = (Matrix.trace (G*(G*(G*(P))))).re := by
  calc
    (Matrix.trace (P*(G*(G*(G))))).re = (Matrix.trace (G*(G*(G*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(G*(G)))))

include hH hG hP hPP in
private theorem w_pggh : (Matrix.trace (P*(G*(G*(H))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(G*(G*(H))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(G*(H)))))

include hH hG hP hPP in
private theorem w_pghg : (Matrix.trace (P*(G*(H*(G))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
  calc
    (Matrix.trace (P*(G*(H*(G))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(H*(G)))))

include hH hG hP hPP in
private theorem w_pghh : (Matrix.trace (P*(G*(H*(H))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(G*(H*(H))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(H*(H)))))

include hH hG hP hPP in
private theorem w_phgg : (Matrix.trace (P*(H*(G*(G))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(H*(G*(G))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(G*(G))))ᴴ = G*(G*(H*(P))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_phgh : (Matrix.trace (P*(H*(G*(H))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (P*(H*(G*(H))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H)) (G*(H))))

include hH hG hP hPP in
private theorem w_phhg : (Matrix.trace (P*(H*(H*(G))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(H*(H*(G))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(H*(G))))ᴴ = G*(H*(H*(P))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_phhh : (Matrix.trace (P*(H*(H*(H))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(H*(H*(H))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (H*(H*(H)))))

include hH hG hP hPP in
private theorem w_gpgpg : (Matrix.trace (G*(P*(G*(P*(G)))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (G*(P*(G*(P*(G)))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (G*(P*(G*(P)))) (G)))

include hH hG hP hPP in
private theorem w_gpgph : (Matrix.trace (G*(P*(G*(P*(H)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (G*(P*(G*(P*(H)))))).re = (Matrix.trace (P*(G*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (G) (P*(G*(P*(H))))))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(G*(P*(H*(G)))))ᴴ = G*(H*(P*(G*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_gphpg : (Matrix.trace (G*(P*(H*(P*(G)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (G*(P*(H*(P*(G)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (G*(P*(H*(P)))) (G)))

include hH hG hP hPP in
private theorem w_gphph : (Matrix.trace (G*(P*(H*(P*(H)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (G*(P*(H*(P*(H)))))).re = (Matrix.trace (P*(H*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (G) (P*(H*(P*(H))))))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(P*(H*(G)))))ᴴ = G*(H*(P*(H*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hggpp : (Matrix.trace (H*(G*(G*(P*(P)))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(G*(G*(P*(P)))))).re = (Matrix.trace (P*(P*(H*(G*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G*(G))) (P*(P))))
    _ = (Matrix.trace (G*(G*(H*(P*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(H*(G*(G)))))ᴴ = G*(G*(H*(P*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hghpp : (Matrix.trace (H*(G*(H*(P*(P)))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (H*(G*(H*(P*(P)))))).re = (Matrix.trace (G*(H*(P*(P*(H)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H) (G*(H*(P*(P))))))
    _ = (Matrix.trace (G*(H*(P*(H))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hgpgp : (Matrix.trace (H*(G*(P*(G*(P)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (H*(G*(P*(G*(P)))))).re = (Matrix.trace (P*(G*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G)) (P*(G*(P)))))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(G*(P*(H*(G)))))ᴴ = G*(H*(P*(G*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hgphp : (Matrix.trace (H*(G*(P*(H*(P)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(G*(P*(H*(P)))))).re = (Matrix.trace (P*(H*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G)) (P*(H*(P)))))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(P*(H*(G)))))ᴴ = G*(H*(P*(H*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hgppg : (Matrix.trace (H*(G*(P*(P*(G)))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
  calc
    (Matrix.trace (H*(G*(P*(P*(G)))))).re = (Matrix.trace (G*(H*(G*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G*(P*(P)))) (G)))
    _ = (Matrix.trace (G*(H*(G*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hgpph : (Matrix.trace (H*(G*(P*(P*(H)))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(G*(P*(P*(H)))))).re = (Matrix.trace (P*(P*(H*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(G)) (P*(P*(H)))))
    _ = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(H*(H*(G)))))ᴴ = G*(H*(H*(P*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hhgpp : (Matrix.trace (H*(H*(G*(P*(P)))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(G*(P*(P)))))).re = (Matrix.trace (P*(P*(H*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(G))) (P*(P))))
    _ = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(H*(H*(G)))))ᴴ = G*(H*(H*(P*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hhhpp : (Matrix.trace (H*(H*(H*(P*(P)))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(H*(P*(P)))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hhpgp : (Matrix.trace (H*(H*(P*(G*(P)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(H*(P*(G*(P)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(P))) (G*(P))))

include hH hG hP hPP in
private theorem w_hhppg : (Matrix.trace (H*(H*(P*(P*(G)))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(P*(P*(G)))))).re = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(P*(P)))) (G)))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hhpph : (Matrix.trace (H*(H*(P*(P*(H)))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(H*(P*(P*(H)))))).re = (Matrix.trace (H*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(H*(P*(P)))) (H)))
    _ = (Matrix.trace (H*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hpggp : (Matrix.trace (H*(P*(G*(G*(P)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(G*(G*(P)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (G*(G*(P)))))

include hH hG hP hPP in
private theorem w_hpghp : (Matrix.trace (H*(P*(G*(H*(P)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(G*(H*(P)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (G*(H*(P)))))

include hH hG hP hPP in
private theorem w_hpgpg : (Matrix.trace (H*(P*(G*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(G*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(G*(P)))) (G)))

include hH hG hP hPP in
private theorem w_hpgph : (Matrix.trace (H*(P*(G*(P*(H)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(G*(P*(H)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (G*(P*(H)))))

include hH hG hP hPP in
private theorem w_hphgp : (Matrix.trace (H*(P*(H*(G*(P)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(H*(G*(P)))))).re = (Matrix.trace (P*(H*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(H*(G)))) (P)))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(P*(H*(G)))))ᴴ = G*(H*(P*(H*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_hphhp : (Matrix.trace (H*(P*(H*(H*(P)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(H*(H*(P)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P)) (H*(H*(P)))))

include hH hG hP hPP in
private theorem w_hphpg : (Matrix.trace (H*(P*(H*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(H*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(H*(P)))) (G)))

include hH hG hP hPP in
private theorem w_hphph : (Matrix.trace (H*(P*(H*(P*(H)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (H*(P*(H*(P*(H)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(H*(P)))) (H)))

include hH hG hP hPP in
private theorem w_hppgg : (Matrix.trace (H*(P*(P*(G*(G)))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(P*(P*(G*(G)))))).re = (Matrix.trace (G*(G*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(P))) (G*(G))))
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hppgh : (Matrix.trace (H*(P*(P*(G*(H)))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(P*(P*(G*(H)))))).re = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(P))) (G*(H))))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hpphg : (Matrix.trace (H*(P*(P*(H*(G)))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (H*(P*(P*(H*(G)))))).re = (Matrix.trace (G*(H*(P*(P*(H)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(P*(H)))) (G)))
    _ = (Matrix.trace (G*(H*(P*(H))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_hpphh : (Matrix.trace (H*(P*(P*(H*(H)))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (H*(P*(P*(H*(H)))))).re = (Matrix.trace (H*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (H*(P*(P))) (H*(H))))
    _ = (Matrix.trace (H*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pggpg : (Matrix.trace (P*(G*(G*(P*(G)))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(G*(P*(G)))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(G*(P*(G))))))

include hH hG hP hPP in
private theorem w_pggph : (Matrix.trace (P*(G*(G*(P*(H)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(G*(P*(H)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(G*(P*(H))))))

include hH hG hP hPP in
private theorem w_pghpg : (Matrix.trace (P*(G*(H*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(H*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(H*(P*(G))))))

include hH hG hP hPP in
private theorem w_pghph : (Matrix.trace (P*(G*(H*(P*(H)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(H*(P*(H)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(H*(P*(H))))))

include hH hG hP hPP in
private theorem w_pgpgg : (Matrix.trace (P*(G*(P*(G*(G)))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(G*(G)))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(G*(P))) (G*(G))))

include hH hG hP hPP in
private theorem w_pgpgh : (Matrix.trace (P*(G*(P*(G*(H)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(G*(H)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(G*(P))) (G*(H))))

include hH hG hP hPP in
private theorem w_pgphg : (Matrix.trace (P*(G*(P*(H*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(H*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(G*(P*(H*(G)))))ᴴ = G*(H*(P*(G*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_pgphh : (Matrix.trace (P*(G*(P*(H*(H)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(H*(H)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(P*(H*(H))))))

include hH hG hP hPP in
private theorem w_phgpg : (Matrix.trace (P*(H*(G*(P*(G)))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(G*(P*(G)))))).re = (Matrix.trace (P*(G*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(G))) (P*(G))))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(G*(P*(H*(G)))))ᴴ = G*(H*(P*(G*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_phgph : (Matrix.trace (P*(H*(G*(P*(H)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(G*(P*(H)))))).re = (Matrix.trace (P*(H*(P*(H*(G)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(G))) (P*(H))))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(P*(H*(G)))))ᴴ = G*(H*(P*(H*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_phhpg : (Matrix.trace (P*(H*(H*(P*(G)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(H*(P*(G)))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(H*(P)))) (G)))

include hH hG hP hPP in
private theorem w_phhph : (Matrix.trace (P*(H*(H*(P*(H)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(H*(P*(H)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (H*(H*(P*(H))))))

include hH hG hP hPP in
private theorem w_phpgg : (Matrix.trace (P*(H*(P*(G*(G)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(G*(G)))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(P))) (G*(G))))

include hH hG hP hPP in
private theorem w_phpgh : (Matrix.trace (P*(H*(P*(G*(H)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(G*(H)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(P))) (G*(H))))

include hH hG hP hPP in
private theorem w_phphg : (Matrix.trace (P*(H*(P*(H*(G)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(H*(G)))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(P*(H*(G)))))ᴴ = G*(H*(P*(H*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))

include hH hG hP hPP in
private theorem w_phphh : (Matrix.trace (P*(H*(P*(H*(H)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(H*(H)))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(P))) (H*(H))))

include hH hG hP hPP in
private theorem w_ppggg : (Matrix.trace (P*(P*(G*(G*(G)))))).re = (Matrix.trace (G*(G*(G*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(G*(G)))))).re = (Matrix.trace (G*(G*(G*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(G*(G)))))
    _ = (Matrix.trace (G*(G*(G*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppggh : (Matrix.trace (P*(P*(G*(G*(H)))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(G*(H)))))).re = (Matrix.trace (G*(G*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(G*(H)))))
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppghg : (Matrix.trace (P*(P*(G*(H*(G)))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(H*(G)))))).re = (Matrix.trace (G*(H*(G*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(H*(G)))))
    _ = (Matrix.trace (G*(H*(G*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppghh : (Matrix.trace (P*(P*(G*(H*(H)))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(H*(H)))))).re = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(H*(H)))))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphgg : (Matrix.trace (P*(P*(H*(G*(G)))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(G*(G)))))).re = (Matrix.trace (G*(G*(H*(P*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(H*(G*(G)))))ᴴ = G*(G*(H*(P*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphgh : (Matrix.trace (P*(P*(H*(G*(H)))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(G*(H)))))).re = (Matrix.trace (G*(H*(P*(P*(H)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H))) (G*(H))))
    _ = (Matrix.trace (G*(H*(P*(H))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphhg : (Matrix.trace (P*(P*(H*(H*(G)))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(H*(G)))))).re = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(H*(H*(G)))))ᴴ = G*(H*(H*(P*(P)))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphhh : (Matrix.trace (P*(P*(H*(H*(H)))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(H*(H)))))).re = (Matrix.trace (H*(H*(H*(P*(P)))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (H*(H*(H)))))
    _ = (Matrix.trace (H*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pgpgpg : (Matrix.trace (P*(G*(P*(G*(P*(G))))))).re = (Matrix.trace (G*(P*(G*(P*(G*(P))))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(G*(P*(G))))))).re = (Matrix.trace (G*(P*(G*(P*(G*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(P*(G*(P*(G)))))))

include hH hG hP hPP in
private theorem w_pgpgph : (Matrix.trace (P*(G*(P*(G*(P*(H))))))).re = (Matrix.trace (G*(P*(G*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(G*(P*(H))))))).re = (Matrix.trace (G*(P*(G*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(P*(G*(P*(H)))))))

include hH hG hP hPP in
private theorem w_pgphpg : (Matrix.trace (P*(G*(P*(H*(P*(G))))))).re = (Matrix.trace (G*(P*(G*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(H*(P*(G))))))).re = (Matrix.trace (G*(P*(G*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(G*(P*(H*(P))))) (G)))

include hH hG hP hPP in
private theorem w_pgphph : (Matrix.trace (P*(G*(P*(H*(P*(H))))))).re = (Matrix.trace (G*(P*(H*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(G*(P*(H*(P*(H))))))).re = (Matrix.trace (G*(P*(H*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (G*(P*(H*(P*(H)))))))

include hH hG hP hPP in
private theorem w_phpgpg : (Matrix.trace (P*(H*(P*(G*(P*(G))))))).re = (Matrix.trace (G*(P*(G*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(G*(P*(G))))))).re = (Matrix.trace (G*(P*(G*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(P))) (G*(P*(G)))))

include hH hG hP hPP in
private theorem w_phpgph : (Matrix.trace (P*(H*(P*(G*(P*(H))))))).re = (Matrix.trace (G*(P*(H*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(G*(P*(H))))))).re = (Matrix.trace (G*(P*(H*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(P))) (G*(P*(H)))))

include hH hG hP hPP in
private theorem w_phphpg : (Matrix.trace (P*(H*(P*(H*(P*(G))))))).re = (Matrix.trace (G*(P*(H*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(H*(P*(G))))))).re = (Matrix.trace (G*(P*(H*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(H*(P*(H*(P))))) (G)))

include hH hG hP hPP in
private theorem w_phphph : (Matrix.trace (P*(H*(P*(H*(P*(H))))))).re = (Matrix.trace (H*(P*(H*(P*(H*(P))))))).re := by
  calc
    (Matrix.trace (P*(H*(P*(H*(P*(H))))))).re = (Matrix.trace (H*(P*(H*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P) (H*(P*(H*(P*(H)))))))

include hH hG hP hPP in
private theorem w_ppggpg : (Matrix.trace (P*(P*(G*(G*(P*(G))))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(G*(P*(G))))))).re = (Matrix.trace (G*(G*(P*(G*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(G*(P*(G))))))
    _ = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppggph : (Matrix.trace (P*(P*(G*(G*(P*(H))))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(G*(P*(H))))))).re = (Matrix.trace (G*(G*(P*(H*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(G*(P*(H))))))
    _ = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppghpg : (Matrix.trace (P*(P*(G*(H*(P*(G))))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(H*(P*(G))))))).re = (Matrix.trace (G*(H*(P*(G*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(H*(P*(G))))))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppghph : (Matrix.trace (P*(P*(G*(H*(P*(H))))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(H*(P*(H))))))).re = (Matrix.trace (G*(H*(P*(H*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(H*(P*(H))))))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppgpgg : (Matrix.trace (P*(P*(G*(P*(G*(G))))))).re = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(P*(G*(G))))))).re = (Matrix.trace (G*(G*(P*(P*(G*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(G*(P)))) (G*(G))))
    _ = (Matrix.trace (G*(G*(P*(G*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppgpgh : (Matrix.trace (P*(P*(G*(P*(G*(H))))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(P*(G*(H))))))).re = (Matrix.trace (G*(H*(P*(P*(G*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(G*(P)))) (G*(H))))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppgphg : (Matrix.trace (P*(P*(G*(P*(H*(G))))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(P*(H*(G))))))).re = (Matrix.trace (G*(H*(P*(G*(P*(P))))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(G*(P*(H*(G))))))ᴴ = G*(H*(P*(G*(P*(P))))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppgphh : (Matrix.trace (P*(P*(G*(P*(H*(H))))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(G*(P*(H*(H))))))).re = (Matrix.trace (G*(P*(H*(H*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (G*(P*(H*(H))))))
    _ = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphgpg : (Matrix.trace (P*(P*(H*(G*(P*(G))))))).re = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(G*(P*(G))))))).re = (Matrix.trace (P*(G*(P*(P*(H*(G))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H*(G)))) (P*(G))))
    _ = (Matrix.trace (G*(H*(P*(P*(G*(P))))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(G*(P*(P*(H*(G))))))ᴴ = G*(H*(P*(P*(G*(P))))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(P*(G*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphgph : (Matrix.trace (P*(P*(H*(G*(P*(H))))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(G*(P*(H))))))).re = (Matrix.trace (P*(H*(P*(P*(H*(G))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H*(G)))) (P*(H))))
    _ = (Matrix.trace (G*(H*(P*(P*(H*(P))))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(H*(P*(P*(H*(G))))))ᴴ = G*(H*(P*(P*(H*(P))))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphhpg : (Matrix.trace (P*(P*(H*(H*(P*(G))))))).re = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(H*(P*(G))))))).re = (Matrix.trace (G*(P*(P*(H*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H*(H*(P))))) (G)))
    _ = (Matrix.trace (G*(P*(H*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphhph : (Matrix.trace (P*(P*(H*(H*(P*(H))))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(H*(P*(H))))))).re = (Matrix.trace (H*(H*(P*(H*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P)) (H*(H*(P*(H))))))
    _ = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphpgg : (Matrix.trace (P*(P*(H*(P*(G*(G))))))).re = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(P*(G*(G))))))).re = (Matrix.trace (G*(G*(P*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H*(P)))) (G*(G))))
    _ = (Matrix.trace (G*(G*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphpgh : (Matrix.trace (P*(P*(H*(P*(G*(H))))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(P*(G*(H))))))).re = (Matrix.trace (G*(H*(P*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H*(P)))) (G*(H))))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphphg : (Matrix.trace (P*(P*(H*(P*(H*(G))))))).re = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(P*(H*(G))))))).re = (Matrix.trace (G*(H*(P*(H*(P*(P))))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(H*(P*(H*(G))))))ᴴ = G*(H*(P*(H*(P*(P))))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pphphh : (Matrix.trace (P*(P*(H*(P*(H*(H))))))).re = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
  calc
    (Matrix.trace (P*(P*(H*(P*(H*(H))))))).re = (Matrix.trace (H*(H*(P*(P*(H*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(H*(P)))) (H*(H))))
    _ = (Matrix.trace (H*(H*(P*(H*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pppggg : (Matrix.trace (P*(P*(P*(G*(G*(G))))))).re = (Matrix.trace (G*(G*(G*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(G*(G*(G))))))).re = (Matrix.trace (G*(G*(G*(P*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(P))) (G*(G*(G)))))
    _ = (Matrix.trace (G*(G*(G*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(G*(G*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pppggh : (Matrix.trace (P*(P*(P*(G*(G*(H))))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(G*(G*(H))))))).re = (Matrix.trace (G*(G*(H*(P*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(P))) (G*(G*(H)))))
    _ = (Matrix.trace (G*(G*(H*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pppghg : (Matrix.trace (P*(P*(P*(G*(H*(G))))))).re = (Matrix.trace (G*(H*(G*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(G*(H*(G))))))).re = (Matrix.trace (G*(H*(G*(P*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(P))) (G*(H*(G)))))
    _ = (Matrix.trace (G*(H*(G*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(H*(G*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_pppghh : (Matrix.trace (P*(P*(P*(G*(H*(H))))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(G*(H*(H))))))).re = (Matrix.trace (G*(H*(H*(P*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(P))) (G*(H*(H)))))
    _ = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppphgg : (Matrix.trace (P*(P*(P*(H*(G*(G))))))).re = (Matrix.trace (G*(G*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(H*(G*(G))))))).re = (Matrix.trace (G*(G*(H*(P*(P*(P))))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(P*(H*(G*(G))))))ᴴ = G*(G*(H*(P*(P*(P))))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(G*(H*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(G*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppphgh : (Matrix.trace (P*(P*(P*(H*(G*(H))))))).re = (Matrix.trace (G*(H*(P*(H))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(H*(G*(H))))))).re = (Matrix.trace (G*(H*(P*(P*(P*(H))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(P*(H)))) (G*(H))))
    _ = (Matrix.trace (G*(H*(P*(P*(H)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(H*(P*(H))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppphhg : (Matrix.trace (P*(P*(P*(H*(H*(G))))))).re = (Matrix.trace (G*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(H*(H*(G))))))).re = (Matrix.trace (G*(H*(H*(P*(P*(P))))))).re := by
      simpa only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq,
        Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re, Matrix.mul_assoc] using
        (congrArg (fun M : Matrix n n ℂ => (Matrix.trace M).re)
          (show (P*(P*(P*(H*(H*(G))))))ᴴ = G*(H*(H*(P*(P*(P))))) from by
            simp only [Matrix.conjTranspose_mul, hH.eq, hG.eq, hP.eq, Matrix.mul_assoc]))
    _ = (Matrix.trace (G*(H*(H*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (G*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

include hH hG hP hPP in
private theorem w_ppphhh : (Matrix.trace (P*(P*(P*(H*(H*(H))))))).re = (Matrix.trace (H*(H*(H*(P))))).re := by
  calc
    (Matrix.trace (P*(P*(P*(H*(H*(H))))))).re = (Matrix.trace (H*(H*(H*(P*(P*(P))))))).re := by
      simpa only [Matrix.mul_assoc] using
        (congrArg Complex.re (Matrix.trace_mul_comm (P*(P*(P))) (H*(H*(H)))))
    _ = (Matrix.trace (H*(H*(H*(P*(P)))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]
    _ = (Matrix.trace (H*(H*(H*(P))))).re := by
      simp only [projection_mul_assoc P _ hPP, hPP, Matrix.mul_assoc]

end Words

/-- Exact equality with the actual ordered second and third coefficients.
Only Hermitian adjoint reversal, cyclic trace and `P*P=P` are used. -/
theorem projection_certificate (H G P : Matrix n n ℂ)
    (hH : H.IsHermitian) (hG : G.IsHermitian)
    (hP : P.IsHermitian) (hPP : P*P = P) :
    27 * (coefficient2 (H+G) H P - 3*coefficient3 (H+G) H P) =
      projectionSOS H G P := by
  simp only [projectionSOS, traceLocalizer, coefficient2, coefficient3,
    traceCoefficient2, traceCoefficient3, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_one, hH.eq, hG.eq, hP.eq, star_trivial,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Complex.add_re,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.div_re,
    Complex.ofNat_re, Complex.ofNat_im, zero_mul, mul_zero, sub_zero, add_zero,
    Matrix.mul_assoc]
  simp only [
    w_hgh H G P hH hG hP hPP,
    w_hhg H G P hH hG hP hPP,
    w_gpgh H G P hH hG hP hPP,
    w_hggp H G P hH hG hP hPP,
    w_hghp H G P hH hG hP hPP,
    w_hgpg H G P hH hG hP hPP,
    w_hgph H G P hH hG hP hPP,
    w_hhgp H G P hH hG hP hPP,
    w_hhpg H G P hH hG hP hPP,
    w_hhph H G P hH hG hP hPP,
    w_hpgg H G P hH hG hP hPP,
    w_hpgh H G P hH hG hP hPP,
    w_hphg H G P hH hG hP hPP,
    w_hphh H G P hH hG hP hPP,
    w_pggg H G P hH hG hP hPP,
    w_pggh H G P hH hG hP hPP,
    w_pghg H G P hH hG hP hPP,
    w_pghh H G P hH hG hP hPP,
    w_phgg H G P hH hG hP hPP,
    w_phgh H G P hH hG hP hPP,
    w_phhg H G P hH hG hP hPP,
    w_phhh H G P hH hG hP hPP,
    w_gpgpg H G P hH hG hP hPP,
    w_gpgph H G P hH hG hP hPP,
    w_gphpg H G P hH hG hP hPP,
    w_gphph H G P hH hG hP hPP,
    w_hggpp H G P hH hG hP hPP,
    w_hghpp H G P hH hG hP hPP,
    w_hgpgp H G P hH hG hP hPP,
    w_hgphp H G P hH hG hP hPP,
    w_hgppg H G P hH hG hP hPP,
    w_hgpph H G P hH hG hP hPP,
    w_hhgpp H G P hH hG hP hPP,
    w_hhhpp H G P hH hG hP hPP,
    w_hhpgp H G P hH hG hP hPP,
    w_hhppg H G P hH hG hP hPP,
    w_hhpph H G P hH hG hP hPP,
    w_hpggp H G P hH hG hP hPP,
    w_hpghp H G P hH hG hP hPP,
    w_hpgpg H G P hH hG hP hPP,
    w_hpgph H G P hH hG hP hPP,
    w_hphgp H G P hH hG hP hPP,
    w_hphhp H G P hH hG hP hPP,
    w_hphpg H G P hH hG hP hPP,
    w_hphph H G P hH hG hP hPP,
    w_hppgg H G P hH hG hP hPP,
    w_hppgh H G P hH hG hP hPP,
    w_hpphg H G P hH hG hP hPP,
    w_hpphh H G P hH hG hP hPP,
    w_pggpg H G P hH hG hP hPP,
    w_pggph H G P hH hG hP hPP,
    w_pghpg H G P hH hG hP hPP,
    w_pghph H G P hH hG hP hPP,
    w_pgpgg H G P hH hG hP hPP,
    w_pgpgh H G P hH hG hP hPP,
    w_pgphg H G P hH hG hP hPP,
    w_pgphh H G P hH hG hP hPP,
    w_phgpg H G P hH hG hP hPP,
    w_phgph H G P hH hG hP hPP,
    w_phhpg H G P hH hG hP hPP,
    w_phhph H G P hH hG hP hPP,
    w_phpgg H G P hH hG hP hPP,
    w_phpgh H G P hH hG hP hPP,
    w_phphg H G P hH hG hP hPP,
    w_phphh H G P hH hG hP hPP,
    w_ppggg H G P hH hG hP hPP,
    w_ppggh H G P hH hG hP hPP,
    w_ppghg H G P hH hG hP hPP,
    w_ppghh H G P hH hG hP hPP,
    w_pphgg H G P hH hG hP hPP,
    w_pphgh H G P hH hG hP hPP,
    w_pphhg H G P hH hG hP hPP,
    w_pphhh H G P hH hG hP hPP,
    w_pgpgpg H G P hH hG hP hPP,
    w_pgpgph H G P hH hG hP hPP,
    w_pgphpg H G P hH hG hP hPP,
    w_pgphph H G P hH hG hP hPP,
    w_phpgpg H G P hH hG hP hPP,
    w_phpgph H G P hH hG hP hPP,
    w_phphpg H G P hH hG hP hPP,
    w_phphph H G P hH hG hP hPP,
    w_ppggpg H G P hH hG hP hPP,
    w_ppggph H G P hH hG hP hPP,
    w_ppghpg H G P hH hG hP hPP,
    w_ppghph H G P hH hG hP hPP,
    w_ppgpgg H G P hH hG hP hPP,
    w_ppgpgh H G P hH hG hP hPP,
    w_ppgphg H G P hH hG hP hPP,
    w_ppgphh H G P hH hG hP hPP,
    w_pphgpg H G P hH hG hP hPP,
    w_pphgph H G P hH hG hP hPP,
    w_pphhpg H G P hH hG hP hPP,
    w_pphhph H G P hH hG hP hPP,
    w_pphpgg H G P hH hG hP hPP,
    w_pphpgh H G P hH hG hP hPP,
    w_pphphg H G P hH hG hP hPP,
    w_pphphh H G P hH hG hP hPP,
    w_pppggg H G P hH hG hP hPP,
    w_pppggh H G P hH hG hP hPP,
    w_pppghg H G P hH hG hP hPP,
    w_pppghh H G P hH hG hP hPP,
    w_ppphgg H G P hH hG hP hPP,
    w_ppphgh H G P hH hG hP hPP,
    w_ppphhg H G P hH hG hP hPP,
    w_ppphhh H G P hH hG hP hPP]
  ring

end D5.S3.Quantum.Matrix.HsfProjectionCubic
