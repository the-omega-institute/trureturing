/- GID: D5/S3/Quantum/Recovery/BKMDiagonalStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMDiagonalStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace, positivity and log-conditioned stability of diagonal BKM recovery. -/

import D5.S3.Quantum.Recovery.BKMRelativeDensity
import D5.S3.Quantum.Recovery.BKMSpectralVariance
import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Schatten.TraceNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Diagonal stability for the actual finite BKM recovery -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Recovery.BKMRelativeDensity (continuous_mpow mpow_smul_of_nonneg omega)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Recovery.BKMSpectralVariance
  (fromEigenbasis omegaLinear omega_isHermitian omega_rankOne_isHermitian omega_rankOne_trace_re
    omega_rankOne_trace_sq_sub_trace_sq_ge omega_trace_eq_trace_mul trace_conjStarAlgAut_symm)

namespace D5.S3.Quantum.Recovery.BKMDiagonalStability

section MatrixBridge

open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The negative trace is the sum of the negative parts of the actual Hermitian eigenvalues. -/
def spectralNegativeTrace {M : Matrix n n ℂ} (hM : M.IsHermitian) : ℝ :=
  ∑ i, max (-hM.eigenvalues i) 0

/-- The positive and negative spectral parts bound the Hermitian trace-square deficit. -/
private theorem hermitian_trace_sq_sub_trace_sq_le (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    let t := M.trace.re
    let ν := spectralNegativeTrace hM
    (M * M).trace.re - t ^ 2 ≤ 2 * ν * (t + ν) := by
  let eigenvalue := hM.eigenvalues
  let p := fun i => max (eigenvalue i) 0
  let q := fun i => max (-eigenvalue i) 0
  let F := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
  have hdiag : F.symm M = diagonal (fun i => (eigenvalue i : ℂ)) := by
    conv_lhs => rw [hM.spectral_theorem]
    exact F.symm_apply_apply _
  have htrace : M.trace.re = ∑ i, eigenvalue i := by
    rw [hM.trace_eq_sum_eigenvalues]
    simp [eigenvalue]
  have hsq : (M * M).trace.re = ∑ i, eigenvalue i ^ 2 := by
    rw [← trace_conjStarAlgAut_symm hM.eigenvectorUnitary (M * M)]
    change (F.symm (M * M)).trace.re = _
    rw [map_mul, hdiag, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re, pow_two]
  have hsplit (i : n) : eigenvalue i = p i - q i ∧ eigenvalue i ^ 2 = p i ^ 2 + q i ^ 2 := by
    by_cases hi : 0 ≤ eigenvalue i
    · simp [p, q, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
    · have hn := le_of_lt (lt_of_not_ge hi)
      simp [p, q, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
  have hp : (∑ i, p i) = M.trace.re + ∑ i, q i := by
    rw [htrace, Finset.sum_congr rfl (fun i _ => (hsplit i).1), Finset.sum_sub_distrib]
    ring
  have hpos : (∑ i, p i ^ 2) ≤ (∑ i, p i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => le_max_right _ _
  have hneg : (∑ i, q i ^ 2) ≤ (∑ i, q i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => le_max_right _ _
  change (M * M).trace.re - M.trace.re ^ 2 ≤
    2 * (∑ i, q i) * (M.trace.re + ∑ i, q i)
  rw [hsq, Finset.sum_congr rfl (fun i _ => (hsplit i).2), Finset.sum_add_distrib]
  rw [hp] at hpos
  linarith only [hpos, hneg]

/-- Both trace-square bounds for the same actual BKM output give the variance estimate
under its finite spectral negative trace bound. The vector is in the eigenbasis of `a`. -/
private theorem omega_rankOne_variance_le {a : Matrix n n ℂ} (ha : a.PosDef)
    (v : n → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) (T ε : ℝ)
    (hT : ∀ i j, |Real.log (ha.isHermitian.eigenvalues i / ha.isHermitian.eigenvalues j)| ≤ T)
    (hdefect : spectralNegativeTrace (omega_rankOne_isHermitian ha v) ≤
      ε * (omega a ((fromEigenbasis ha) (vecMulVec v (starRingEnd ℂ ∘ v)))).trace.re) :
    let p := fun i => ‖v i‖ ^ 2
    let eigenvalue := ha.isHermitian.eigenvalues
    let t := (omega a ((fromEigenbasis ha) (vecMulVec v (starRingEnd ℂ ∘ v)))).trace.re
    (∑ i, p i * eigenvalue i ^ 2) - (∑ i, p i * eigenvalue i) ^ 2 ≤
      (12 + T ^ 2) * ε * (1 + ε) * t ^ 2 := by
  let M := omega a ((fromEigenbasis ha) (vecMulVec v (starRingEnd ℂ ∘ v)))
  let t := M.trace.re
  let ν := spectralNegativeTrace (omega_rankOne_isHermitian ha v)
  have ht : 0 ≤ t := by
    change 0 ≤ M.trace.re
    rw [omega_rankOne_trace_re ha v]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (ha.eigenvalues_pos i).le
  have hν : 0 ≤ ν := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hb : ν ≤ ε * t := hdefect
  have hbounded : 2 * ν * (t + ν) ≤ 2 * (ε * t) * (t + ε * t) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) (add_le_add_right hb t)
      (add_nonneg ht hν) (mul_nonneg (by norm_num) (hν.trans hb))
  have h := (omega_rankOne_trace_sq_sub_trace_sq_ge ha v hv T hT).trans
    ((hermitian_trace_sq_sub_trace_sq_le M (omega_rankOne_isHermitian ha v)).trans hbounded)
  have hscaled := (div_le_iff₀ (by positivity : 0 < 12 + T ^ 2)).mp h
  dsimp only
  linarith only [hscaled]

end MatrixBridge

section ColumnAggregation

open scoped ComplexOrder MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM (traceNorm_mul_le_hsSq)

omit [DecidableEq n] in
/-- Factor by square roots of the column weights and apply finite Schatten Hölder. -/
private theorem traceNorm_le_of_weighted_columns (A : Matrix n n ℂ) (w : n → ℝ)
    (hw : ∀ i, 0 < w i) (C : ℝ) (hC : 0 ≤ C)
    (hcol : ∀ i, (∑ j, ‖A j i‖ ^ 2) ≤ C * w i ^ 2) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm A ≤ Real.sqrt C * ∑ i, w i := by
  classical
  let D : Matrix n n ℂ := diagonal fun i => (Real.sqrt (w i) : ℂ)
  let R : Matrix n n ℂ := A * diagonal (fun i => ((Real.sqrt (w i) : ℂ)⁻¹))
  have hfactor : R * D = A := by
    ext j i
    have hroot : (Real.sqrt (w i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hw i)).ne'
    simp [R, D, mul_diagonal, hroot]
  have hD : entryNormSq D = ∑ i, w i := by
    unfold entryNormSq
    apply Finset.sum_congr rfl
    intro i _
    have hentry (j : n) : ‖D i j‖ ^ 2 = if i = j then w i else 0 := by
      by_cases hij : i = j
      · subst j
        simp [D, Complex.norm_real, Real.norm_eq_abs, Real.sq_sqrt (hw i).le]
      · simp [D, hij]
    simp only [hentry, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hR : entryNormSq R ≤ C * ∑ i, w i := by
    rw [entryNormSq, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hentry (j : n) : ‖R j i‖ ^ 2 = ‖A j i‖ ^ 2 / w i := by
      simp [R, mul_diagonal, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, inv_pow, Real.sq_sqrt (hw i).le, div_eq_mul_inv]
    simp only [hentry, ← Finset.sum_div]
    exact (div_le_iff₀ (hw i)).2 (by simpa only [pow_two, mul_assoc] using hcol i)
  have hwSum : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  calc
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm A ≤
        Real.sqrt (entryNormSq R) * Real.sqrt (entryNormSq D) := by
      rw [← hfactor]
      exact traceNorm_mul_le_hsSq R D
    _ ≤ Real.sqrt (C * ∑ i, w i) * Real.sqrt (∑ i, w i) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hR) (Real.sqrt_nonneg _) |>.trans_eq
        (by rw [hD])
    _ = Real.sqrt C * ∑ i, w i := by
      rw [Real.sqrt_mul hC, mul_assoc, Real.mul_self_sqrt hwSum]

/-- The rank-one projector of the standard coordinate vector indexed by `i`. -/
def coordinateProjector (i : n) : Matrix n n ℂ :=
  vecMulVec (Pi.single i 1) (star (Pi.single i 1))

private theorem coordinate_omega_isHermitian {a : Matrix n n ℂ} (ha : a.PosDef) (i : n) :
    (omega a (coordinateProjector i)).IsHermitian :=
  omega_isHermitian ha (Matrix.posSemidef_vecMulVec_self_star (Pi.single i 1)).isHermitian

/-- For a coordinate input, the spectral variance is the squared off-diagonal column norm
and the BKM output trace is the corresponding diagonal entry. -/
private theorem coordinate_omega_trace_and_column_le {a : Matrix n n ℂ} (ha : a.PosDef)
    (i : n) (T ε : ℝ)
    (hT : ∀ j k, |Real.log (ha.isHermitian.eigenvalues j / ha.isHermitian.eigenvalues k)| ≤ T)
    (hdefect : spectralNegativeTrace (coordinate_omega_isHermitian ha i) ≤
      ε * (omega a (coordinateProjector i)).trace.re) :
    (∑ j, ‖(a - diagonal (fun k => a k k)) j i‖ ^ 2) ≤
      (12 + T ^ 2) * ε * (1 + ε) * (a i i).re ^ 2 := by
  let W : Matrix n n ℂ := ha.isHermitian.eigenvectorUnitary
  let F := fromEigenbasis ha
  let e : n → ℂ := Pi.single i 1
  let v := Wᴴ *ᵥ e
  let eigenvalue := ha.isHermitian.eigenvalues
  have hW : W * Wᴴ = 1 := Unitary.coe_mul_star_self ha.isHermitian.eigenvectorUnitary
  have hvEntry (j : n) : v j = star (W i j) := by
    simp only [v, e, mulVec_single_one, Matrix.col_apply, conjTranspose_apply]
  have hprob : ∑ j, ‖v j‖ ^ 2 = 1 := by
    have h := congrArg (fun B : Matrix n n ℂ => (B i i).re) hW
    change ((W * Wᴴ) i i).re = ((1 : Matrix n n ℂ) i i).re at h
    simp only [hvEntry, norm_star]
    simpa only [mul_apply, conjTranspose_apply, Complex.re_sum, Complex.star_def,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, one_apply_eq, Complex.one_re]
      using h
  have hproj : F (vecMulVec v (starRingEnd ℂ ∘ v)) = coordinateProjector i := by
    change W * vecMulVec v (star v) * Wᴴ = vecMulVec e (star e)
    have hWe : W *ᵥ v = e := by
      dsimp only [v]
      rw [mulVec_mulVec, hW, one_mulVec]
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hWe]
  have hmoment (f : n → ℝ) :
      (F (diagonal fun j => (f j : ℂ)) i i).re = ∑ j, ‖v j‖ ^ 2 * f j := by
    change ((W * diagonal (fun j => (f j : ℂ)) * Wᴴ) i i).re = _
    simp only [mul_apply (M := W * diagonal _), mul_diagonal, conjTranspose_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hvEntry, norm_star]
    have hterm : W i j * (f j : ℂ) * star (W i j) = (‖W i j‖ ^ 2 * f j : ℝ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
      change W i j * (f j : ℂ) * (starRingEnd ℂ) (W i j) = _
      ring
    rw [hterm, Complex.ofReal_re]
  have hfirst : (a i i).re = ∑ j, ‖v j‖ ^ 2 * eigenvalue j := by
    rw [show a = F (diagonal fun j => (eigenvalue j : ℂ)) from ha.isHermitian.spectral_theorem]
    exact hmoment eigenvalue
  have hsecond : ((a * a) i i).re = ∑ j, ‖v j‖ ^ 2 * eigenvalue j ^ 2 := by
    have hs : a * a = F (diagonal fun j => (eigenvalue j ^ 2 : ℝ)) := by
      have h : a = F (diagonal fun j => (eigenvalue j : ℂ)) := ha.isHermitian.spectral_theorem
      conv_lhs => rw [h, ← map_mul, diagonal_mul_diagonal]
      simp only [pow_two, Complex.ofReal_mul]
    rw [hs]
    exact hmoment (fun j => eigenvalue j ^ 2)
  have htrace : (omega a (coordinateProjector i)).trace.re = (a i i).re := by
    rw [← hproj, omega_rankOne_trace_re, hfirst]
  have hgram : ((a * a) i i).re = ∑ j, ‖a j i‖ ^ 2 := by
    simp only [mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← ha.isHermitian.apply i j, mul_comm]
    change (a j i * (starRingEnd ℂ) (a j i)).re = _
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hd : ‖a i i‖ ^ 2 = (a i i).re ^ 2 := by
    have hreal : ((a i i).re : ℂ) = a i i := ha.isHermitian.coe_re_apply_self i
    calc
      _ = ‖((a i i).re : ℂ)‖ ^ 2 := congrArg (fun z : ℂ => ‖z‖ ^ 2) hreal.symm
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs]
  have hcolumn :
      (∑ j, ‖(a - diagonal (fun k => a k k)) j i‖ ^ 2) =
        ((a * a) i i).re - (a i i).re ^ 2 := by
    have hj (j : n) : ‖(a - diagonal (fun k => a k k)) j i‖ ^ 2 =
        ‖a j i‖ ^ 2 - (if j = i then ‖a i i‖ ^ 2 else 0) := by
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    simp only [hj, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← hgram, hd]
  rw [hcolumn, hsecond, hfirst]
  have hneg : spectralNegativeTrace (omega_rankOne_isHermitian ha v) ≤
      ε * (omega a (F (vecMulVec v (starRingEnd ℂ ∘ v)))).trace.re := by
    have hsame {A B : Matrix n n ℂ} (h : A = B)
        (hA : A.IsHermitian) (hB : B.IsHermitian) :
        spectralNegativeTrace hA = spectralNegativeTrace hB := by
      subst B
      rfl
    rw [hsame (congrArg (omega a) hproj) (omega_rankOne_isHermitian ha v)
      (coordinate_omega_isHermitian ha i), hproj]
    exact hdefect
  have hbound := omega_rankOne_variance_le ha v hprob T ε hT hneg
  dsimp only at hbound
  change (∑ j, ‖v j‖ ^ 2 * eigenvalue j ^ 2) -
    (∑ j, ‖v j‖ ^ 2 * eigenvalue j) ^ 2 ≤
    (12 + T ^ 2) * ε * (1 + ε) * (omega a (F (vecMulVec v (starRingEnd ℂ ∘ v)))).trace.re ^ 2
    at hbound
  rw [hproj, htrace, hfirst] at hbound
  exact hbound

/-- Weighted aggregation for the actual standard-coordinate BKM outputs. -/
private theorem omega_diagonal_traceNorm_le {a : Matrix n n ℂ} (ha : a.PosDef) (T ε : ℝ)
    (hT : ∀ i j, |Real.log (ha.isHermitian.eigenvalues i / ha.isHermitian.eigenvalues j)| ≤ T)
    (hε : 0 ≤ ε)
    (hdefect : ∀ i, spectralNegativeTrace (coordinate_omega_isHermitian ha i) ≤
      ε * (omega a (coordinateProjector i)).trace.re) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (a - diagonal (fun i => a i i)) ≤
      Real.sqrt ((12 + T ^ 2) * ε * (1 + ε)) * a.trace.re := by
  have hw (i : n) : 0 < (a i i).re := (Complex.pos_iff.mp ha.diag_pos).1
  have hsum : (∑ i, (a i i).re) = a.trace.re := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  rw [← hsum]
  exact traceNorm_le_of_weighted_columns _ _ hw _ (by positivity)
    (fun i => coordinate_omega_trace_and_column_le ha i T ε hT (hdefect i))

end ColumnAggregation

section DiagonalRecovery

open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_of_posSemidef)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_smul_nonneg)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_diagonal)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace-preserving conditional expectation onto the diagonal algebra. -/
def diagonalPart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  diagonal fun i => A i i

/-- Coordinate division by the diagonal of the reference state. -/
def diagonalOmegaInverse (a B : Matrix n n ℂ) : Matrix n n ℂ :=
  diagonal fun i => B i i / a i i

/-- BKM recovery on the diagonal algebra. The matrix formula uses only diagonal inputs. -/
def diagonalRecovery (a B : Matrix n n ℂ) : Matrix n n ℂ :=
  omega a (diagonalOmegaInverse a B)

omit [Fintype n] [DecidableEq n] in
private theorem diag_re_pos {a : Matrix n n ℂ} (ha : a.PosDef) (i : n) :
    0 < (a i i).re := (Complex.pos_iff.mp ha.diag_pos).1

private theorem omega_diagonal_on_diagonal {a : Matrix n n ℂ} (ha : a.PosDef) (b : n → ℂ) :
    omega (diagonalPart a) (diagonal b) = diagonal fun i => a i i * b i := by
  have hpow (s : ℝ) :
      mpow (diagonalPart a) s = diagonal fun i => (((a i i).re ^ s : ℝ) : ℂ) := by
    unfold mpow diagonalPart
    have he : diagonal (fun i => ((a i i).re : ℂ)) = diagonal (fun i => a i i) :=
      congrArg diagonal (funext ha.isHermitian.coe_re_apply_self)
    rw [← he]
    exact cfc_diagonal (fun t : ℝ => t ^ s) (fun i => (a i i).re)
  have hpoint (s : ℝ) :
      mpow (diagonalPart a) s * diagonal b * mpow (diagonalPart a) (1 - s) =
        diagonal fun i => a i i * b i := by
    rw [hpow, hpow, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    calc
      _ = (((a i i).re ^ s : ℝ) : ℂ) * (((a i i).re ^ (1 - s) : ℝ) : ℂ) * b i := by ring
      _ = _ := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add (diag_re_pos ha i),
          show s + (1 - s) = 1 by ring, Real.rpow_one]
        exact congrArg (fun z : ℂ => z * b i) (ha.isHermitian.coe_re_apply_self i)
  simp only [omega, hpoint, intervalIntegral.integral_const, sub_zero, one_smul]

/-- The restriction of the actual integral on the diagonal algebra has the stated
two-sided inverse. -/
theorem diagonalOmegaInverse_spec {a B : Matrix n n ℂ} (ha : a.PosDef)
    (hB : diagonalPart B = B) :
    omega (diagonalPart a) (diagonalOmegaInverse a B) = B ∧
      diagonalOmegaInverse a (omega (diagonalPart a) B) = B := by
  have hn (i : n) : a i i ≠ 0 := ha.diag_pos.ne'
  constructor
  · rw [diagonalOmegaInverse, omega_diagonal_on_diagonal ha]
    exact (congrArg diagonal (funext fun i => mul_div_cancel₀ (B i i) (hn i))).trans hB
  · conv_lhs => rw [← hB]
    change diagonalOmegaInverse a (omega (diagonalPart a) (diagonal fun i => B i i)) = B
    rw [omega_diagonal_on_diagonal ha, diagonalOmegaInverse]
    calc
      _ = diagonalPart B := by
        congr 1
        funext i
        simp [mul_comm (a i i), hn i]
      _ = B := hB

private theorem omega_smul_reference {a : Matrix n n ℂ} (ha : a.PosDef)
    {c : ℝ} (hc : 0 < c) (B : Matrix n n ℂ) :
    omega (c • a) B = c • omega a B := by
  rw [omega, omega, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [Set.uIcc_of_le (zero_le_one' ℝ)] at hs
  rw [mpow_smul_of_nonneg ha.posSemidef.nonneg hc.le hs.1,
    mpow_smul_of_nonneg ha.posSemidef.nonneg hc.le (sub_nonneg.mpr hs.2),
    Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Real.rpow_add hc, show s + (1 - s) = 1 by ring,
    Real.rpow_one]

private def diagonalRecoveryLinear {a : Matrix n n ℂ} (ha : a.PosDef) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
  (omegaLinear ha).comp
    ({ toFun := diagonalOmegaInverse a
       map_add' B C := by
         simp only [diagonalOmegaInverse, Matrix.add_apply, add_div, ← diagonal_add]
       map_smul' c B := by
         change diagonal (fun i => (c * B i i) / a i i) =
           c • diagonal (fun i => B i i / a i i)
         rw [← diagonal_smul]
         congr 1
         funext i
         exact mul_div_assoc c (B i i) (a i i) } :
      Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)

private theorem diagonalRecovery_smul_reference {a : Matrix n n ℂ} (ha : a.PosDef)
    {c : ℝ} (hc : 0 < c) (B : Matrix n n ℂ) :
    diagonalRecovery (c • a) B = diagonalRecovery a B := by
  have hdivide : diagonalOmegaInverse (c • a) B = (c⁻¹ : ℂ) • diagonalOmegaInverse a B := by
    rw [diagonalOmegaInverse, diagonalOmegaInverse, ← diagonal_smul]
    congr 1
    funext i
    change B i i / ((c : ℂ) * a i i) = (c⁻¹ : ℂ) * (B i i / a i i)
    field_simp [Complex.ofReal_ne_zero.mpr hc.ne', (ha.diag_pos (i := i)).ne']
  unfold diagonalRecovery
  rw [omega_smul_reference ha hc, hdivide]
  change (c : ℂ) • omegaLinear ha ((c⁻¹ : ℂ) • diagonalOmegaInverse a B) = _
  rw [map_smul, smul_smul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]
  rfl

omit [Fintype n] in
private theorem coordinateProjector_eq_diagonal (i : n) :
    coordinateProjector i = diagonal (Pi.single i (1 : ℂ)) := by
  ext j k
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      simp [coordinateProjector, vecMulVec_apply]
    · simp [coordinateProjector, vecMulVec_apply, Ne.symm hk]
  · simp [coordinateProjector, vecMulVec_apply, diagonal_apply, hj]

private theorem coordinateProjector_rank (i : n) : (coordinateProjector i).rank = 1 := by
  classical
  rw [coordinateProjector_eq_diagonal, Matrix.rank_diagonal, Fintype.card_subtype]
  have h : Finset.univ.filter (fun j => (Pi.single i 1 : n → ℂ) j ≠ 0) = {i} := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h, Finset.card_singleton]

/-- A positive semidefinite trace-one element of the diagonal algebra. -/
def DiagonalTest (B : Matrix n n ℂ) : Prop :=
  diagonalPart B = B ∧ B.PosSemidef ∧ B.trace = 1

private theorem coordinateProjector_test (i : n) : DiagonalTest (coordinateProjector i) := by
  refine ⟨?_, Matrix.posSemidef_vecMulVec_self_star (Pi.single i 1), ?_⟩
  · rw [coordinateProjector_eq_diagonal]
    simp [diagonalPart]
  · rw [coordinateProjector_eq_diagonal, trace_diagonal]
    simp

private theorem coordinate_recovery_smul {a : Matrix n n ℂ} (ha : a.PosDef) (i : n) :
    (a i i).re • diagonalRecovery a (coordinateProjector i) =
      omega a (coordinateProjector i) := by
  have hinput : (a i i).re • diagonalOmegaInverse a (coordinateProjector i) =
      coordinateProjector i := by
    rw [coordinateProjector_eq_diagonal, diagonalOmegaInverse, ← diagonal_smul]
    congr 1
    funext j
    change ((a i i).re : ℂ) * (diagonal (Pi.single i (1 : ℂ)) j j / a j j) =
      (Pi.single i 1 : n → ℂ) j
    rw [diagonal_apply_eq]
    by_cases hj : j = i
    · subst j
      have hr : ((a i i).re : ℂ) = a i i := ha.isHermitian.coe_re_apply_self i
      rw [hr, mul_div_cancel₀ _ ha.diag_pos.ne']
    · simp [Pi.single_eq_of_ne hj]
  change (↑(a i i).re : ℂ) • omegaLinear ha (diagonalOmegaInverse a (coordinateProjector i)) =
    omegaLinear ha (coordinateProjector i)
  rw [← map_smul]
  exact congrArg (omegaLinear ha) hinput

private theorem traceNorm_hermitian_eq_sum_abs {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    traceNorm M = ∑ i, |hM.eigenvalues i| := by
  change (CFC.abs M).trace.re = _
  rw [CFC.abs_eq_cfc_norm M hM.isSelfAdjoint]
  let U := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
  rw [← trace_conjStarAlgAut_symm hM.eigenvectorUnitary, hM.cfc_eq]
  change (U.symm (U (diagonal fun i => (‖hM.eigenvalues i‖ : ℝ)))).trace.re = _
  rw [U.symm_apply_apply, trace_diagonal, Complex.re_sum]
  simp [Real.norm_eq_abs]

/-- The sum of the magnitudes of the negative eigenvalues is the trace-norm defect. -/
private theorem spectralNegativeTrace_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    spectralNegativeTrace hM = (traceNorm M - M.trace.re) / 2 := by
  rw [traceNorm_hermitian_eq_sum_abs hM, hM.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, ← Finset.sum_sub_distrib, Finset.sum_div,
    spectralNegativeTrace]
  apply Finset.sum_congr rfl
  intro i _
  change max (-hM.eigenvalues i) 0 = (|hM.eigenvalues i| - hM.eigenvalues i) / 2
  by_cases hi : 0 ≤ hM.eigenvalues i
  · rw [abs_of_nonneg hi, max_eq_right (neg_nonpos.mpr hi), sub_self, zero_div]
  · have h := le_of_lt (lt_of_not_ge hi)
    rw [abs_of_nonpos h, max_eq_left (neg_nonneg.mpr h)]
    ring

/-- The negative trace formula, defined on all matrices for use in sums. -/
def negativeTrace (M : Matrix n n ℂ) : ℝ :=
  (traceNorm M - M.trace.re) / 2

private theorem diagonalRecovery_isHermitian {a B : Matrix n n ℂ} (ha : a.PosDef)
    (hB : B.IsHermitian) : (diagonalRecovery a B).IsHermitian := by
  apply omega_isHermitian ha
  rw [diagonalOmegaInverse, isHermitian_diagonal_iff]
  intro i
  have hnum : ((B i i).re : ℂ) = B i i := hB.coe_re_apply_self i
  have hden : ((a i i).re : ℂ) = a i i := ha.isHermitian.coe_re_apply_self i
  rw [← hnum, ← hden, ← Complex.ofReal_div]
  simp [IsSelfAdjoint]

theorem diagonalRecovery_negativeTrace_eq_spectral {a B : Matrix n n ℂ} (ha : a.PosDef)
    (hB : DiagonalTest B) :
    negativeTrace (diagonalRecovery a B) =
      spectralNegativeTrace (diagonalRecovery_isHermitian ha hB.2.1.isHermitian) :=
  (spectralNegativeTrace_eq _).symm

omit [DecidableEq n] in
private theorem negativeTrace_smul (M : Matrix n n ℂ) {c : ℝ} (hc : 0 ≤ c) :
    negativeTrace (c • M) = c * negativeTrace M := by
  classical
  change negativeTrace ((c : ℂ) • M) = _
  rw [negativeTrace, traceNorm_smul_nonneg M c hc, trace_smul, negativeTrace]
  simp [smul_eq_mul, Complex.mul_re]
  ring

/-- The coordinate negativity of recovery has the scaling required by the
actual BKM output on the projection. -/
private theorem coordinate_recovery_negativeTrace {a : Matrix n n ℂ} (ha : a.PosDef) (i : n) :
    negativeTrace (diagonalRecovery a (coordinateProjector i)) * (a i i).re =
      spectralNegativeTrace (coordinate_omega_isHermitian ha i) := by
  rw [spectralNegativeTrace_eq, ← coordinate_recovery_smul ha i]
  change _ = negativeTrace ((a i i).re • diagonalRecovery a (coordinateProjector i))
  rw [negativeTrace_smul _ (diag_re_pos ha i).le, mul_comm]

/-- The actual recovery preserves the complex trace on the diagonal algebra. -/
theorem diagonalRecovery_trace {a B : Matrix n n ℂ} (ha : a.PosDef)
    (hB : diagonalPart B = B) : (diagonalRecovery a B).trace = B.trace := by
  calc
    _ = (a * diagonalOmegaInverse a B).trace := omega_trace_eq_trace_mul ha _
    _ = (omega (diagonalPart a) (diagonalOmegaInverse a B)).trace := by
      rw [diagonalOmegaInverse, omega_diagonal_on_diagonal ha]
      simp [Matrix.trace, Matrix.mul_diagonal]
    _ = B.trace := congrArg Matrix.trace (diagonalOmegaInverse_spec ha hB).1

private theorem coordinate_omega_trace_re {a : Matrix n n ℂ} (ha : a.PosDef) (i : n) :
    (omega a (coordinateProjector i)).trace.re = (a i i).re := by
  rw [← coordinate_recovery_smul ha i, trace_smul,
    diagonalRecovery_trace ha (coordinateProjector_test i).1, (coordinateProjector_test i).2.2]
  simp [Complex.real_smul]

/-- The defect over all positive semidefinite trace-one elements of the diagonal algebra. -/
def diagonalRecoveryDefect (a : Matrix n n ℂ) : ℝ :=
  sSup {ε : ℝ | ∃ B : Matrix n n ℂ, DiagonalTest B ∧ negativeTrace (diagonalRecovery a B) = ε}

omit [DecidableEq n] in
private theorem traceNorm_eq_re_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  have h : (↑(traceNorm A) : ℂ) = A.trace := traceNorm_of_posSemidef hA
  simpa only [Complex.ofReal_re] using congrArg Complex.re h

omit [DecidableEq n] in
private theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix n n ℂ) :
    traceNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, traceNorm (f i) := by
  classical
  refine Finset.le_sum_of_subadditive traceNorm ?_
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le s f
  simp [traceNorm_eq_re_trace (Matrix.PosSemidef.zero (n := n) (R := ℂ))]

omit [DecidableEq n] in
private theorem negativeTrace_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix n n ℂ) :
    negativeTrace (∑ i ∈ s, f i) ≤ ∑ i ∈ s, negativeTrace (f i) := by
  simp only [negativeTrace, trace_sum, Complex.re_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
  linarith only [traceNorm_sum_le s f]

private theorem diagonalTest_decomposition {B : Matrix n n ℂ} (hB : DiagonalTest B) :
    B = ∑ i, (B i i).re • coordinateProjector i := by
  conv_lhs => rw [← hB.1]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [diagonalPart, diagonal_apply_eq, Matrix.sum_apply, Matrix.smul_apply,
      coordinateProjector_eq_diagonal]
    have h (i : n) : (B i i).re • ((Pi.single i 1 : n → ℂ) j) =
        if j = i then B j j else 0 := by
      by_cases hji : j = i
      · subst i
        simpa [Complex.real_smul] using
          (show ((B j j).re : ℂ) = B j j from hB.2.1.isHermitian.coe_re_apply_self j)
      · simp [hji]
    simp [h]
  · simp [diagonalPart, diagonal_apply_ne _ hjk, Matrix.sum_apply, Matrix.smul_apply,
      coordinateProjector_eq_diagonal]

private theorem diagonalRecovery_convex_bound {a B : Matrix n n ℂ} (ha : a.PosDef)
    (hB : DiagonalTest B) (m : ℝ)
    (hm : ∀ i, negativeTrace (diagonalRecovery a (coordinateProjector i)) ≤ m) :
    negativeTrace (diagonalRecovery a B) ≤ m := by
  have hweight (i : n) : 0 ≤ (B i i).re := (Complex.nonneg_iff.mp (hB.2.1.diag_nonneg)).1
  have htotal : (∑ i, (B i i).re) = 1 := by
    simpa [Matrix.trace, Complex.re_sum] using congrArg Complex.re hB.2.2
  have hout : diagonalRecovery a B =
      ∑ i, (B i i).re • diagonalRecovery a (coordinateProjector i) := by
    change diagonalRecoveryLinear ha B =
      ∑ i, ((B i i).re : ℂ) • diagonalRecoveryLinear ha (coordinateProjector i)
    conv_lhs => rw [diagonalTest_decomposition hB]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (diagonalRecoveryLinear ha).map_smul ((B i i).re : ℂ) _
  rw [hout]
  calc
    _ ≤ ∑ i, negativeTrace ((B i i).re • diagonalRecovery a (coordinateProjector i)) :=
      negativeTrace_sum_le _ _
    _ ≤ ∑ i, (B i i).re * m :=
      Finset.sum_le_sum fun i _ => by
        rw [negativeTrace_smul _ (hweight i)]
        exact mul_le_mul_of_nonneg_left (hm i) (hweight i)
    _ = m := by rw [← Finset.sum_mul, htotal, one_mul]

/-- A coordinate test attains the all-test supremum, and its value bounds every
positive trace-one diagonal test. -/
theorem diagonalRecoveryDefect_isGreatest [Nonempty n] {a : Matrix n n ℂ} (ha : a.PosDef) :
    ∃ i, (coordinateProjector i).rank = 1 ∧ IsGreatest {ε : ℝ | ∃ B : Matrix n n ℂ,
        DiagonalTest B ∧ negativeTrace (diagonalRecovery a B) = ε}
      (negativeTrace (diagonalRecovery a (coordinateProjector i))) := by
  let f := fun i : n => negativeTrace (diagonalRecovery a (coordinateProjector i))
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨i, coordinateProjector_rank i,
    ⟨coordinateProjector i, coordinateProjector_test i, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact diagonalRecovery_convex_bound ha hB (f i) (fun j => hi j (Finset.mem_univ j))

private theorem diagonalRecoveryDefect_eq_max_coordinate [Nonempty n] {a : Matrix n n ℂ}
    (ha : a.PosDef) :
    ∃ i, diagonalRecoveryDefect a = negativeTrace (diagonalRecovery a (coordinateProjector i)) ∧
      ∀ j, negativeTrace (diagonalRecovery a (coordinateProjector j)) ≤
        diagonalRecoveryDefect a := by
  obtain ⟨i, _, hi⟩ := diagonalRecoveryDefect_isGreatest ha
  have hsup : diagonalRecoveryDefect a = _ := hi.csSup_eq
  refine ⟨i, hsup, fun j => ?_⟩
  rw [hsup]
  exact hi.2 ⟨coordinateProjector j, coordinateProjector_test j, rfl⟩

private theorem diagonalRecoveryDefect_nonneg [Nonempty n] {a : Matrix n n ℂ}
    (ha : a.PosDef) : 0 ≤ diagonalRecoveryDefect a := by
  obtain ⟨i, hi, _⟩ := diagonalRecoveryDefect_eq_max_coordinate ha
  rw [hi, diagonalRecovery_negativeTrace_eq_spectral ha (coordinateProjector_test i)]
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _

private theorem diagonalPart_trace (a : Matrix n n ℂ) : (diagonalPart a).trace = a.trace := by
  simp [diagonalPart, Matrix.trace]

omit [Fintype n] in
private theorem diagonalPart_smul (c : ℝ) (a : Matrix n n ℂ) :
    diagonalPart (c • a) = c • diagonalPart a := by
  rw [diagonalPart, diagonalPart, ← diagonal_smul]
  rfl

/-- The density scaled to have trace equal to the dimension. -/
def normalizedReference (a : Matrix n n ℂ) : Matrix n n ℂ :=
  (Fintype.card n : ℝ) • a

omit [DecidableEq n] in
private theorem card_pos_real [Nonempty n] : (0 : ℝ) < Fintype.card n :=
  Nat.cast_pos.mpr Fintype.card_pos

omit [DecidableEq n] in
private theorem normalizedReference_posDef [Nonempty n] {a : Matrix n n ℂ} (ha : a.PosDef) :
    (normalizedReference a).PosDef :=
  ha.smul card_pos_real

omit [DecidableEq n] in
private theorem normalizedReference_trace {a : Matrix n n ℂ} (ht : a.trace = 1) :
    (normalizedReference a).trace = (Fintype.card n : ℂ) := by
  rw [normalizedReference, trace_smul, ht]
  simp [Complex.real_smul]

private theorem diagonalRecovery_normalizedReference [Nonempty n] {a : Matrix n n ℂ}
    (ha : a.PosDef) (B : Matrix n n ℂ) :
    diagonalRecovery (normalizedReference a) B = diagonalRecovery a B :=
  diagonalRecovery_smul_reference ha card_pos_real B

private theorem diagonalPart_normalizedReference [Nonempty n] (a : Matrix n n ℂ) :
    ((Fintype.card n : ℝ)⁻¹) • diagonalPart (normalizedReference a) = diagonalPart a := by
  rw [normalizedReference, diagonalPart_smul, smul_smul, inv_mul_cancel₀ card_pos_real.ne',
    one_smul]

private theorem coordinate_normalized_negativeTrace_le [Nonempty n] {a : Matrix n n ℂ}
    (ha : a.PosDef) (i : n) :
    spectralNegativeTrace (coordinate_omega_isHermitian (normalizedReference_posDef ha) i) ≤
      diagonalRecoveryDefect a *
        (omega (normalizedReference a) (coordinateProjector i)).trace.re := by
  let hX := normalizedReference_posDef ha
  rw [← coordinate_recovery_negativeTrace hX i, diagonalRecovery_normalizedReference ha,
    coordinate_omega_trace_re hX]
  obtain ⟨_, _, h⟩ := diagonalRecoveryDefect_eq_max_coordinate ha
  exact mul_le_mul_of_nonneg_right (h i) (diag_re_pos hX i).le

/-- Logarithm of the ratio between the largest and smallest eigenvalues. -/
def spectralLogCondition [Nonempty n] {X : Matrix n n ℂ} (hX : X.PosDef) : ℝ :=
  Real.log ((Finset.univ.sup' Finset.univ_nonempty hX.isHermitian.eigenvalues) /
    (Finset.univ.inf' Finset.univ_nonempty hX.isHermitian.eigenvalues))

private theorem eigenvalue_logRatio_le [Nonempty n] {X : Matrix n n ℂ} (hX : X.PosDef) (i j : n) :
    |Real.log (hX.isHermitian.eigenvalues i / hX.isHermitian.eigenvalues j)| ≤
      spectralLogCondition hX := by
  let eigenvalue := hX.isHermitian.eigenvalues
  let lo := Finset.univ.inf' Finset.univ_nonempty eigenvalue
  let hi := Finset.univ.sup' Finset.univ_nonempty eigenvalue
  have hlo : 0 < lo := by
    obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ eigenvalue Finset.univ_nonempty
    exact lt_of_lt_of_le (hX.eigenvalues_pos k) (Finset.le_inf' _ _ hk)
  have hlow (k : n) : lo ≤ eigenvalue k := Finset.inf'_le eigenvalue (Finset.mem_univ k)
  have hhigh (k : n) : eigenvalue k ≤ hi := Finset.le_sup' eigenvalue (Finset.mem_univ k)
  have hhi : 0 < hi := (hX.eigenvalues_pos i).trans_le (hhigh i)
  have hloglow (k : n) : Real.log lo ≤ Real.log (eigenvalue k) := Real.log_le_log hlo (hlow k)
  have hloghigh (k : n) : Real.log (eigenvalue k) ≤ Real.log hi :=
    Real.log_le_log (hX.eigenvalues_pos k) (hhigh k)
  change |Real.log (eigenvalue i / eigenvalue j)| ≤ Real.log (hi / lo)
  rw [Real.log_div (hX.eigenvalues_pos i).ne' (hX.eigenvalues_pos j).ne',
    Real.log_div hhi.ne' hlo.ne']
  exact abs_le.mpr ⟨by linarith [hloglow i, hloghigh j], by linarith [hloghigh i, hloglow j]⟩

/-- Maximal abelian BKM stability in the basis of the diagonal algebra.
The defect is the supremum over all positive semidefinite trace-one diagonal tests and the
conditioning is computed from the trace-dimension normalized reference. -/
theorem actual_maximal_abelian_bkm_stability [Nonempty n] (a : Matrix n n ℂ)
    (ha : a.PosDef) (ht : a.trace = 1) :
    let X := normalizedReference a
    let T := spectralLogCondition (normalizedReference_posDef ha)
    let ε := diagonalRecoveryDefect a
    traceNorm (a - (Fintype.card n : ℝ)⁻¹ • diagonalPart X) ≤
      min 2 (Real.sqrt ((12 + T ^ 2) * ε * (1 + ε))) := by
  dsimp only
  rw [diagonalPart_normalizedReference]
  apply le_min
  · have hdiag : (diagonalPart a).PosSemidef :=
      Matrix.PosSemidef.diagonal fun i => (ha.diag_pos (i := i)).le
    rw [sub_eq_add_neg]
    calc
      _ ≤ traceNorm a + traceNorm (-diagonalPart a) :=
        D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le _ _
      _ = 2 := by
        rw [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg,
          traceNorm_eq_re_trace ha.posSemidef, traceNorm_eq_re_trace hdiag,
          diagonalPart_trace, ht]
        norm_num
  · let X := normalizedReference a
    let hX := normalizedReference_posDef ha
    let T := spectralLogCondition hX
    let ε := diagonalRecoveryDefect a
    have h := omega_diagonal_traceNorm_le hX T ε (eigenvalue_logRatio_le hX)
      (diagonalRecoveryDefect_nonneg ha) (coordinate_normalized_negativeTrace_le ha)
    change traceNorm (X - diagonalPart X) ≤
      Real.sqrt ((12 + T ^ 2) * ε * (1 + ε)) * X.trace.re at h
    rw [show X - diagonalPart X = (Fintype.card n : ℝ) • (a - diagonalPart a) by
        change (Fintype.card n : ℝ) • a - diagonalPart ((Fintype.card n : ℝ) • a) = _
        rw [diagonalPart_smul, smul_sub],
      normalizedReference_trace ht] at h
    change traceNorm (((Fintype.card n : ℝ) : ℂ) • (a - diagonalPart a)) ≤ _ at h
    rw [traceNorm_smul_nonneg _ (Fintype.card n : ℝ) card_pos_real.le, Complex.natCast_re] at h
    rw [mul_comm (Fintype.card n : ℝ) (traceNorm (a - diagonalPart a))] at h
    exact le_of_mul_le_mul_right h (card_pos_real (n := n))

/-- On diagonal density matrices, recovery preserves positive semidefiniteness exactly when
the faithful reference is diagonal. -/
theorem diagonalRecovery_positive_iff [Nonempty n] {a : Matrix n n ℂ}
    (ha : a.PosDef) (ht : a.trace = 1) :
    (∀ B, DiagonalTest B → (diagonalRecovery a B).PosSemidef) ↔ diagonalPart a = a := by
  constructor
  · intro h
    obtain ⟨i, hi, _⟩ := diagonalRecoveryDefect_eq_max_coordinate ha
    have hzero : diagonalRecoveryDefect a = 0 := by
      rw [hi, negativeTrace, traceNorm_eq_re_trace (h _ (coordinateProjector_test i)),
        sub_self, zero_div]
    have hbound := actual_maximal_abelian_bkm_stability a ha ht
    dsimp only at hbound
    rw [diagonalPart_normalizedReference, hzero, mul_zero, zero_mul, Real.sqrt_zero,
      min_eq_right (by norm_num : (0 : ℝ) ≤ 2)] at hbound
    let M := a - diagonalPart a
    have hz : traceNorm M = 0 := le_antisymm hbound
      (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_nonneg M)
    let e := (Fintype.equivFin n).symm
    have hreindex :=
      D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv M e e
    have hM : M.submatrix e e = 0 :=
      ((D5.S3.Quantum.Schatten.TraceNorm.traceNormUINorm (Fintype.card n)).eq_zero_iff _).mp
        (hreindex.trans hz)
    have hMzero : M = 0 := by
      ext j k
      simpa [e] using congrFun (congrFun hM (Fintype.equivFin n j)) (Fintype.equivFin n k)
    exact (sub_eq_zero.mp hMzero).symm
  · intro h B hB
    have hfix : diagonalRecovery a B = B := by
      exact (congrArg (fun A => omega A (diagonalOmegaInverse a B)) h.symm).trans
        (diagonalOmegaInverse_spec ha hB.1).1
    exact hfix.symm ▸ hB.2.1

end DiagonalRecovery

end D5.S3.Quantum.Recovery.BKMDiagonalStability
