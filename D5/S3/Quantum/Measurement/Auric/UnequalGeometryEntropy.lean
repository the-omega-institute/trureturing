/- GID: D5/S3/Quantum/Measurement/Auric/UnequalGeometryEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalGeometryEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Express the actual pinching gain as the spectral score of fiber row effects divided by the input rank. -/

import D5.S3.Quantum.Measurement.Auric.UnequalGeometryFrames
import D5.S3.Quantum.Measurement.Auric.DisjointSpectralSuppliers
import D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

/-! Pinching entropy for a normalized projection on an arbitrary three-fiber partition. -/

namespace D5.S3.Quantum.Measurement.Auric

open _root_.Matrix
open scoped Matrix BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Observer.Conditioning (unreadState)
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (charpoly_conj_unitary density_posSemidef entropy_eq_spectral
    spectral_sum_eq_of_charpoly_prod spectralEntropy)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
  (coordinatePVM pinchingChannel pinchingChannel_apply)
open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects (entropyIntegrand)
open D5.S3.Quantum.Measurement.Auric.EqualBlockProjection (gain)
open D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects (spectralSum)

open D5.S3.Quantum.Measurement.Auric.EqualBlockProjection (spectralSum_reindex spectralSum_scale_entropy entropy_flat_projection)

open GeometryFrames (fiberRows fiberCompression frameProjection fiberCompression_frameProjection)

noncomputable section

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

private theorem coordinate_pinching_eq_blockDiagonal (c : ι → Fin 3) (X : Matrix ι ι ℂ) :
    Matrix.reindex (Equiv.sigmaFiberEquiv c).symm (Equiv.sigmaFiberEquiv c).symm
        (unreadState (coordinatePVM c).proj X) =
      Matrix.blockDiagonal' (fiberCompression c X) := by
  ext x y
  rcases x with ⟨j, a⟩
  rcases y with ⟨k, b⟩
  change (∑ l : Fin 3,
    (Matrix.diagonal (fun i => if c i = l then (1 : ℂ) else 0) * X *
      Matrix.diagonal (fun i => if c i = l then (1 : ℂ) else 0)) a.val b.val) =
    Matrix.blockDiagonal' (fiberCompression c X) ⟨j, a⟩ ⟨k, b⟩
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, a.property, b.property]
  by_cases hjk : j = k
  · subst k
    rw [Matrix.blockDiagonal'_apply_eq, Finset.sum_eq_single j]
    · simp [fiberCompression]
    · intro l _ hlj
      simp [Ne.symm hlj]
    · simp
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hjk]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hjl : j = l
    · have hkl : k ≠ l := fun hkl => hjk (hjl.trans hkl.symm)
      simp [hkl]
    · simp [hjl]

/-- The sum over the dependent block diagonal is the sum over its block spectra. -/
private theorem spectral_sum_blockDiagonal'
    {b : Type*} [Fintype b] [DecidableEq b]
    {m : b → Type*} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (A : ∀ j, Matrix (m j) (m j) ℂ)
    (hA : ∀ j, (A j).IsHermitian) (hBD : (Matrix.blockDiagonal' A).IsHermitian)
    (f : ℝ → ℝ) :
    (∑ i, f (hBD.eigenvalues i)) = ∑ j, ∑ a, f ((hA j).eigenvalues a) := by
  let U (j : b) : Matrix (m j) (m j) ℂ := (hA j).eigenvectorUnitary
  let d (i : Σ j, m j) : ℝ := (hA i.1).eigenvalues i.2
  let D (j : b) : Matrix (m j) (m j) ℂ :=
    Matrix.diagonal (fun a => (RCLike.ofReal (d ⟨j, a⟩) : ℂ))
  let W := Matrix.blockDiagonal' U
  have hUnitary (j : b) : (U j)ᴴ * U j = 1 := by
    exact Unitary.coe_star_mul_self (hA j).eigenvectorUnitary
  have hW : star W * W = 1 := by
    rw [Matrix.star_eq_conjTranspose]
    change (Matrix.blockDiagonal' U)ᴴ * Matrix.blockDiagonal' U = _
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    rw [show (fun j => (U j)ᴴ * U j) = (1 : ∀ j, Matrix (m j) (m j) ℂ)
      from funext hUnitary, Matrix.blockDiagonal'_one]
  have hDiagonal (j : b) : A j = U j * D j * (U j)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U, D, d,
      Function.comp_def] using
      (hA j).spectral_theorem
  have hConjugate : Matrix.blockDiagonal' A =
      W * Matrix.diagonal (fun i => (RCLike.ofReal (d i) : ℂ)) * star W := by
    calc
      _ = Matrix.blockDiagonal' (fun j => U j * D j * (U j)ᴴ) :=
        congrArg (fun B : ∀ j, Matrix (m j) (m j) ℂ => Matrix.blockDiagonal' B)
          (funext hDiagonal)
      _ = Matrix.blockDiagonal' U * Matrix.blockDiagonal' D * (Matrix.blockDiagonal' U)ᴴ := by
        rw [Matrix.blockDiagonal'_mul (fun j => U j * D j) (fun j => (U j)ᴴ),
          Matrix.blockDiagonal'_mul U D, Matrix.blockDiagonal'_conjTranspose U]
      _ = _ := by simp only [D, W, Matrix.blockDiagonal'_diagonal, Matrix.star_eq_conjTranspose]
  have hChar : (Matrix.blockDiagonal' A).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((RCLike.ofReal (d i)) : ℂ)) := by
    rw [hConjugate, charpoly_conj_unitary hW, Matrix.charpoly_diagonal]
  calc
    _ = ∑ i, f (d i) := spectral_sum_eq_of_charpoly_prod hBD d f hChar
    _ = _ := by simp only [Fintype.sum_sigma, d]

private theorem spectralEntropy_congr {X Y : Matrix ι ι ℂ} (h : X = Y)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    spectralEntropy hX = spectralEntropy hY := by
  subst Y
  rfl

private theorem unreadState_of_projection_isHermitian (c : ι → Fin 3) {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hP₂ : P * P = P) :
    (unreadState (coordinatePVM c).proj P).IsHermitian := by
  have hPos : P.PosSemidef := by
    simpa only [hP.eq, hP₂] using Matrix.posSemidef_conjTranspose_mul_self P
  apply Matrix.PosSemidef.isHermitian
  unfold unreadState
  refine Matrix.posSemidef_sum _ fun j _ => ?_
  have hJ := (coordinatePVM c).hermitian j
  simpa only [hJ.eq] using hPos.mul_mul_conjTranspose_same ((coordinatePVM c).proj j)

/-- The trace term introduced by entropy scaling cancels across the actual channel. -/
private theorem gain_eq_unscaled_pinching (c : ι → Fin 3) {r : ℕ} (hr : 0 < r)
    (ρ : DensityState ι) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hP₂ : P * P = P)
    (hρ : CStarMatrix.ofMatrix.symm ρ.1 = ((r : ℂ)⁻¹) • P)
    (hU : (unreadState (coordinatePVM c).proj P).IsHermitian) :
    gain c ρ = spectralEntropy hU / (r : ℝ) := by
  let Ψ := pinchingChannel (coordinatePVM c)
  let U := unreadState (coordinatePVM c).proj P
  let s : ℝ := (r : ℝ)⁻¹
  have hInput : CStarMatrix.ofMatrix.symm ρ.1 = (s : ℂ) • P := by
    simpa [s] using hρ
  have hOutput : CStarMatrix.ofMatrix.symm (Ψ.mapState ρ).1 = (s : ℂ) • U := by
    change CStarMatrix.ofMatrix.symm (Ψ.toCompletelyPositiveMap ρ.1) = _
    rw [← CStarMatrix.ofMatrix.apply_symm_apply ρ.1, hInput, pinchingChannel_apply]
    simp only [unreadState, U, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  have hTrace : U.trace = P.trace := by
    have h := Ψ.trace_preserving ρ.1
    change Matrix.trace (CStarMatrix.ofMatrix.symm (Ψ.mapState ρ).1) =
      Matrix.trace (CStarMatrix.ofMatrix.symm ρ.1) at h
    rw [hOutput, hInput, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul] at h
    exact mul_left_cancel₀ (by simp [s, hr.ne']) h
  have hScaledP : ((s : ℂ) • P).IsHermitian :=
    hInput ▸ (density_posSemidef ρ).isHermitian
  have hScaledU : ((s : ℂ) • U).IsHermitian :=
    hOutput ▸ (density_posSemidef (Ψ.mapState ρ)).isHermitian
  have hPre : spectralEntropy hScaledP =
      s * spectralEntropy hP + P.trace.re * Real.negMulLog s :=
    spectralSum_scale_entropy hP s hScaledP
  have hPost : spectralEntropy hScaledU =
      s * spectralEntropy hU + U.trace.re * Real.negMulLog s :=
    spectralSum_scale_entropy hU s hScaledU
  have hProjection : spectralEntropy hP = 0 := entropy_flat_projection hP hP₂
  change vonNeumannEntropy (Ψ.mapState ρ) - vonNeumannEntropy ρ = _
  rw [entropy_eq_spectral (Ψ.mapState ρ), entropy_eq_spectral ρ,
    spectralEntropy_congr hOutput (density_posSemidef (Ψ.mapState ρ)).isHermitian hScaledU,
    spectralEntropy_congr hInput (density_posSemidef ρ).isHermitian hScaledP,
    hPost, hPre, hProjection, hTrace]
  simp only [mul_zero, zero_add, add_sub_cancel_right, div_eq_mul_inv, s, mul_comm]

private theorem spectral_entropy_coordinate_pinching (c : ι → Fin 3) {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (hU : (unreadState (coordinatePVM c).proj P).IsHermitian) :
    spectralEntropy hU = ∑ j : Fin 3, spectralEntropy
      (hP.submatrix (fun a : {a : ι // c a = j} => a.val)) := by
  let U := unreadState (coordinatePVM c).proj P
  let E := Equiv.sigmaFiberEquiv c
  let B := fiberCompression c P
  have hB (j : Fin 3) : (B j).IsHermitian := hP.submatrix _
  have hBD : (Matrix.blockDiagonal' B).IsHermitian :=
    Matrix.isHermitian_blockDiagonal'_iff.mpr hB
  have heq : Matrix.reindex E.symm E.symm U = Matrix.blockDiagonal' B :=
    coordinate_pinching_eq_blockDiagonal c P
  have hRe : (Matrix.reindex E.symm E.symm U).IsHermitian := heq.symm ▸ hBD
  calc
    _ = spectralEntropy hRe := (spectralSum_reindex E.symm Real.negMulLog hU hRe).symm
    _ = spectralEntropy hBD := spectralEntropy_congr heq hRe hBD
    _ = _ := spectral_sum_blockDiagonal' B hB hBD Real.negMulLog

private theorem compression_spectral_entropy_eq_gram (c : ι → Fin 3) (flip : Bool)
    (V : Matrix ι n ℂ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (hFrame : P = if flip then 1 - V * Vᴴ else V * Vᴴ) (j : Fin 3) :
    spectralEntropy (hP.submatrix (fun a : {a : ι // c a = j} => a.val)) =
      ∑ i, entropyIntegrand flip
        ((Matrix.isHermitian_conjTranspose_mul_self (fiberRows c V j)).eigenvalues i) := by
  let W := fiberRows c V j
  have hRow : (W * Wᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self W
  have hCol : (Wᴴ * W).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self W).isHermitian
  have hB : (fiberCompression c P j).IsHermitian := hP.submatrix _
  have hBlock : fiberCompression c P j = if flip then 1 - W * Wᴴ else W * Wᴴ := by
    rw [show P = frameProjection flip V from hFrame]
    exact fiberCompression_frameProjection c flip V j
  have hZero : entropyIntegrand flip 0 = 0 := by
    cases flip <;> simp [entropyIntegrand]
  change spectralEntropy hB = ∑ i, entropyIntegrand flip (hCol.eigenvalues i)
  calc
    _ = ∑ i, entropyIntegrand flip (hRow.eigenvalues i) := by
      cases flip
      · exact spectralEntropy_congr hBlock hB hRow
      · have hComp : (1 - W * Wᴴ).IsHermitian := Matrix.isHermitian_one.sub hRow
        exact (spectralEntropy_congr hBlock hB hComp).trans
          (spectral_sum_one_sub Real.negMulLog hRow hComp)
    _ = _ := spectralSum_mul_reverse (entropyIntegrand flip) hZero W Wᴴ hRow hCol

/-- Actual pinching gain of a normalized projection, in direct or corank coordinates.
The normalizer is the rank of the input projection in either branch. The outcome
fibers are arbitrary and the working column type may be empty. -/
theorem gain_eq_unequal_rowEffects (c : ι → Fin 3) (flip : Bool) {r : ℕ} (hr : 0 < r)
    (ρ : DensityState ι) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) (hP₂ : P * P = P)
    (hρ : CStarMatrix.ofMatrix.symm ρ.1 = ((r : ℂ)⁻¹) • P)
    (V : Matrix ι n ℂ) (hFrame : P = if flip then 1 - V * Vᴴ else V * Vᴴ) :
    gain c ρ = spectralSum (entropyIntegrand flip)
      (fun j => (fiberRows c V j)ᴴ * fiberRows c V j)
      (fun j => Matrix.posSemidef_conjTranspose_mul_self (fiberRows c V j)) / (r : ℝ) := by
  have hU := unreadState_of_projection_isHermitian c hP hP₂
  rw [gain_eq_unscaled_pinching c hr ρ hP hP₂ hρ hU]
  apply congrArg (fun score : ℝ => score / (r : ℝ))
  rw [spectral_entropy_coordinate_pinching c hP hU]
  unfold spectralSum
  exact Finset.sum_congr rfl fun j _ => compression_spectral_entropy_eq_gram c flip V hP hFrame j

end

end D5.S3.Quantum.Measurement.Auric
