import D5.S3.Quantum.Recovery.PetzStinespringCompression
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-!
# Isometric invariants and retained support compression for Petz recovery

The trace-log identities use the totalized real logarithm. The retained
carrier consists of the strictly positive spectral indices of the reference
marginal, with one index for each eigenvector in the chosen eigenbasis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w z

namespace PetzSupportCompressionInvariants

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker Matrix MatrixOrder
open PetzStinespringCompression
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy (finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport)
open D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
  (coordinateEmbedding coordinateEmbedding_isometry)

section IsometricEmbedding

variable {a : Type u} {m : Type v} [Fintype a] [DecidableEq a] [Fintype m] [DecidableEq m]

theorem trace_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix a a ℂ) : (V * X * Vᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_comm (V * X) Vᴴ, ← Matrix.mul_assoc, hV, Matrix.one_mul]

private theorem isometric_embed_mul (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix a a ℂ) :
    (V * X * Vᴴ) * (V * Y * Vᴴ) = V * (X * Y) * Vᴴ := by
  calc
    _ = (V * X) * (Vᴴ * V) * Y * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V X Y]

private theorem cfc_isometric_embed_of_zero (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix a a ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) (hf : f 0 = 0) :
    cfc f (V * X * Vᴴ) = V * cfc f X * Vᴴ := by
  simpa only [hf, zero_smul, add_zero] using cfc_isometric_embed V hV hX f

/-- The mixed trace-log pairing uses the ordinary complex trace. -/
theorem trace_mul_log_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    (R : Matrix a a ℂ) {S : Matrix a a ℂ} (hS : S.IsHermitian) :
    ((V * R * Vᴴ) * cfc Real.log (V * S * Vᴴ)).trace = (R * cfc Real.log S).trace := by
  rw [cfc_isometric_embed_of_zero V hV hS Real.log Real.log_zero,
    isometric_embed_mul V hV, trace_isometric_embed V hV]

/-- The raw finite trace-log expression is invariant, including at singular inputs. -/
theorem raw_traceLog_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {R S : Matrix a a ℂ} (hR : R.IsHermitian) (hS : S.IsHermitian) :
    ((V * R * Vᴴ) * (cfc Real.log (V * R * Vᴴ) - cfc Real.log (V * S * Vᴴ))).trace.re =
      (R * (cfc Real.log R - cfc Real.log S)).trace.re := by
  simp only [Matrix.mul_sub, Matrix.trace_sub,
    trace_mul_log_isometric_embed V hV R hR, trace_mul_log_isometric_embed V hV R hS]

/-- A rectangular isometry sends a density state to a density state. -/
def embedDensityState (V : Matrix m a ℂ) (hV : Vᴴ * V = 1) (ρ : DensityState a) :
    DensityState m := by
  let R := CStarMatrix.ofMatrix.symm ρ.1
  refine ⟨CStarMatrix.ofMatrix (V * R * Vᴴ), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef ρ).mul_mul_conjTranspose_same V).nonneg
  · exact (trace_isometric_embed V hV R).trans ρ.2.2

private theorem map_cfc_log (R : Matrix a a ℂ) (hR : R.IsHermitian) :
    CStarMatrix.ofMatrix (cfc Real.log R) = CFC.log (CStarMatrix.ofMatrix R) :=
  StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log R
    (R.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
    hR.isSelfAdjoint hR.isSelfAdjoint

/-- Isometric invariance for the library's finite trace-log branch on density states. -/
theorem finiteTraceLogRelativeEntropy_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    (ρ σ : DensityState a) :
    finiteTraceLogRelativeEntropy (embedDensityState V hV ρ) (embedDensityState V hV σ) =
      finiteTraceLogRelativeEntropy ρ σ := by
  let R := CStarMatrix.ofMatrix.symm ρ.1
  let S := CStarMatrix.ofMatrix.symm σ.1
  have hR : R.IsHermitian := (density_posSemidef ρ).isHermitian
  have hS : S.IsHermitian := (density_posSemidef σ).isHermitian
  unfold finiteTraceLogRelativeEntropy
  change ((CStarMatrix.ofMatrix (V * R * Vᴴ)) *
      (CFC.log (CStarMatrix.ofMatrix (V * R * Vᴴ)) -
        CFC.log (CStarMatrix.ofMatrix (V * S * Vᴴ)))).trace.re =
    ((CStarMatrix.ofMatrix R) *
      (CFC.log (CStarMatrix.ofMatrix R) - CFC.log (CStarMatrix.ofMatrix S))).trace.re
  rw [← map_cfc_log _ (Matrix.isHermitian_mul_mul_conjTranspose V hR),
    ← map_cfc_log _ (Matrix.isHermitian_mul_mul_conjTranspose V hS),
    ← map_cfc_log R hR, ← map_cfc_log S hS]
  exact raw_traceLog_isometric_embed V hV hR hS

private theorem sqrt_eq_cfc_real {X : Matrix a a ℂ} (hX : X.PosSemidef) :
    CFC.sqrt X = cfc Real.sqrt X := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ hX.nonneg]
  apply cfc_congr
  intro x hx
  change (NNReal.sqrt x.toNNReal : ℝ) = Real.sqrt x
  rw [Real.coe_sqrt, Real.coe_toNNReal x (spectrum_nonneg_of_nonneg hX.nonneg hx)]

private theorem sqrt_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix a a ℂ} (hX : X.PosSemidef) :
    CFC.sqrt (V * X * Vᴴ) = V * CFC.sqrt X * Vᴴ := by
  rw [sqrt_eq_cfc_real (hX.mul_mul_conjTranspose_same V), sqrt_eq_cfc_real hX]
  exact cfc_isometric_embed_of_zero V hV hX.isHermitian Real.sqrt Real.sqrt_zero

variable {b : Type w} {n : Type z} [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]

private theorem gram_two_isometries (A : Matrix a b ℂ) (V : Matrix m a ℂ)
    (W : Matrix n b ℂ) (hV : Vᴴ * V = 1) :
    (V * A * Wᴴ)ᴴ * (V * A * Wᴴ) = W * (Aᴴ * A) * Wᴴ := by
  calc
    _ = (W * Aᴴ) * (Vᴴ * V) * A * Wᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc W Aᴴ A]

/-- The native rectangular trace norm uses the unnormalized trace of the Gram square root. -/
theorem traceNorm_two_isometries (A : Matrix a b ℂ) (V : Matrix m a ℂ)
    (W : Matrix n b ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (V * A * Wᴴ) =
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm A := by
  unfold D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
  rw [gram_two_isometries A V W hV,
    sqrt_isometric_embed W hW (Matrix.posSemidef_conjTranspose_mul_self A),
    trace_isometric_embed W hW]

theorem traceNorm_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix a a ℂ) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (V * A * Vᴴ) =
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm A :=
  traceNorm_two_isometries A V V hV hV

open scoped Matrix.Norms.Frobenius in
private theorem frobenius_sq_eq_trace (A : Matrix a b ℂ) :
    ((‖A‖ ^ 2 : ℝ) : ℂ) = (Aᴴ * A).trace := by
  have hNorm : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (A i))‖ ^ 2 = _
    simp [PiLp.norm_sq_eq_of_L2]
  rw [hNorm, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_pow, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']
  rw [Finset.sum_comm]

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_two_isometries (A : Matrix a b ℂ) (V : Matrix m a ℂ)
    (W : Matrix n b ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    ‖V * A * Wᴴ‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact Complex.ofReal_injective (by
    rw [frobenius_sq_eq_trace, frobenius_sq_eq_trace, gram_two_isometries A V W hV,
      trace_isometric_embed W hW])

end IsometricEmbedding

section Compression

variable {b : Type u} {s : Type v} [Fintype b] [DecidableEq b] [Fintype s] [DecidableEq s]

theorem compress_isometric_embed (U : Matrix b s ℂ) (hU : Uᴴ * U = 1)
    (Y : Matrix s s ℂ) : Uᴴ * (U * Y * Uᴴ) * U = Y := by
  calc
    _ = (Uᴴ * U) * Y * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]

/-- Exact reconstruction from the compression of a matrix in the range corner. -/
theorem isometric_embed_compress (U : Matrix b s ℂ) {X : Matrix b b ℂ}
    (hLeft : (U * Uᴴ) * X = X) (hRight : X * (U * Uᴴ) = X) :
    U * (Uᴴ * X * U) * Uᴴ = X := by
  calc
    _ = (U * Uᴴ) * X * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hLeft, hRight]

private theorem mul_projection_of_projection_mul (U : Matrix b s ℂ)
    {X : Matrix b b ℂ} (hX : X.IsHermitian) (h : (U * Uᴴ) * X = X) :
    X * (U * Uᴴ) = X := by
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX.eq] using
    congrArg Matrix.conjTranspose h

/-- One coordinate for each strictly positive eigenvalue, counted with multiplicity. -/
abbrev PositiveSpectralIndex {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :=
  {i : b // 0 < hQ.isHermitian.eigenvalues i}

theorem card_positiveSpectralIndex_eq_rank {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    Fintype.card (PositiveSpectralIndex hQ) = Q.rank := by
  calc
    _ = Fintype.card {i : b // hQ.isHermitian.eigenvalues i ≠ 0} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
        ⟨ne_of_gt, fun hi => lt_of_le_of_ne (hQ.eigenvalues_nonneg i) hi.symm⟩)
    _ = _ := hQ.isHermitian.rank_eq_card_non_zero_eigs.symm

/-- The positive eigenvectors, as an isometry into the original carrier. -/
def spectralInclusion {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    Matrix b (PositiveSpectralIndex hQ) ℂ :=
  (↑hQ.isHermitian.eigenvectorUnitary : Matrix b b ℂ) *
    coordinateEmbedding (Function.Embedding.subtype _)

private theorem eigenvectorUnitary_isometry {Q : Matrix b b ℂ} (hQ : Q.IsHermitian) :
    (hQ.eigenvectorUnitary : Matrix b b ℂ)ᴴ * (hQ.eigenvectorUnitary : Matrix b b ℂ) = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    Unitary.star_mul_self_of_mem hQ.eigenvectorUnitary.property

theorem spectralInclusion_isometry {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    (spectralInclusion hQ)ᴴ * spectralInclusion hQ = 1 := by
  let U : Matrix b b ℂ := hQ.isHermitian.eigenvectorUnitary
  let J : Matrix b (PositiveSpectralIndex hQ) ℂ :=
    coordinateEmbedding (Function.Embedding.subtype _)
  change (U * J)ᴴ * (U * J) = 1
  calc
    _ = Jᴴ * (Uᴴ * U) * J := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by
      rw [show Uᴴ * U = 1 from eigenvectorUnitary_isometry hQ.isHermitian, Matrix.mul_one]
      exact coordinateEmbedding_isometry _

private theorem subtype_embed_diagonal (p : b → Prop) [DecidablePred p]
    (d : b → ℂ) (hd : ∀ i, ¬ p i → d i = 0) :
    let J := coordinateEmbedding (Function.Embedding.subtype p)
    J * Matrix.diagonal (fun i : {j // p j} => d i.1) * Jᴴ = Matrix.diagonal d := by
  classical
  dsimp only
  ext i j : 1
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, coordinateEmbedding, Function.Embedding.coe_subtype]
  by_cases hi : p i
  · let ii : {k // p k} := ⟨i, hi⟩
    rw [Finset.sum_eq_single ii]
    · by_cases hij : i = j
      · subst j
        simp [ii]
      · simp [ii, hij, Ne.symm hij]
    · intro k _ hk
      have hki : i ≠ k.1 := fun h => hk (Subtype.ext h.symm)
      simp [hki]
    · simp
  · have hnone (k : {j // p j}) : i ≠ k.1 := fun h => hi (h.symm ▸ k.2)
    simp [hnone, hd i hi]

theorem spectralInclusion_mul_adjoint {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    spectralInclusion hQ * (spectralInclusion hQ)ᴴ = spectralSupport Q := by
  let U : Matrix b b ℂ := hQ.isHermitian.eigenvectorUnitary
  let J : Matrix b (PositiveSpectralIndex hQ) ℂ :=
    coordinateEmbedding (Function.Embedding.subtype _)
  let d : b → ℂ := fun i => if hQ.isHermitian.eigenvalues i = 0 then 0 else 1
  have hd (i : b) (hi : ¬ 0 < hQ.isHermitian.eigenvalues i) : d i = 0 := by
    have he := le_antisymm (le_of_not_gt hi) (hQ.eigenvalues_nonneg i)
    simp [d, he]
  have hdiag : Matrix.diagonal (fun i : PositiveSpectralIndex hQ => d i.1) = 1 := by
    have hEntries : (fun i : PositiveSpectralIndex hQ => d i.1) = fun _ => 1 :=
      funext fun i => if_neg (ne_of_gt i.2)
    rw [hEntries, Matrix.diagonal_one]
  have hJ : J * Jᴴ = Matrix.diagonal d := by
    have h := subtype_embed_diagonal (fun i => 0 < hQ.isHermitian.eigenvalues i) d hd
    change J * Matrix.diagonal (fun i : PositiveSpectralIndex hQ => d i.1) * Jᴴ = _ at h
    simpa only [hdiag, Matrix.mul_one] using h
  have hP : spectralSupport Q = U * Matrix.diagonal d * Uᴴ := by
    unfold spectralSupport
    rw [hQ.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp only [U, d, Function.comp_def, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, apply_ite, Complex.ofReal_zero, Complex.ofReal_one]
  change (U * J) * (U * J)ᴴ = spectralSupport Q
  calc
    _ = U * (J * Jᴴ) * Uᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hJ, ← hP]

theorem card_positiveSpectralIndex_eq_support_rank {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    Fintype.card (PositiveSpectralIndex hQ) = (spectralSupport Q).rank := by
  let U := spectralInclusion hQ
  calc
    _ = (1 : Matrix (PositiveSpectralIndex hQ) (PositiveSpectralIndex hQ) ℂ).rank :=
      Matrix.rank_one.symm
    _ = (Uᴴ * U).rank := congrArg Matrix.rank (spectralInclusion_isometry hQ).symm
    _ = U.rank := Matrix.rank_conjTranspose_mul_self U
    _ = (U * Uᴴ).rank := (Matrix.rank_self_mul_conjTranspose U).symm
    _ = _ := congrArg Matrix.rank (spectralInclusion_mul_adjoint hQ)

theorem card_positiveSpectralIndex_eq_support_finrank {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    Fintype.card (PositiveSpectralIndex hQ) =
      Module.finrank ℂ (LinearMap.range (spectralSupport Q).mulVecLin) :=
  card_positiveSpectralIndex_eq_support_rank hQ

/-- Compression to the positive spectral indices is the positive diagonal of eigenvalues. -/
theorem spectralCompression_eq_diagonal {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    (spectralInclusion hQ)ᴴ * Q * spectralInclusion hQ =
      Matrix.diagonal (fun i : PositiveSpectralIndex hQ => (hQ.isHermitian.eigenvalues i.1 : ℂ)) := by
  let U : Matrix b b ℂ := hQ.isHermitian.eigenvectorUnitary
  let J : Matrix b (PositiveSpectralIndex hQ) ℂ :=
    coordinateEmbedding (Function.Embedding.subtype _)
  let d : b → ℂ := fun i => hQ.isHermitian.eigenvalues i
  let D := Matrix.diagonal (fun i : PositiveSpectralIndex hQ => d i.1)
  have hd (i : b) (hi : ¬ 0 < hQ.isHermitian.eigenvalues i) : d i = 0 := by
    have he := le_antisymm (le_of_not_gt hi) (hQ.eigenvalues_nonneg i)
    simp [d, he]
  have hJ : J * D * Jᴴ = Matrix.diagonal d :=
    subtype_embed_diagonal (fun i => 0 < hQ.isHermitian.eigenvalues i) d hd
  have hQ' : Q = U * Matrix.diagonal d * Uᴴ := by
    simpa only [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      hQ.isHermitian.spectral_theorem
  have hEmbed : Q = spectralInclusion hQ * D * (spectralInclusion hQ)ᴴ := by
    calc
      Q = U * (J * D * Jᴴ) * Uᴴ := by rw [hJ]; exact hQ'
      _ = _ := by
        change U * (J * D * Jᴴ) * Uᴴ = (U * J) * D * (U * J)ᴴ
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc
    _ = (spectralInclusion hQ)ᴴ *
        (spectralInclusion hQ * D * (spectralInclusion hQ)ᴴ) * spectralInclusion hQ :=
      congrArg (fun X => (spectralInclusion hQ)ᴴ * X * spectralInclusion hQ) hEmbed
    _ = _ := compress_isometric_embed _ (spectralInclusion_isometry hQ) D

theorem spectralCompression_posDef {Q : Matrix b b ℂ} (hQ : Q.PosSemidef) :
    ((spectralInclusion hQ)ᴴ * Q * spectralInclusion hQ).PosDef := by
  rw [spectralCompression_eq_diagonal hQ]
  exact Matrix.PosDef.diagonal fun (i : PositiveSpectralIndex hQ) =>
    Complex.zero_lt_real.mpr i.2

end Compression

section PartialTrace

variable {b : Type u} {s : Type v} {e : Type w}
  [Fintype b] [DecidableEq b]
  [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

private def partialTraceRightRect {r : Type u} {t : Type v} (Z : Matrix (r × e) (t × e) ℂ) :
    Matrix r t ℂ :=
  fun i j => ∑ k : e, Z (i, k) (j, k)

private theorem partialTraceRight_mul_retained {c : Type*}
    (Z : Matrix (b × e) (s × e) ℂ) (T : Matrix s c ℂ) :
    partialTraceRightRect (Z * (T ⊗ₖ (1 : Matrix e e ℂ))) =
      (partialTraceRightRect Z : Matrix b s ℂ) * T := by
  ext i j : 1
  simp only [partialTraceRightRect, Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

private theorem partialTraceRight_retained_mul {c : Type*}
    (T : Matrix b s ℂ) (Z : Matrix (s × e) (c × e) ℂ) :
    partialTraceRightRect ((T ⊗ₖ (1 : Matrix e e ℂ)) * Z) =
      T * (partialTraceRightRect Z : Matrix s c ℂ) := by
  ext i j : 1
  simp only [partialTraceRightRect, Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- The right partial trace commutes with the lift of every rectangular sandwich. -/
theorem partialTraceRight_retained_sandwich (U : Matrix b s ℂ) (Z : Matrix (s × e) (s × e) ℂ) :
    partialTraceRight ((U ⊗ₖ (1 : Matrix e e ℂ)) * Z * (U ⊗ₖ (1 : Matrix e e ℂ))ᴴ) =
      U * partialTraceRight Z * Uᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  change partialTraceRightRect ((U ⊗ₖ (1 : Matrix e e ℂ)) * Z *
    (Uᴴ ⊗ₖ (1 : Matrix e e ℂ))) = U * (partialTraceRightRect Z : Matrix s s ℂ) * Uᴴ
  rw [partialTraceRight_mul_retained (c := b), partialTraceRight_retained_mul (c := s)]

/-- The actual right marginal of the compressed joint matrix is the compressed marginal. -/
theorem partialTraceRight_compress (U : Matrix b s ℂ) (Z : Matrix (b × e) (b × e) ℂ) :
    partialTraceRight ((U ⊗ₖ (1 : Matrix e e ℂ))ᴴ * Z * (U ⊗ₖ (1 : Matrix e e ℂ))) =
      Uᴴ * partialTraceRight Z * U := by
  simpa only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose] using partialTraceRight_retained_sandwich Uᴴ Z

theorem retained_lift_isometry (U : Matrix b s ℂ) (hU : Uᴴ * U = 1) :
    (U ⊗ₖ (1 : Matrix e e ℂ))ᴴ * (U ⊗ₖ (1 : Matrix e e ℂ)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    hU, Matrix.one_mul, Matrix.one_kronecker_one]

/-- Lifting a retained density state commutes with the actual density-state marginal. -/
theorem marginalRight_embedDensityState (U : Matrix b s ℂ) (hU : Uᴴ * U = 1)
    (ρ : DensityState (s × e)) :
    marginalRight (embedDensityState (U ⊗ₖ (1 : Matrix e e ℂ)) (retained_lift_isometry U hU) ρ) =
      embedDensityState U hU (marginalRight ρ) := by
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix
    (partialTraceRight_retained_sandwich U (CStarMatrix.ofMatrix.symm ρ.1))

private theorem retained_lift_mul_adjoint (U : Matrix b s ℂ) :
    (U ⊗ₖ (1 : Matrix e e ℂ)) * (U ⊗ₖ (1 : Matrix e e ℂ))ᴴ =
      (U * Uᴴ) ⊗ₖ (1 : Matrix e e ℂ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]

/-- The partial-trace constraint on supported matrices is equivalent after compression. -/
theorem partialTraceRight_compress_eq_iff (U : Matrix b s ℂ)
    {Z : Matrix (b × e) (b × e) ℂ} {p : Matrix b b ℂ}
    (hZ : IsHermitian Z) (hp : IsHermitian p)
    (hZsupport : ((U ⊗ₖ (1 : Matrix e e ℂ)) * (U ⊗ₖ (1 : Matrix e e ℂ))ᴴ) * Z = Z)
    (hpsupport : (U * Uᴴ) * p = p) :
    partialTraceRight ((U ⊗ₖ (1 : Matrix e e ℂ))ᴴ * Z * (U ⊗ₖ (1 : Matrix e e ℂ))) =
      Uᴴ * p * U ↔ partialTraceRight Z = p := by
  let L := U ⊗ₖ (1 : Matrix e e ℂ)
  constructor
  · intro h
    have hZ' : L * (Lᴴ * Z * L) * Lᴴ = Z :=
      isometric_embed_compress L hZsupport (mul_projection_of_projection_mul L hZ hZsupport)
    have hp' : U * (Uᴴ * p * U) * Uᴴ = p :=
      isometric_embed_compress U hpsupport (mul_projection_of_projection_mul U hp hpsupport)
    calc
      partialTraceRight Z = U * partialTraceRight (Lᴴ * Z * L) * Uᴴ :=
        (congrArg partialTraceRight hZ').symm.trans
          (partialTraceRight_retained_sandwich U (Lᴴ * Z * L))
      _ = p := by rw [show partialTraceRight (Lᴴ * Z * L) = Uᴴ * p * U from h, hp']
  · intro h
    rw [partialTraceRight_compress U Z, h]

end PartialTrace

section Stinespring

variable {a b e : Type u}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype e] [DecidableEq e]

/-- The joint reference and every Hermitian input in its support corner reconstruct exactly. -/
theorem stinespring_support_compression
    (V : Matrix (b × e) a ℂ) {σ X : Matrix a a ℂ} (hσ : σ.PosSemidef)
    (hX : X.IsHermitian) (hPX : spectralSupport σ * X = X) :
    let q := partialTraceRight (V * σ * Vᴴ)
    let hq : q.PosSemidef := partialTraceRight_posSemidef (hσ.mul_mul_conjTranspose_same V)
    let U := spectralInclusion hq
    let L := U ⊗ₖ (1 : Matrix e e ℂ)
    L * (Lᴴ * (V * X * Vᴴ) * L) * Lᴴ = V * X * Vᴴ := by
  dsimp only
  let q := partialTraceRight (V * σ * Vᴴ)
  let hq := partialTraceRight_posSemidef (hσ.mul_mul_conjTranspose_same V)
  let U := spectralInclusion hq
  let L := U ⊗ₖ (1 : Matrix e e ℂ)
  have hL : L * Lᴴ = spectralSupport q ⊗ₖ (1 : Matrix e e ℂ) :=
    (retained_lift_mul_adjoint U).trans
      (congrArg (fun P => P ⊗ₖ (1 : Matrix e e ℂ)) (spectralInclusion_mul_adjoint hq))
  have hRange : (L * Lᴴ) * (V * spectralSupport σ) = V * spectralSupport σ := by
    rw [hL]
    exact range_support_le_marginal_support (b := b) (e := e) V hσ
  have hLeft : (L * Lᴴ) * (V * X * Vᴴ) = V * X * Vᴴ := by
    calc
      _ = (L * Lᴴ) * (V * (spectralSupport σ * X) * Vᴴ) := by rw [hPX]
      _ = (L * Lᴴ) * (V * spectralSupport σ) * X * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRange, Matrix.mul_assoc V (spectralSupport σ) X, hPX]
  exact isometric_embed_compress L hLeft
    (mul_projection_of_projection_mul L (Matrix.isHermitian_mul_mul_conjTranspose V hX) hLeft)

/-- On the retained carrier the actual joint reference has a positive definite marginal.
Embedding the compressed joint matrix recovers the original joint reference. -/
theorem faithful_retained_marginal
    (V : Matrix (b × e) a ℂ) {σ : Matrix a a ℂ} (hσ : σ.PosSemidef) :
    let Y := V * σ * Vᴴ
    let q := partialTraceRight Y
    let hq : q.PosSemidef := partialTraceRight_posSemidef (hσ.mul_mul_conjTranspose_same V)
    let U := spectralInclusion hq
    let L := U ⊗ₖ (1 : Matrix e e ℂ)
    let Y' := Lᴴ * Y * L
    Y'.PosSemidef ∧ partialTraceRight Y' = Uᴴ * q * U ∧
      (partialTraceRight Y').PosDef ∧ L * Y' * Lᴴ = Y ∧
      U * partialTraceRight Y' * Uᴴ = q ∧ (partialTraceRight Y').trace = q.trace := by
  dsimp only
  let Y := V * σ * Vᴴ
  let q := partialTraceRight Y
  let hq := partialTraceRight_posSemidef (hσ.mul_mul_conjTranspose_same V)
  let U := spectralInclusion hq
  let L := U ⊗ₖ (1 : Matrix e e ℂ)
  let Y' := Lᴴ * Y * L
  have hMarginal : partialTraceRight Y' = Uᴴ * q * U := partialTraceRight_compress U Y
  have hFaithful : (partialTraceRight Y').PosDef := by
    rw [hMarginal]
    exact spectralCompression_posDef hq
  have hNorm := spectral_sqrt_normalization σ hσ
  dsimp only at hNorm
  obtain ⟨_, _, _, _, _, _, hPσ, _⟩ := hNorm
  have hEmbed : L * Y' * Lᴴ = Y :=
    stinespring_support_compression V hσ hσ.isHermitian hPσ
  have hLift : U * partialTraceRight Y' * Uᴴ = q :=
    (partialTraceRight_retained_sandwich U Y').symm.trans (congrArg partialTraceRight hEmbed)
  have hTrace : (partialTraceRight Y').trace = q.trace :=
    (trace_isometric_embed U (spectralInclusion_isometry hq) (partialTraceRight Y')).symm.trans
      (congrArg Matrix.trace hLift)
  exact ⟨(hσ.mul_mul_conjTranspose_same V).conjTranspose_mul_mul_same L, hMarginal,
    hFaithful, hEmbed, hLift, hTrace⟩

/-- A faithful input reference permits the entire dilation to be compressed.
The new dilation realizes the compressed action of the actual channel on every input. -/
theorem faithful_retained_stinespring
    (Φ : QuantumChannel a b) (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) = act Φ X)
    {σ : Matrix a a ℂ} (hσ : σ.PosDef) :
    let q := partialTraceRight (V * σ * Vᴴ)
    let hq : q.PosSemidef := partialTraceRight_posSemidef (hσ.posSemidef.mul_mul_conjTranspose_same V)
    let U := spectralInclusion hq
    let L := U ⊗ₖ (1 : Matrix e e ℂ)
    let W := Lᴴ * V
    Wᴴ * W = 1 ∧ L * W = V ∧
      (∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) = Uᴴ * act Φ X * U) ∧
      (partialTraceRight (W * σ * Wᴴ)).PosDef := by
  dsimp only
  let q := partialTraceRight (V * σ * Vᴴ)
  let hq := partialTraceRight_posSemidef (hσ.posSemidef.mul_mul_conjTranspose_same V)
  let U := spectralInclusion hq
  let L := U ⊗ₖ (1 : Matrix e e ℂ)
  let W := Lᴴ * V
  have hL : L * Lᴴ = spectralSupport q ⊗ₖ (1 : Matrix e e ℂ) :=
    (retained_lift_mul_adjoint U).trans
      (congrArg (fun P => P ⊗ₖ (1 : Matrix e e ℂ)) (spectralInclusion_mul_adjoint hq))
  have hLW : L * W = V := by
    change L * (Lᴴ * V) = V
    rw [← Matrix.mul_assoc, hL]
    exact faithful_range_le_marginal_support (b := b) (e := e) V hσ
  have hW : Wᴴ * W = 1 := by
    calc
      _ = Vᴴ * (L * W) := by
        simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hLW, hV]
  have hCompressed (X : Matrix a a ℂ) :
      partialTraceRight (W * X * Wᴴ) = Uᴴ * partialTraceRight (V * X * Vᴴ) * U := by
    have hJoint : W * X * Wᴴ = Lᴴ * (V * X * Vᴴ) * L := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hJoint]
    exact partialTraceRight_compress U (V * X * Vᴴ)
  refine ⟨hW, hLW, fun X => (hCompressed X).trans ?_, ?_⟩
  · rw [hAction X]
  · rw [hCompressed σ]
    exact spectralCompression_posDef hq

end Stinespring

end PetzSupportCompressionInvariants
