/- GID: D5/S3/Quantum/Recovery/PetzSupportedStinespringGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzSupportedStinespringGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Stinespring complement gives the exact Petz deficit and a trace error bound. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
import D5.S3.Quantum.Recovery.PetzSpectralCoordinates
import D5.S3.Quantum.Recovery.PetzSchwarzRecovery
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction

/-!
# Supported Stinespring Gram and ordinary Petz recovery

The orthogonal complement of the supported dilation columns accounts for
the missing upper-edge norm. The resulting rectangular Gram at zero phase
is the ordinary Petz output on the positive spectrum of the reference output.
-/

set_option autoImplicit false

noncomputable section

universe u

open Matrix MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open PetzExponentialBoundaryEvaluation
open PetzCothStripMode (lowerWeight)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_mul_embed)
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality (channel_kraus_stinespring)
open D5.S3.Quantum.Recovery.PetzSpectralCoordinates (cfc_supported_sum)
open D5.S3.Quantum.Recovery.PetzSchwarzRecovery (petz_output_support_projection)

open private frobenius_sq from D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private support_preserves_of_kernel from D5.S3.Quantum.Recovery.PetzSchwarzRecovery

namespace D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

section SpectralPowers

variable {n : Type*} [Fintype n] [DecidableEq n]
  {H : Matrix n n ℂ}

/-- Columns of the spectral unitary indexed by its strictly positive spectrum. -/
private def columns (h : H.IsHermitian) : Matrix n {i : n // 0 < h.eigenvalues i} ℂ :=
  (h.eigenvectorUnitary : Matrix n n ℂ).submatrix id Subtype.val

private theorem columns_apply (h : H.IsHermitian) (x : n) (i : {i // 0 < h.eigenvalues i}) :
    columns h x i = h.eigenvectorBasis i.1 x :=
  h.eigenvectorUnitary_apply x i.1

private theorem columns_isometry (h : H.IsHermitian) : (columns h)ᴴ * columns h = 1 := by
  rw [columns, Matrix.conjTranspose_submatrix]
  let V : Matrix n n ℂ := h.eigenvectorUnitary
  change Vᴴ.submatrix Subtype.val (Equiv.refl n) * V.submatrix (Equiv.refl n) Subtype.val = 1
  rw [Matrix.submatrix_mul_equiv]
  rw [show Vᴴ * V = 1 from
    Unitary.coe_star_mul_self h.eigenvectorUnitary]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply]
  simp [Subtype.ext_iff]

/-- Spectral multiplier with value zero on the kernel, including at exponent zero. -/
private def supportedFunction (h : H.IsHermitian) (f : ℝ → ℂ) : Matrix n n ℂ :=
  (columns h * diagonal (fun i : {i : n // 0 < h.eigenvalues i} => f (h.eigenvalues i.1)) :
    Matrix n {i : n // 0 < h.eigenvalues i} ℂ) * (columns h)ᴴ

private theorem supportedFunction_sum (h : H.IsHermitian) (f : ℝ → ℂ) :
    supportedFunction h f = ∑ i : {i // 0 < h.eigenvalues i},
      f (h.eigenvalues i.1) •
        vecMulVec (fun x => h.eigenvectorBasis i.1 x) (star (fun x => h.eigenvectorBasis i.1 x)) := by
  ext x y
  unfold supportedFunction
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply, columns_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem supportedFunction_cfc (h : H.PosSemidef) (f : ℝ → ℝ) (hf : f 0 = 0) :
    supportedFunction h.1 (fun x => (f x : ℂ)) = cfc f H := by
  rw [supportedFunction_sum, cfc_supported_sum H h f hf]

private theorem supportedFunction_conjTranspose (h : H.IsHermitian) (f : ℝ → ℂ) :
    (supportedFunction h f)ᴴ = supportedFunction h (fun x => star (f x)) := by
  simp only [supportedFunction, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  rfl

private theorem supportedFunction_mul (h : H.IsHermitian) (f g : ℝ → ℂ) :
    supportedFunction h f * supportedFunction h g = supportedFunction h (fun x => f x * g x) := by
  simp only [supportedFunction, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (columns h)ᴴ (columns h) _, columns_isometry, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal _) (diagonal _) _, Matrix.diagonal_mul_diagonal]

private theorem supportedFunction_congr (h : H.IsHermitian) {f g : ℝ → ℂ}
    (he : ∀ x > 0, f x = g x) : supportedFunction h f = supportedFunction h g := by
  unfold supportedFunction
  have hd : (fun i : {i : n // 0 < h.eigenvalues i} => f (h.eigenvalues i.1)) =
      (fun i => g (h.eigenvalues i.1)) := funext fun i => he _ i.2
  rw [hd]

private theorem supportedFunction_id (h : H.PosSemidef) :
    supportedFunction h.1 Complex.ofReal = H := by
  exact (supportedFunction_cfc h id rfl).trans (cfc_id' ℝ H h.1.isSelfAdjoint)

private theorem supportedFunction_one (h : H.PosSemidef) :
    supportedFunction h.1 (fun _ => 1) = spectralSupport H := by
  rw [spectralSupport, ← supportedFunction_cfc h _ (by simp)]
  exact supportedFunction_congr h.1 fun x hx => by simp [hx.ne']

/-- The positive-spectrum power, evaluated by real logarithms. -/
private def power (h : H.IsHermitian) (z : ℂ) : Matrix n n ℂ :=
  supportedFunction h (fun x => Complex.exp ((Real.log x : ℂ) * z))

private theorem power_zero (h : H.PosSemidef) : power h.1 0 = spectralSupport H := by
  simp only [power, mul_zero, Complex.exp_zero, supportedFunction_one h]

private theorem power_one (h : H.PosSemidef) : power h.1 1 = H := by
  unfold power
  refine (supportedFunction_congr h.1 (g := Complex.ofReal) ?_).trans (supportedFunction_id h)
  intro x hx
  rw [mul_one, ← Complex.ofReal_exp, Real.exp_log hx]

private theorem power_mul (h : H.IsHermitian) (z w : ℂ) :
    power h z * power h w = power h (z + w) := by
  simp only [power, supportedFunction_mul, mul_add, Complex.exp_add]

private theorem power_conjTranspose (h : H.IsHermitian) (z : ℂ) :
    (power h z)ᴴ = power h (star z) := by
  simp only [power, supportedFunction_conjTranspose, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal]

private theorem exp_log_half {x : ℝ} (hx : 0 < x) :
    Complex.exp ((Real.log x : ℂ) * ((1 / 2 : ℝ) : ℂ)) = (Real.sqrt x : ℂ) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp, Complex.ofReal_mul]

private theorem power_half (h : H.PosSemidef) :
    power h.1 ((1 / 2 : ℝ) : ℂ) = cfc Real.sqrt H := by
  rw [← supportedFunction_cfc h Real.sqrt (by simp)]
  exact supportedFunction_congr h.1 fun _ hx => exp_log_half hx

private theorem power_neg_half (h : H.PosSemidef) :
    power h.1 (-((1 / 2 : ℝ) : ℂ)) = spectralInverseSqrt H := by
  rw [spectralInverseSqrt, ← supportedFunction_cfc h _ (by simp)]
  exact supportedFunction_congr h.1 fun _ hx => by
    rw [mul_neg, Complex.exp_neg, exp_log_half hx, Complex.ofReal_inv]

/-- Positive spectral columns span every vector with zero coefficients in
the kernel of a positive semidefinite matrix. -/
private theorem columns_support (h : H.PosSemidef) :
    columns h.1 * (columns h.1)ᴴ = spectralSupport H := by
  rw [← supportedFunction_one h]
  simp [supportedFunction]

private theorem card_positive_eigenvalues (h : H.PosSemidef) :
    Fintype.card {i // 0 < h.1.eigenvalues i} = H.rank := by
  rw [h.1.rank_eq_card_non_zero_eigs]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i =>
    (h.eigenvalues_nonneg i).lt_iff_ne')


end SpectralPowers

section ColumnCompletion

variable {r i c : Type*} [Fintype r] [Fintype i] [Fintype c]


private theorem frobenius_sq_trace (A : Matrix r c ℂ) : ‖A‖ ^ 2 = (A * Aᴴ).trace.re := by
  rw [frobenius_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

private theorem fromCols_norm_sq (A : Matrix r i ℂ) (B : Matrix r c ℂ) :
    ‖fromCols A B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  simp only [frobenius_sq, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
    Finset.sum_add_distrib]

/-- The missing right projection restores the full Gram. If that Gram has
unit trace, the restored block contributes exactly the compressed norm defect. -/
private theorem complete_gram [DecidableEq i] [DecidableEq c]
    (A : Matrix r i ℂ) (K : Matrix r c ℂ) (V : Matrix c i ℂ)
    (U : Matrix i i ℂ) (hV : Vᴴ * V = 1) (hU : U * Uᴴ = 1)
    (hK : (K * Kᴴ).trace.re = 1) :
    let X := K * V * U
    let Y := K * (1 - V * Vᴴ)
    let B := fromCols X Y
    B * Bᴴ = K * Kᴴ ∧ ‖B‖ = 1 ∧
      ‖Y‖ ^ 2 = 1 - ‖X‖ ^ 2 ∧
      ‖fromCols A (0 : Matrix r c ℂ) - B‖ ^ 2 = ‖A - X‖ ^ 2 + (1 - ‖X‖ ^ 2) := by
  dsimp only
  let P := V * Vᴴ
  let C := 1 - P
  have hP : P * P = P := by
    dsimp only [P]
    rw [Matrix.mul_assoc V Vᴴ (V * Vᴴ), ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
  have hCs : Cᴴ = C := by
    simp [C, P, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hC : C * C = C := by
    dsimp only [C]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hP, sub_self, sub_zero]
  let X := K * V * U
  let Y := K * C
  let B := fromCols X Y
  change B * Bᴴ = _ ∧ ‖B‖ = 1 ∧ ‖Y‖ ^ 2 = _ ∧ _
  have hx : X * Xᴴ = K * P * Kᴴ := by
    dsimp only [X, P]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ (Vᴴ * Kᴴ), hU, Matrix.one_mul]
  have hy : Y * Yᴴ = K * C * Kᴴ := by
    dsimp only [Y]
    simp only [Matrix.conjTranspose_mul, hCs, Matrix.mul_assoc, ← Matrix.mul_assoc C C Kᴴ, hC]
  have hGram : B * Bᴴ = K * Kᴴ := by
    dsimp only [B]
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows, hx, hy,
      ← Matrix.add_mul, ← Matrix.mul_add]
    simp [C]
  have hBsq : ‖B‖ ^ 2 = 1 := by rw [frobenius_sq_trace, hGram, hK]
  have hB : ‖B‖ = 1 := by nlinarith [norm_nonneg B]
  have hsum := fromCols_norm_sq X Y
  change ‖B‖ ^ 2 = _ at hsum
  have hY : ‖Y‖ ^ 2 = 1 - ‖X‖ ^ 2 := by linarith
  refine ⟨hGram, hB, hY, ?_⟩
  change ‖fromCols A (0 : Matrix r c ℂ) - B‖ ^ 2 = ‖A - X‖ ^ 2 + (1 - ‖X‖ ^ 2)
  have heq : fromCols A (0 : Matrix r c ℂ) - B = fromCols (A - X) (-Y) := by
    ext j (k | k) <;> simp [B]
  rw [heq, fromCols_norm_sq, norm_neg, hY]

end ColumnCompletion

variable {a b e : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e] [DecidableEq e]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

local notation "½" => (((1 / 2 : ℝ) : ℂ))
local notation "phase " t => ((t : ℂ) * Complex.I)

/-- The amplitude uses the canonical physical adjoint applied to the actual
spectral reconstruction on the output support. -/
private theorem amplitude_coordinate (M : SupportedRelativeModularModel Φ ρ σ) (z : ℂ)
    (i : M.data.J × M.data.I) :
    amplitude M.data z i =
      Complex.exp ((Real.log (inputRatio M.data i) : ℂ) * z) *
        ((Real.sqrt (M.data.ri i.2) : ℂ) *
          (star (M.data.v i.1) ⬝ᵥ
            (M.data.Ψ (M.data.spectralX
              (modularPower (outputRatio M.data) (-z) *ᵥ M.data.η)) *ᵥ M.data.u i.2))) := by
  rw [amplitude, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    modularPower, Matrix.mulVec_diagonal, M.coordinateAction]

private abbrev upper (t : ℝ) : ℂ := ½ + phase t

variable (D : SupportedRelativeModularData Φ ρ σ)

private abbrev Ur := columns D.hR.1
private abbrev Us := columns D.hS.1
private abbrev pPower := power D.hT.1
private abbrev qPower := power D.hQ.1

private def sourceBlock : Matrix D.J D.I ℂ :=
  (Us D)ᴴ * Ur D * diagonal (fun i => (Real.sqrt (D.ri i) : ℂ))

private def sourceAmplitude : Matrix D.J (D.I ⊕ (b × e)) ℂ :=
  fromCols (sourceBlock D) 0

private def mode (k : D.L × D.K) : Matrix b b ℂ :=
  vecMulVec (D.w k.1) (star (D.w k.1)) * vecMulVec (D.z k.2) (star (D.z k.2))

private def outputProduct (z : ℂ) : Matrix b b ℂ := qPower D (-z) * pPower D z

private theorem exp_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    Complex.exp ((Real.log (x / y) : ℂ) * z) =
      Complex.exp ((Real.log x : ℂ) * z) * Complex.exp ((Real.log y : ℂ) * (-z)) := by
  rw [Real.log_div hx.ne' hy.ne', Complex.ofReal_sub, sub_mul, Complex.exp_sub, mul_neg,
    Complex.exp_neg, div_eq_mul_inv]

private theorem outputProduct_sum (z : ℂ) :
    outputProduct D z =
      ∑ k : D.L × D.K, Complex.exp ((Real.log (outputRatio D k) : ℂ) * (-z)) • mode D k := by
  unfold outputProduct
  simp only [power, supportedFunction_sum]
  rw [Matrix.sum_mul, Fintype.sum_prod_type]
  simp only [Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_eq_mul, mode]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [exp_ratio l.2 k.2, neg_neg, mul_comm (Complex.exp _)]

private theorem spectralX_power (z : ℂ) :
    D.spectralX (modularPower (outputRatio D) (-z) *ᵥ D.η) = outputProduct D z := by
  rw [outputProduct_sum]
  simp only [SupportedRelativeModularData.spectralX, SupportedRelativeModularData.η,
    modularPower, Matrix.mulVec_diagonal, mode, Matrix.vecMulVec_mul_vecMulVec, smul_smul,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (Real.sqrt (D.pk k.2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr k.2.2).ne'
  have hc : Complex.exp ((Real.log (outputRatio D k) : ℂ) * (-z)) *
      ((Real.sqrt (D.pk k.2) : ℂ) * (star (D.w k.1) ⬝ᵥ D.z k.2)) /
        (Real.sqrt (D.pk k.2) : ℂ) =
      Complex.exp ((Real.log (outputRatio D k) : ℂ) * (-z)) * (star (D.w k.1) ⬝ᵥ D.z k.2) := by
    field_simp
    <;> ring
  rw [hc, Matrix.vecMulVec_smul, smul_smul]

private theorem coordinate_mul (X : Matrix a a ℂ) (j : D.J) (i : D.I) :
    ((Us D)ᴴ * X * Ur D) j i = star (D.v j) ⬝ᵥ (X *ᵥ D.u i) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    columns_apply, Pi.star_apply]

private theorem sourceBlock_apply (j : D.J) (i : D.I) :
    sourceBlock D j i = D.ξ (j, i) := by
  rw [sourceBlock, Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, columns_apply, SupportedRelativeModularData.ξ,
    dotProduct, Pi.star_apply]
  exact mul_comm _ _

private theorem sourceAmplitude_unit (M : SupportedRelativeModularModel Φ ρ σ) :
    ‖(sourceAmplitude M.data : Matrix M.data.J (M.data.I ⊕ (b × e)) ℂ)‖ = 1 := by
  have h : ‖(sourceAmplitude M.data : Matrix M.data.J (M.data.I ⊕ (b × e)) ℂ)‖ ^ 2 = 1 := by
    rw [frobenius_sq, ← M.normξ, Fintype.sum_prod_type]
    simp only [sourceAmplitude, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr,
      Matrix.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
      add_zero, sourceBlock_apply]
  nlinarith [norm_nonneg (sourceAmplitude M.data : Matrix M.data.J (M.data.I ⊕ (b × e)) ℂ)]

variable (W : Matrix (b × e) a ℂ)

private def lift (Y : Matrix b b ℂ) : Matrix (b × e) (b × e) ℂ :=
  Y ⊗ₖ (1 : Matrix e e ℂ)

private theorem lift_conjTranspose (Y : Matrix b b ℂ) :
    (lift (e := e) Y)ᴴ = lift Yᴴ := by
  simp [lift, conjTranspose_kronecker]

private theorem lift_mul (Y Z : Matrix b b ℂ) :
    lift (e := e) Y * lift Z = lift (Y * Z) := by
  rw [lift, lift, ← mul_kronecker_mul, Matrix.mul_one]
  rfl

private theorem lift_sum (z : ℂ) :
    lift (e := e) (outputProduct D z) =
      ∑ k : D.L × D.K, Complex.exp ((Real.log (outputRatio D k) : ℂ) * (-z)) • lift (mode D k) := by
  rw [outputProduct_sum]
  ext i j
  simp only [lift, Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, mul_assoc]

private def dilationColumns : Matrix (b × e) D.I ℂ := W * Ur D

private def rowFactor (z : ℂ) : Matrix D.J a ℂ :=
  modularPower D.sj z * (Us D)ᴴ

private def physicalFactor (t : ℝ) : Matrix D.J (b × e) ℂ :=
  rowFactor D (upper t) * Wᴴ * lift (outputProduct D (upper t))

private def phaseMatrix (t : ℝ) : Matrix D.I D.I ℂ := modularPower D.ri (-(phase t))

private def complementaryAmplitude (t : ℝ) : Matrix D.J (b × e) ℂ :=
  physicalFactor D W t * (1 - dilationColumns D W * (dilationColumns D W)ᴴ)

private def completed (t : ℝ) : Matrix D.J (D.I ⊕ (b × e)) ℂ :=
  fromCols (physicalFactor D W t * dilationColumns D W * phaseMatrix D t)
    (complementaryAmplitude D W t)

private def rotatedGram (t : ℝ) : Matrix D.J D.J ℂ :=
  rowFactor D (upper t) *
    D.Ψ (qPower D (-upper t) * D.T * qPower D (-star (upper t))) *
    (rowFactor D (upper t))ᴴ

private theorem dilationColumns_isometry (hW : Wᴴ * W = 1) :
    (dilationColumns D W)ᴴ * dilationColumns D W = 1 := by
  simp only [dilationColumns, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W _, hW, Matrix.one_mul, columns_isometry]

private theorem phase_unitary (t : ℝ) :
    phaseMatrix D t * (phaseMatrix D t)ᴴ = 1 := by
  rw [← Matrix.diagonal_one]
  simp only [phaseMatrix, modularPower, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  have hn : ‖Complex.exp ((Real.log (D.ri i) : ℂ) * (-(phase t)))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_conj', hn, one_pow, Complex.ofReal_one]

private theorem compression (M : SupportedRelativeModularModel Φ ρ σ)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X)
    (Y : Matrix b b ℂ) :
    Wᴴ * lift (e := e) Y * W = M.data.Ψ Y := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  rw [M.tracePair, show CStarMatrix.ofMatrix.symm
    (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = act Φ X from rfl, ← hAction X]
  calc
    _ = ((W * X * Wᴴ) * lift (e := e) Y).trace := by
      rw [← Matrix.mul_assoc X (Wᴴ * lift (e := e) Y) W,
        Matrix.trace_mul_comm (X * (Wᴴ * lift (e := e) Y)) W]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [← trace_partialTraceRight ((W * X * Wᴴ) * lift (e := e) Y),
      lift, partialTraceRight_mul_embed]

private theorem upper_star_add (t : ℝ) : star (upper t) + upper t = 1 := by
  apply Complex.ext <;> simp [upper, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> norm_num

private theorem outputProduct_gram (t : ℝ) :
    outputProduct D (upper t) * (outputProduct D (upper t))ᴴ =
      qPower D (-upper t) * D.T * qPower D (-star (upper t)) := by
  simp only [outputProduct, Matrix.conjTranspose_mul, power_conjTranspose, star_neg,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (pPower D _) (pPower D _) _, power_mul,
    add_comm (upper t) _, upper_star_add, power_one D.hT]

private theorem rowFactor_lift (z : ℂ) :
    Us D * rowFactor D z = power D.hS.1 z := by
  rw [rowFactor, ← Matrix.mul_assoc]
  rfl

private theorem rowFactor_gram (t : ℝ) :
    (rowFactor D (upper t))ᴴ * rowFactor D (upper t) = D.S := by
  let F := rowFactor D (upper t)
  change Fᴴ * F = D.S
  calc
    _ = (Us D * F)ᴴ * (Us D * F) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Us D)ᴴ (Us D) F, columns_isometry, Matrix.one_mul]
    _ = D.S := by
      rw [rowFactor_lift, power_conjTranspose, power_mul, upper_star_add, power_one D.hS]

private theorem physicalFactor_gram (M : SupportedRelativeModularModel Φ ρ σ)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X)
    (t : ℝ) :
    physicalFactor M.data W t * (physicalFactor M.data W t)ᴴ =
      rowFactor M.data (upper t) *
        M.data.Ψ (outputProduct M.data (upper t) * (outputProduct M.data (upper t))ᴴ) *
        (rowFactor M.data (upper t))ᴴ := by
  let F := rowFactor M.data (upper t)
  let Y := outputProduct M.data (upper t)
  let G : Matrix M.data.J (b × e) ℂ := F * Wᴴ
  let L : Matrix (b × e) (b × e) ℂ := lift Y
  change (G * L) * (G * L)ᴴ = F * M.data.Ψ (Y * Yᴴ) * Fᴴ
  have hG : Gᴴ = W * Fᴴ := by
    unfold G
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  let C : Matrix a a ℂ := (Wᴴ * lift (e := e) (Y * Yᴴ) : Matrix a (b × e) ℂ) * W
  have hC : C = M.data.Ψ (Y * Yᴴ) := compression W M hAction _
  calc
    _ = G * (L * Lᴴ) * Gᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = F * C * Fᴴ := by
      rw [hG]
      have hL : L * Lᴴ = lift (e := e) (Y * Yᴴ) := by
        dsimp only [L]
        rw [lift_conjTranspose, lift_mul]
      rw [hL]
      simp only [C, G, Matrix.mul_assoc]
    _ = _ := by rw [hC]

private theorem physicalFactor_unitTrace (M : SupportedRelativeModularModel Φ ρ σ)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X)
    (t : ℝ) :
    (physicalFactor M.data W t * (physicalFactor M.data W t)ᴴ).trace.re = 1 := by
  let D := M.data
  let F := rowFactor D (upper t)
  let Y := outputProduct D (upper t) * (outputProduct D (upper t))ᴴ
  rw [physicalFactor_gram W M hAction]
  change (F * D.Ψ Y * Fᴴ).trace.re = 1
  have hCycle : (F * D.Ψ Y * Fᴴ).trace = (Fᴴ * F * D.Ψ Y).trace := by
    rw [Matrix.trace_mul_comm (F * D.Ψ Y) Fᴴ, ← Matrix.mul_assoc]
  rw [hCycle, rowFactor_gram, M.tracePair]
  change (D.Q * Y).trace.re = 1
  have hq : qPower D (-star (upper t)) * D.Q * qPower D (-upper t) =
      spectralSupport D.Q := by
    nth_rw 1 [(show qPower D 1 = D.Q from power_one D.hQ).symm]
    rw [power_mul, power_mul]
    have hh : -star (upper t) + 1 + -upper t = 0 := by
      rw [← upper_star_add t]
      abel
    rw [hh, power_zero D.hQ]
  have htrace : (D.Q * Y).trace = (spectralSupport D.Q * D.T).trace := by
    dsimp only [Y]
    rw [outputProduct_gram, ← Matrix.mul_assoc D.Q _ _, Matrix.trace_mul_comm _ (qPower D _),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq]
  rw [htrace, petz_output_support_projection M, show D.T.trace = 1 from (Φ.mapState ρ).2.2,
    Complex.one_re]

private theorem completed_columns (M : SupportedRelativeModularModel Φ ρ σ)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X)
    (t : ℝ) (j : M.data.J) (i : M.data.I) :
    completed M.data W t j (.inl i) = amplitude M.data (upper t) (j, i) := by
  let D := M.data
  let Y := outputProduct D (upper t)
  have hMatrix : physicalFactor D W t * dilationColumns D W =
      modularPower D.sj (upper t) * ((Us D)ᴴ * D.Ψ Y * Ur D) := by
    change (modularPower D.sj (upper t) * (Us D)ᴴ * Wᴴ * lift (e := e) Y) * (W * Ur D) = _
    calc
      _ = modularPower D.sj (upper t) * ((Us D)ᴴ * ((Wᴴ * lift (e := e) Y * W) * Ur D)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [compression W M hAction, Matrix.mul_assoc]
  change (physicalFactor D W t * dilationColumns D W * phaseMatrix D t) j i =
    amplitude M.data (upper t) (j, i)
  rw [amplitude_coordinate M, spectralX_power, hMatrix,
    phaseMatrix]
  simp only [modularPower, Matrix.mul_diagonal, Matrix.diagonal_mul, coordinate_mul]
  change Complex.exp ((Real.log (D.sj j) : ℂ) * upper t) *
      (star (D.v j) ⬝ᵥ (D.Ψ Y *ᵥ D.u i)) *
      Complex.exp ((Real.log (D.ri i) : ℂ) * (-(phase t))) =
    Complex.exp ((Real.log (D.sj j / D.ri i) : ℂ) * upper t) *
      ((Real.sqrt (D.ri i) : ℂ) * (star (D.v j) ⬝ᵥ (D.Ψ Y *ᵥ D.u i)))
  rw [exp_ratio j.2 i.2, ← exp_log_half i.2]
  have he : Complex.exp ((Real.log (D.ri i) : ℂ) * (-upper t)) *
      Complex.exp ((Real.log (D.ri i) : ℂ) * ½) =
      Complex.exp ((Real.log (D.ri i) : ℂ) * (-(phase t))) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp only [upper]
    ring
  calc
    _ = Complex.exp ((Real.log (D.sj j) : ℂ) * upper t) *
        (Complex.exp ((Real.log (D.ri i) : ℂ) * (-upper t)) *
          Complex.exp ((Real.log (D.ri i) : ℂ) * ½)) *
        (star (D.v j) ⬝ᵥ (D.Ψ Y *ᵥ D.u i)) := by rw [he]; ring
    _ = _ := by ring

private theorem source_gram :
    sourceBlock D * (sourceBlock D)ᴴ = (Us D)ᴴ * D.R * Us D := by
  let U := Ur D
  let V := Us D
  let L := diagonal (fun i : D.I => (Real.sqrt (D.ri i) : ℂ))
  have hL : Lᴴ = L := by simp [L, Matrix.diagonal_conjTranspose, Complex.star_def]
  have hL₂ : L * L = diagonal (fun i : D.I => (D.ri i : ℂ)) := by
    rw [show L = diagonal (fun i : D.I => (Real.sqrt (D.ri i) : ℂ)) from rfl,
      Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt i.2.le]
  change (Vᴴ * U * L) * (Vᴴ * U * L)ᴴ = Vᴴ * D.R * V
  rw [(show supportedFunction D.hR.1 Complex.ofReal = D.R from supportedFunction_id D.hR).symm]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hL, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L L _, hL₂]
  simp only [supportedFunction, Matrix.mul_assoc]
  rfl

private theorem source_gram_lift (M : SupportedRelativeModularModel Φ ρ σ) :
    Us M.data * (sourceBlock M.data * (sourceBlock M.data)ᴴ) * (Us M.data)ᴴ = M.data.R := by
  let D := M.data
  let V := Us D
  have hP : (V * Vᴴ) * D.R = D.R := by
    rw [columns_support D.hS]
    exact support_preserves_of_kernel D.S D.R D.hS D.hR M.inputSupport
  have hP' : D.R * (V * Vᴴ) = D.R := by
    have h := congrArg Matrix.conjTranspose hP
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, D.hR.1.eq] using h
  rw [source_gram]
  change V * (Vᴴ * D.R * V) * Vᴴ = D.R
  calc
    _ = (V * Vᴴ) * D.R * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
    _ = D.R := by rw [hP, hP']

/-- The canonical ordinary recovery uses the actual Kraus adjoint and the
inverse square root on the positive output spectrum. -/
def recoveredState (D : SupportedRelativeModularData Φ ρ σ) : Matrix a a ℂ :=
  let Qinv := spectralInverseSqrt D.Q
  cfc Real.sqrt D.S *
    krausAdjoint (actual_kraus_representation Φ).kraus (Qinv * D.T * Qinv) *
    cfc Real.sqrt D.S

/-- The completed amplitude has the adjoint Gram at every real upper-edge phase.
Its orthogonal column block contributes the missing squared norm. The two
zero-phase Grams lift to the original state and its ordinary recovery. -/
theorem supported_stinespring_gram (M : SupportedRelativeModularModel Φ ρ σ)
    (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X) :
    let D := M.data
    let A : Matrix D.J (D.I ⊕ (b × e)) ℂ := sourceAmplitude D
    let B := completed D W
    ‖A‖ = 1 ∧ (∀ t, ‖B t‖ = 1) ∧
      (∀ t, ‖A - B t‖ ^ 2 = deficit D (1 / 2) t) ∧
      (∀ t, ‖complementaryAmplitude D W t‖ ^ 2 =
        1 - ∑ i, ‖amplitude D (upper t) i‖ ^ 2) ∧
      (∀ t, B t * (B t)ᴴ = rotatedGram D t) ∧
      Us D * (A * Aᴴ) * (Us D)ᴴ = D.R ∧
      Us D * (B 0 * (B 0)ᴴ) * (Us D)ᴴ = recoveredState D := by
  let D := M.data
  let A : Matrix D.J (D.I ⊕ (b × e)) ℂ := sourceAmplitude D
  have hc (t : ℝ) := complete_gram (sourceBlock D) (physicalFactor D W t)
    (dilationColumns D W) (phaseMatrix D t) (dilationColumns_isometry D W hW)
    (phase_unitary D t) (physicalFactor_unitTrace W M hAction t)
  have hcol (t : ℝ) (j : D.J) (i : D.I) :
      (physicalFactor D W t * dilationColumns D W * phaseMatrix D t) j i =
        amplitude D (upper t) (j, i) := completed_columns W M hAction t j i
  have hnorm (t : ℝ) :
      ‖physicalFactor D W t * dilationColumns D W * phaseMatrix D t‖ ^ 2 =
        ∑ i, ‖amplitude D (upper t) i‖ ^ 2 := by
    rw [frobenius_sq, Fintype.sum_prod_type]
    simp only [hcol]
  have hGram (t : ℝ) : completed D W t * (completed D W t)ᴴ = rotatedGram D t := by
    calc
      _ = physicalFactor D W t * (physicalFactor D W t)ᴴ := (hc t).1
      _ = _ := by rw [physicalFactor_gram W M hAction, outputProduct_gram, rotatedGram]
  refine ⟨sourceAmplitude_unit M, fun t => (hc t).2.1, ?_, ?_, hGram, ?_, ?_⟩
  · intro t
    have hdist : ‖A - completed D W t‖ ^ 2 =
        ‖sourceBlock D - physicalFactor D W t * dilationColumns D W * phaseMatrix D t‖ ^ 2 +
          (1 - ‖physicalFactor D W t * dilationColumns D W * phaseMatrix D t‖ ^ 2) := (hc t).2.2.2
    change ‖A - completed D W t‖ ^ 2 = _
    rw [hdist, deficit_eq_distance_add_defect M, hnorm, frobenius_sq, Fintype.sum_prod_type]
    simp only [Matrix.sub_apply, sourceBlock_apply, hcol, upper, Fintype.sum_prod_type]
    rfl
  · intro t
    simpa only [complementaryAmplitude, hnorm t] using (hc t).2.2.1
  · change Us D * (A * Aᴴ) * (Us D)ᴴ = D.R
    rw [show A = fromCols (sourceBlock D) (0 : Matrix D.J (b × e) ℂ) from rfl,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows,
      Matrix.zero_mul, add_zero, source_gram_lift M]
  · change Us D * (completed D W 0 * (completed D W 0)ᴴ) * (Us D)ᴴ = _
    rw [hGram, rotatedGram]
    have h0 : upper 0 = ½ := by simp [upper]
    have hs0 : star ½ = ½ := by rw [Complex.star_def, Complex.conj_ofReal]
    rw [h0, hs0]
    have hQ0 : qPower M.data (-½) = spectralInverseSqrt M.data.Q := power_neg_half M.data.hQ
    rw [hQ0]
    have hF : Us D * rowFactor D ½ = cfc Real.sqrt D.S := by
      rw [rowFactor_lift, power_half D.hS]
    have hFt : (rowFactor D ½)ᴴ * (Us D)ᴴ = cfc Real.sqrt D.S := by
      rw [← Matrix.conjTranspose_mul, hF]
      exact (cfc_predicate _ D.S : IsSelfAdjoint (cfc Real.sqrt D.S)).star_eq
    rw [Matrix.mul_assoc (rowFactor D ½) _ _, ← Matrix.mul_assoc (Us D) _ _,
      hF, Matrix.mul_assoc, Matrix.mul_assoc, hFt]
    unfold recoveredState
    change cfc Real.sqrt D.S * (_ * _) = _
    change cfc Real.sqrt D.S *
      ((∑ c, (D.kraus c)ᴴ * (spectralInverseSqrt D.Q * D.T * spectralInverseSqrt D.Q) *
        D.kraus c) * cfc Real.sqrt D.S) = _
    rw [M.kraus_eq]
    let Z : Matrix a a ℂ :=
      krausAdjoint (actual_kraus_representation Φ).kraus
        (spectralInverseSqrt D.Q * D.T * spectralInverseSqrt D.Q)
    change cfc Real.sqrt D.S * (Z * cfc Real.sqrt D.S) =
      cfc Real.sqrt D.S * Z * cfc Real.sqrt D.S
    exact (Matrix.mul_assoc _ _ _).symm

private def block (j : D.J) : D.I ⊕ (b × e) → (D.J × D.I) ⊕ D.J
  | .inl i => .inl (j, i)
  | .inr _ => .inr j

private def outer : (D.J × D.I) ⊕ D.J → ℝ
  | .inl ji => inputRatio D ji
  | .inr j => D.sj j

private def modeFactor (k : D.L × D.K) : Matrix D.J (b × e) ℂ :=
  (Us D)ᴴ * Wᴴ * lift (mode D k)

private def coefficients (k : D.L × D.K) : Matrix D.J (D.I ⊕ (b × e)) ℂ :=
  fromCols ((modeFactor D W k * dilationColumns D W) *
      diagonal (fun i => (Real.sqrt (D.ri i) : ℂ)))
    (modeFactor D W k * (1 - dilationColumns D W * (dilationColumns D W)ᴴ))

private theorem boundary_scalar {x : ℝ} (hx : 0 < x) (t : ℝ) :
    Complex.exp ((Real.log x : ℂ) * upper t) =
      (Real.sqrt x : ℂ) * Complex.exp (Complex.I * (Real.log x : ℂ) * (t : ℂ)) := by
  rw [show (Real.log x : ℂ) * upper t =
      (Real.log x : ℂ) * ½ + Complex.I * (Real.log x : ℂ) * (t : ℂ) by
      dsimp only [upper]; ring, Complex.exp_add, exp_log_half hx]

private theorem boundary_eq (t : ℝ) :
    petzBoundary (block (e := e) D) (outer D) D.ql D.pk
      (sourceAmplitude D) (coefficients D W) t =
      sourceAmplitude D - completed D W t := by
  let V := dilationColumns D W
  let P : Matrix (b × e) (b × e) ℂ := 1 - V * Vᴴ
  let coeff := fun k : D.L × D.K => Complex.exp ((Real.log (outputRatio D k) : ℂ) * (-upper t))
  have hfactor : physicalFactor D W t = modularPower D.sj (upper t) *
      (∑ k : D.L × D.K, coeff k • modeFactor D W k) := by
    let F : Matrix D.J (b × e) ℂ := rowFactor D (upper t) * Wᴴ
    let L : D.L × D.K → Matrix (b × e) (b × e) ℂ := fun k => coeff k • lift (mode D k)
    let M := modularPower D.sj (upper t)
    let N : D.L × D.K → Matrix D.J (b × e) ℂ := fun k => coeff k • modeFactor D W k
    change (F * lift (e := e) (outputProduct D (upper t)) : Matrix D.J (b × e) ℂ) =
      M * ∑ k, N k
    have hL : lift (e := e) (outputProduct D (upper t)) = ∑ k, L k := lift_sum D (e := e) (upper t)
    calc
      _ = F * (∑ k, L k) := congrArg (fun X : Matrix (b × e) (b × e) ℂ =>
        (F * X : Matrix D.J (b × e) ℂ)) hL
      _ = ∑ k, F * L k := Matrix.mul_sum _ _ _
      _ = ∑ k, M * N k := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [F, L, M, N, rowFactor, modeFactor, Matrix.mul_smul, Matrix.mul_assoc]
        exact congrArg (fun X : Matrix D.J (b × e) ℂ =>
          coeff k • (modularPower D.sj (upper t) * X))
          (Matrix.mul_assoc (Us D)ᴴ Wᴴ (lift (e := e) (mode D k))).symm
      _ = _ := (Matrix.mul_sum _ _ _).symm
  ext j (i | c)
  · change _ = sourceAmplitude D j (.inl i) -
      (physicalFactor D W t * V * phaseMatrix D t) j i
    simp only [petzBoundary, Matrix.of_apply, hfactor, Matrix.mul_assoc _ _ V,
      Matrix.sum_mul, Matrix.smul_mul, phaseMatrix, modularPower, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.sum_apply, Matrix.smul_apply, block, outer, coefficients,
      fromCols_apply_inl, retainedFrequency, smul_eq_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    let ratio := outputRatio D k
    have hr : 0 < ratio := div_pos k.1.2 k.2.2
    have hs : 0 < inputRatio D (j, i) := div_pos j.2 i.2
    change (Real.sqrt (inputRatio D (j, i) / ratio) : ℂ) *
        ((modeFactor D W k * V) j i * (Real.sqrt (D.ri i) : ℂ)) *
        Complex.exp (Complex.I * (Real.log (inputRatio D (j, i) / ratio) : ℂ) * (t : ℂ)) = _
    have hscalar := boundary_scalar (div_pos hs hr) t
    have hphase : Complex.exp ((Real.log (D.ri i) : ℂ) * (-upper t)) *
        Complex.exp ((Real.log (D.ri i) : ℂ) * ½) =
        Complex.exp ((Real.log (D.ri i) : ℂ) * (-(phase t))) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp only [upper]
      ring
    calc
      _ = ((Real.sqrt (inputRatio D (j, i) / ratio) : ℂ) *
          Complex.exp (Complex.I * (Real.log (inputRatio D (j, i) / ratio) : ℂ) * (t : ℂ))) *
          (Real.sqrt (D.ri i) : ℂ) * (modeFactor D W k * V) j i := by
            dsimp only [V]; ring
      _ = _ := by
        rw [← hscalar, exp_ratio hs hr, exp_ratio j.2 i.2, ← exp_log_half i.2]
        dsimp only [coeff, ratio]
        rw [show _ * _ * Complex.exp ((Real.log (D.ri i) : ℂ) * ½) =
            Complex.exp ((Real.log (D.sj j) : ℂ) * upper t) *
              Complex.exp ((Real.log (outputRatio D k) : ℂ) * (-upper t)) *
              (Complex.exp ((Real.log (D.ri i) : ℂ) * (-upper t)) *
                Complex.exp ((Real.log (D.ri i) : ℂ) * ½)) by ring, hphase]
        ring
  · change _ = sourceAmplitude D j (.inr c) - (physicalFactor D W t * P) j c
    simp only [petzBoundary, Matrix.of_apply, hfactor, Matrix.mul_assoc _ _ P,
      Matrix.sum_mul, Matrix.smul_mul, modularPower, Matrix.diagonal_mul,
      Matrix.sum_apply, Matrix.smul_apply, block, outer, coefficients,
      fromCols_apply_inr, retainedFrequency, smul_eq_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hr : 0 < outputRatio D k := div_pos k.1.2 k.2.2
    rw [mul_right_comm, ← boundary_scalar (div_pos j.2 hr), exp_ratio j.2 hr]
    rw [mul_assoc]

private theorem upperIntegral_le_loss (M : SupportedRelativeModularModel Φ ρ σ) :
    let D := M.data
    (∫ t : ℝ, petzWeight t * deficit D (1 / 2) t) ≤
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
  have h := (integral_supported_channel_strip M).2.2
  dsimp only
  rw [← h]
  have hlow : 0 ≤ ∫ t : ℝ, lowerWeight t * deficit M.data 0 t := by
    apply integral_nonneg
    intro t
    apply mul_nonneg _ (lower_deficit_nonneg M t)
    exact div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _))
  linarith

/-- Reindex the existing environment-first Stinespring matrix by swapping
its product row coordinates. The right partial trace is the actual channel. -/
private theorem exists_retainedFirst_stinespring (Φ : QuantumChannel a b) :
    ∃ V : Matrix (b × (b × a)) a ℂ, Vᴴ * V = 1 ∧
      ∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) =
        act Φ X := by
  obtain ⟨W, hW, hAction⟩ := channel_kraus_stinespring.2 Φ
  let swap : b × (b × a) ≃ (b × a) × b := Equiv.prodComm b (b × a)
  let V := W.submatrix swap id
  refine ⟨V, ?_, ?_⟩
  · change (W.submatrix swap id)ᴴ * W.submatrix swap id = _
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv Wᴴ W id swap id,
      Matrix.submatrix_id_id, hW]
  · intro X
    change partialTraceLeft (W * X * Wᴴ) =
      act Φ X
    exact hAction X

set_option maxHeartbeats 800000 in
-- The dependent spectral carriers also occur in the endpoint and integral types.
private theorem traceBound_of_dilation (M : SupportedRelativeModularModel Φ ρ σ) (W : Matrix (b × e) a ℂ) (hW : Wᴴ * W = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (W * X * Wᴴ) =
      act Φ X)
    (m : ℕ) (hm : let D := M.data
      ∀ l, (distinctFrequencies (retainedFrequency (outer D l) D.ql D.pk)).card ≤ m) :
    let D := M.data
    traceNorm (D.R - recoveredState D) ^ 2 ≤ (8 * (m : ℝ)) *
      (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  let D := M.data
  let A : Matrix D.J (D.I ⊕ (b × e)) ℂ := sourceAmplitude D
  let B := completed D W
  let E := petzBoundary (block (e := e) D) (outer D) D.ql D.pk A (coefficients D W)
  have hE (t : ℝ) : E t = A - B t := boundary_eq D W t
  have hB : A - E 0 = B 0 := by rw [hE, sub_sub_cancel]
  obtain ⟨hAu, hBu, hd, _, _, hA, hRec⟩ := supported_stinespring_gram M W hW hAction
  have hEv := traceNorm_gram_sub_sq_le_petz_boundary (block (e := e) D) (outer D)
    D.ql D.pk A (coefficients D W) m hm hAu (by
      change ‖A - E 0‖ = 1
      rw [hB]
      exact hBu 0)
  dsimp only at hEv
  change traceNorm ((A - E 0) * (A - E 0)ᴴ - A * Aᴴ) ^ 2 ≤
    (8 * (m : ℝ)) * (∫ t : ℝ, petzWeight t * ‖E t‖ ^ 2) at hEv
  have hpoint (t : ℝ) : ‖E t‖ ^ 2 = deficit D (1 / 2) t := by
    rw [hE]
    exact hd t
  rw [hB] at hEv
  simp only [hpoint] at hEv
  have hLift : Us D * (B 0 * (B 0)ᴴ - A * Aᴴ) * (Us D)ᴴ =
      recoveredState D - D.R := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hA, hRec]
  have hTrace := traceNorm_isometry (Us D) (columns_isometry D.hS.1)
    (B 0 * (B 0)ᴴ - A * Aᴴ)
  rw [hLift, ← neg_sub, Foundation.FiniteTraceDistance.traceNorm_neg] at hTrace
  calc
    _ = traceNorm (B 0 * (B 0)ᴴ - A * Aᴴ) ^ 2 := by rw [hTrace]
    _ ≤ (8 * (m : ℝ)) * (∫ t : ℝ, petzWeight t * deficit D (1 / 2) t) := hEv
    _ ≤ _ := mul_le_mul_of_nonneg_left (upperIntegral_le_loss M) (by positivity)

/-- For an actual finite CPTP map and supported input states, the ordinary
Petz trace error is bounded by the finite trace-log entropy loss. The
coefficient uses the positive ranks of the two actual channel outputs. -/
theorem ordinary_petz_traceNorm_sq_le_entropy_loss
    {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) :
    let D := M.data
    traceNorm (D.R - recoveredState D) ^ 2 ≤
      (8 * (↑(1 + D.T.rank * D.Q.rank) : ℝ)) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  obtain ⟨W, hW, hAction⟩ := exists_retainedFirst_stinespring Φ
  let D := M.data
  refine traceBound_of_dilation M W hW hAction (1 + D.T.rank * D.Q.rank) ?_
  change ∀ l : (D.J × D.I) ⊕ D.J,
    (distinctFrequencies (retainedFrequency (outer D l) D.ql D.pk)).card ≤
      1 + D.T.rank * D.Q.rank
  intro l
  have hcard := Finset.card_image_le
    (s := (Finset.univ : Finset (Option (D.L × D.K))))
    (f := retainedFrequency (outer D l) D.ql D.pk)
  simpa only [distinctFrequencies, Finset.card_univ, Fintype.card_option, Fintype.card_prod,
    card_positive_eigenvalues D.hT, card_positive_eigenvalues D.hQ,
    Nat.mul_comm D.Q.rank D.T.rank, Nat.add_comm (D.T.rank * D.Q.rank) 1] using hcard

#print axioms supported_stinespring_gram
#print axioms ordinary_petz_traceNorm_sq_le_entropy_loss

end D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
