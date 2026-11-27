/- GID: D5/S3/Quantum/Recovery/PetzSupportedLinearRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzSupportedLinearRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both exact supported strip deficits are squared distances of physical Stinespring amplitudes. -/

import Mathlib.Analysis.Normed.Operator.Basic
import D5.S3.Analytic.PetzLogisticMatrixStrip
import D5.S3.Quantum.Recovery.CanonicalPetzEquality
import D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
import D5.S3.Quantum.Recovery.PetzSupportedStinespringGram

/-! Physical boundary amplitudes for the actual supported Stinespring model. -/

set_option autoImplicit false

noncomputable section

universe u

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_mul_embed)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight trace_partialTraceRight)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)
open D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Recovery.PetzSupportedStinespringGram (recoveredState)
open D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation
open D5.S3.Quantum.Recovery.PetzSchwarzRecovery (petz_output_support_projection)
open PetzCothStripMode (lowerWeight)
open PetzExponentialBoundaryEvaluation (petzWeight petzWeight_pos)
open PetzLogisticMatrixStrip (differentiable_exp_sum norm_exp_sum_le)

open private sourceBlock sourceBlock_apply amplitude_coordinate coordinate_mul spectralX_power
  columns columns_isometry columns_support card_positive_eigenvalues
  Ur Us pPower qPower power power_conjTranspose power_mul power_zero power_one
  power_half power_neg_half exp_log_half exp_ratio
  supportedFunction supportedFunction_sum outputProduct outputProduct_gram rowFactor rowFactor_lift
  compression frobenius_sq_trace exists_retainedFirst_stinespring from
  D5.S3.Quantum.Recovery.PetzSupportedStinespringGram
open private overlap_eq_pair from D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open private support_preserves_of_kernel from D5.S3.Quantum.Recovery.PetzSchwarzRecovery
open private traceNorm_gram_sub_le from D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
open private upperWeight_le_lowerWeight from D5.S3.Analytic.PetzLogisticMidline
open private diagonalPhase from D5.S3.Quantum.Recovery.PetzMixedBoundaryEvaluation

namespace D5.S3.Quantum.Recovery.PetzSupportedLinearRank

local notation "half" => (((1 / 2 : ℝ) : ℂ))
local notation "itime" => (fun t : ℝ => (t : ℂ) * Complex.I)

private theorem star_it (t : ℝ) : star (itime t) = -(itime t) := by
  simp [Complex.star_def, map_mul, Complex.conj_I]

private theorem star_half : star (half : ℂ) = half := by
  rw [Complex.star_def, Complex.conj_ofReal]

private theorem half_add_half : (half : ℂ) + half = 1 := by norm_num

private abbrev matMul {i j k : Type*} [Fintype j] (X : Matrix i j ℂ) (Y : Matrix j k ℂ) :
    Matrix i k ℂ := X * Y

section MatrixIdentities

variable {r c s : Type*} [Fintype r] [Fintype c] [Fintype s]

private theorem sq_mul_isometry [DecidableEq s] (V : Matrix r s ℂ) (hV : Vᴴ * V = 1)
    (Z : Matrix s c ℂ) : ‖V * Z‖ ^ 2 = ‖Z‖ ^ 2 := by
  simp only [frobenius_sq_trace, Matrix.conjTranspose_mul]
  congr 1
  rw [← Matrix.mul_assoc (V * Z), Matrix.trace_mul_comm _ Vᴴ,
    ← Matrix.mul_assoc Vᴴ (V * Z), ← Matrix.mul_assoc Vᴴ V Z, hV, Matrix.one_mul]

private theorem sq_mul_adjoint_isometry [DecidableEq s] (V : Matrix r s ℂ) (hV : Vᴴ * V = 1)
    (Z : Matrix c s ℂ) : ‖Z * Vᴴ‖ ^ 2 = ‖Z‖ ^ 2 := by
  simp only [frobenius_sq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc Z, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]

private theorem sq_sub_of_unit (U V : Matrix r c ℂ) (hU : ‖U‖ ^ 2 = 1)
    (hV : ‖V‖ ^ 2 = 1) :
    ‖U - V‖ ^ 2 = 2 * (1 - (Uᴴ * V).trace.re) := by
  have hcross : (U * Vᴴ).trace.re = (V * Uᴴ).trace.re := by
    have h := congrArg Complex.re (Matrix.trace_conjTranspose (U * Vᴴ))
    simpa [Matrix.conjTranspose_mul, Complex.star_def] using h.symm
  rw [frobenius_sq_trace] at hU hV ⊢
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, hU, hV, hcross, Matrix.trace_mul_comm V Uᴴ]
  ring

end MatrixIdentities

section Tensor

variable {b k l e : Type u} [Fintype b] [Fintype k] [Fintype l] [Fintype e] [DecidableEq e]

private def tensorId (X : Matrix b k ℂ) : Matrix (b × e) (k × e) ℂ :=
  X ⊗ₖ (1 : Matrix e e ℂ)

private theorem tensorId_mul (X : Matrix b k ℂ) (Y : Matrix k l ℂ) :
    (tensorId (e := e) X * tensorId (e := e) Y : Matrix (b × e) (l × e) ℂ) =
      tensorId (e := e) (X * Y) := by
  change (X ⊗ₖ (1 : Matrix e e ℂ)) * (Y ⊗ₖ (1 : Matrix e e ℂ)) =
    (X * Y) ⊗ₖ (1 : Matrix e e ℂ)
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

private theorem tensorId_adjoint (X : Matrix b k ℂ) :
    (tensorId (e := e) X)ᴴ = tensorId Xᴴ := by
  simp [tensorId, conjTranspose_kronecker]

private theorem tensorId_isometry [DecidableEq k] (X : Matrix b k ℂ) (hX : Xᴴ * X = 1) :
    (tensorId (e := e) X)ᴴ * tensorId (e := e) X = 1 := by
  rw [tensorId_adjoint]
  rw [tensorId_mul, hX, tensorId, Matrix.one_kronecker_one]

private theorem tensorId_diagonal [DecidableEq k] (p : k → ℝ) (z : ℂ) :
    tensorId (e := e) (modularPower p z) = diagonalPhase (p ∘ Prod.fst) z := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [tensorId, modularPower, diagonalPhase, kroneckerMap_apply]
  · by_cases h₁ : i.1 = j.1
    · have h₂ : i.2 ≠ j.2 := fun h₂ => h (Prod.ext h₁ h₂)
      simp [tensorId, modularPower, diagonalPhase, kroneckerMap_apply, h, h₁, h₂]
    · simp [tensorId, modularPower, diagonalPhase, kroneckerMap_apply, h, h₁]

private theorem trace_tensor_right [DecidableEq b] (A : Matrix (b × e) (b × e) ℂ) (T : Matrix b b ℂ) :
    (A * tensorId T).trace = (partialTraceRight A * T).trace := by
  rw [← trace_partialTraceRight (A * tensorId T)]
  exact congrArg Matrix.trace (partialTraceRight_mul_embed A T)

/-- A factor belongs to the lift of the support of its actual marginal.
This is used for the source and reference square roots independently. -/
private theorem tensor_projection_of_marginal [DecidableEq b]
    {c : Type*} [Fintype c] (X : Matrix (b × e) c ℂ)
    (E : Matrix b b ℂ) (hE : Eᴴ = E) (hEE : E * E = E)
    (hMarginal : partialTraceRight (X * Xᴴ) * E = partialTraceRight (X * Xᴴ)) :
    tensorId E * X = X := by
  let F := tensorId (e := e) E
  have hF : Fᴴ = F := by rw [tensorId_adjoint, hE]
  have hFF : F * F = F := by
    dsimp only [F]
    rw [tensorId_mul (e := e) E E, hEE]
  have hnorm : ‖F * X - X‖ ^ 2 = 0 := by
    have htr : (X * Xᴴ * F).trace = (X * Xᴴ).trace := by
      dsimp only [F]
      rw [trace_tensor_right, hMarginal, trace_partialTraceRight]
    rw [frobenius_sq_trace, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hF]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    have hleft : (F * X * Xᴴ).trace = (X * Xᴴ).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm F, htr]
    have hright : (X * (Xᴴ * F)).trace = (X * Xᴴ).trace := by
      rw [← Matrix.mul_assoc, htr]
    have hboth : (F * X * (Xᴴ * F)).trace = (X * Xᴴ).trace := by
      rw [← Matrix.mul_assoc (F * X), Matrix.trace_mul_comm _ F,
        Matrix.mul_assoc F X Xᴴ, ← Matrix.mul_assoc F F, hFF, ← Matrix.mul_assoc, hleft]
    rw [hleft, hright, hboth]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (by change ‖F * X - X‖ = 0; nlinarith [norm_nonneg (F * X - X)]))

end Tensor

private theorem differentiable_power {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Differentiable ℂ (power hA) := by
  have hPower : power hA = fun z => ∑ i : {i // 0 < hA.eigenvalues i},
      Complex.exp ((Real.log (hA.eigenvalues i.1) : ℂ) * z) •
        vecMulVec (fun x => hA.eigenvectorBasis i.1 x)
          (star (fun x => hA.eigenvectorBasis i.1 x)) :=
    funext fun z => supportedFunction_sum hA _
  rw [hPower]
  exact
    (differentiable_exp_sum
      (fun i : {i // 0 < hA.eigenvalues i} => Real.log (hA.eigenvalues i.1))
      (fun i => vecMulVec (fun x => hA.eigenvectorBasis i.1 x)
        (star (fun x => hA.eigenvectorBasis i.1 x))))

private def powerBound {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i : {i // 0 < hA.eigenvalues i},
    Real.exp (|Real.log (hA.eigenvalues i.1)| * (1 / 2)) *
      ‖vecMulVec (fun x => hA.eigenvectorBasis i.1 x)
        (star (fun x => hA.eigenvectorBasis i.1 x))‖

private theorem powerBound_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : 0 ≤ powerBound hA := by
  unfold powerBound
  exact Finset.sum_nonneg fun _ _ => by positivity

private theorem norm_power_le {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : |z.re| ≤ 1 / 2) : ‖power hA z‖ ≤ powerBound hA := by
  rw [power, supportedFunction_sum]
  exact norm_exp_sum_le _ _ hz

section Physical

variable {a b e : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b] [Fintype e] [DecidableEq e]
  {Φ : QuantumChannel a b} {ρ σ : DensityState a}

variable (M : SupportedRelativeModularModel Φ ρ σ)
variable (W : Matrix (b × e) a ℂ)

private def dilate (W : Matrix (b × e) a ℂ) (X : Matrix a a ℂ) : Matrix (b × e) (b × e) ℂ :=
  W * X * Wᴴ

private theorem dilate_adjoint (X : Matrix a a ℂ) : (dilate W X)ᴴ = dilate W Xᴴ := by
  simp only [dilate, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

private theorem dilate_mul (hW : Wᴴ * W = 1) (X Y : Matrix a a ℂ) :
    dilate W X * dilate W Y = dilate W (X * Y) := by
  simp only [dilate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]

private theorem trace_dilate (hW : Wᴴ * W = 1) (X : Matrix a a ℂ) :
    (dilate W X).trace = X.trace := by
  rw [dilate, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]

private theorem trace_dilate_tensor (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    (dilate W X * tensorId Y).trace = (X * M.data.Ψ Y).trace := by
  rw [trace_tensor_right, hAction, M.tracePair]
  rfl

private theorem trace_compress_tensor (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (X Z : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    (dilate W X * tensorId Y * dilate W Z).trace =
      (Z * X * M.data.Ψ Y).trace := by
  rw [Matrix.trace_mul_comm _ (dilate W Z), ← Matrix.mul_assoc, dilate_mul W hW,
    trace_dilate_tensor M W hAction]

private theorem power_of_support_left {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (E : Matrix n n ℂ) (h : E * A = A) (z : ℂ) :
    E * power hA.1 z = power hA.1 z := by
  have he : A * power hA.1 (z - 1) = power hA.1 z := by
    calc
      _ = power hA.1 1 * power hA.1 (z - 1) :=
        congrArg (· * power hA.1 (z - 1)) (power_one hA).symm
      _ = _ := by rw [power_mul, show (1 : ℂ) + (z - 1) = z by ring]
  rw [← he, ← Matrix.mul_assoc, h]

private def sourceRoot := dilate W (power M.data.hR.1 half)
private def referenceRoot := dilate W (power M.data.hS.1 half)

/-- All three amplitudes are in the original product basis of the dilation.
The input modular phases occur only in the common amplitude. -/
private def commonAmplitude (t : ℝ) :=
  dilate W (power M.data.hS.1 (-(itime t)) * power M.data.hR.1 (half + itime t))

private def lowerAmplitude (t : ℝ) :=
  tensorId (outputProduct M.data (itime t)) * sourceRoot M W

private def upperAmplitude (t : ℝ) :=
  referenceRoot M W * tensorId (outputProduct M.data (half + itime t))

private theorem sourceRoot_selfAdjoint : (sourceRoot M W)ᴴ = sourceRoot M W := by
  rw [sourceRoot, dilate_adjoint, power_conjTranspose, star_half]

private theorem referenceRoot_selfAdjoint : (referenceRoot M W)ᴴ = referenceRoot M W := by
  rw [referenceRoot, dilate_adjoint, power_conjTranspose, star_half]

private theorem sourceRoot_square (hW : Wᴴ * W = 1) :
    sourceRoot M W * sourceRoot M W = dilate W M.data.R := by
  rw [sourceRoot, dilate_mul W hW, power_mul, half_add_half, power_one M.data.hR]

private theorem referenceRoot_square (hW : Wᴴ * W = 1) :
    referenceRoot M W * referenceRoot M W = dilate W M.data.S := by
  rw [referenceRoot, dilate_mul W hW, power_mul, half_add_half, power_one M.data.hS]

private theorem commonAmplitude_unit (hW : Wᴴ * W = 1) (t : ℝ) :
    ‖commonAmplitude M W t‖ ^ 2 = 1 := by
  let D := M.data
  have hS : spectralSupport D.S * D.R = D.R :=
    support_preserves_of_kernel _ _ D.hS D.hR M.inputSupport
  rw [frobenius_sq_trace, Matrix.trace_mul_comm, commonAmplitude, dilate_adjoint,
    dilate_mul W hW, trace_dilate W hW]
  simp only [Matrix.conjTranspose_mul, power_conjTranspose, star_add, star_half, star_it,
    star_neg, neg_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (power D.hS.1 _) (power D.hS.1 _) _, power_mul,
    add_neg_cancel, power_zero D.hS, power_of_support_left D.hR _ hS,
    power_mul, show (half : ℂ) + -(itime t) + (half + itime t) = 1 by
      rw [← half_add_half]; ring, power_one D.hR]
  exact congrArg Complex.re ρ.2.2

private theorem lower_output_gram (t : ℝ) :
    (outputProduct M.data (itime t))ᴴ * outputProduct M.data (itime t) = spectralSupport M.data.T := by
  let D := M.data
  have hT := petz_output_support_projection M
  simp only [outputProduct, Matrix.conjTranspose_mul, power_conjTranspose, star_neg, star_it,
    neg_neg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (qPower D _) (qPower D _) _, power_mul, add_neg_cancel,
    power_zero D.hQ, power_of_support_left D.hT _ hT, power_mul, neg_add_cancel, power_zero D.hT]

private theorem act_source : act Φ M.data.R = M.data.T := rfl
private theorem act_reference : act Φ M.data.S = M.data.Q := rfl

private theorem lowerAmplitude_unit (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (t : ℝ) : ‖lowerAmplitude M W t‖ ^ 2 = 1 := by
  let L := tensorId (e := e) (outputProduct M.data (itime t))
  have hL : Lᴴ * L = tensorId (spectralSupport M.data.T) := by
    dsimp only [L]
    rw [tensorId_adjoint, tensorId_mul (e := e) _ _, lower_output_gram]
  rw [lowerAmplitude, frobenius_sq_trace, Matrix.conjTranspose_mul, sourceRoot_selfAdjoint]
  change ((L * sourceRoot M W) * (sourceRoot M W * Lᴴ)).trace.re = _
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (sourceRoot M W) (sourceRoot M W),
    sourceRoot_square M W hW, ← Matrix.mul_assoc, Matrix.trace_mul_comm _ Lᴴ,
    ← Matrix.mul_assoc Lᴴ L, hL, Matrix.trace_mul_comm, trace_tensor_right, hAction, act_source]
  have hT : M.data.T * spectralSupport M.data.T = M.data.T := by
    calc
      _ = power M.data.hT.1 1 * power M.data.hT.1 0 := by
        rw [power_one M.data.hT, power_zero M.data.hT]
      _ = _ := by rw [power_mul, add_zero, power_one M.data.hT]
  rw [hT, show M.data.T.trace = 1 from (Φ.mapState ρ).2.2, Complex.one_re]

private theorem upperAmplitude_unit (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X)
    (t : ℝ) : ‖upperAmplitude M W t‖ ^ 2 = 1 := by
  let D := M.data
  let Z := outputProduct D (half + itime t)
  have hZ : Z * Zᴴ = qPower D (-(half + itime t)) * D.T * qPower D (-(half - itime t)) := by
    simpa only [star_add, star_half, star_it, sub_eq_add_neg] using outputProduct_gram D t
  rw [upperAmplitude, frobenius_sq_trace, Matrix.conjTranspose_mul, referenceRoot_selfAdjoint]
  change ((referenceRoot M W * tensorId Z) * ((tensorId Z)ᴴ * referenceRoot M W)).trace.re = _
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (tensorId Z), tensorId_adjoint, tensorId_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm _ (referenceRoot M W), ← Matrix.mul_assoc,
    referenceRoot_square M W hW, trace_tensor_right, hAction, act_reference, hZ]
  have hQ : qPower D (-(half - itime t)) * D.Q * qPower D (-(half + itime t)) =
      spectralSupport D.Q := by
    let z₁ := -(half - itime t)
    let z₂ := -(half + itime t)
    change power D.hQ.1 z₁ * D.Q * power D.hQ.1 z₂ = _
    calc
      _ = power D.hQ.1 z₁ * power D.hQ.1 1 * power D.hQ.1 z₂ :=
        congrArg (fun X : Matrix b b ℂ => power D.hQ.1 z₁ * X * power D.hQ.1 z₂)
          (power_one D.hQ).symm
      _ = _ := by
        rw [power_mul, power_mul, show z₁ + 1 + z₂ = 0 by
          dsimp only [z₁, z₂]
          rw [← half_add_half]
          ring, power_zero D.hQ]
  rw [← Matrix.mul_assoc D.Q, Matrix.trace_mul_comm _ (qPower D (-(half - itime t))),
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, petz_output_support_projection M,
    show D.T.trace = 1 from (Φ.mapState ρ).2.2, Complex.one_re]

/-- The canonical supported overlap is the physical trace of the three
positive-spectrum factors. This identifies the cross term on both edges. -/
private theorem overlap_trace (z : ℂ) :
    overlap M.data z =
      (power M.data.hR.1 (1 - z) * power M.data.hS.1 z *
        M.data.Ψ (outputProduct M.data z)).trace := by
  let D := M.data
  let T := D.Ψ (outputProduct D z)
  let Γ := rowFactor D z * T * Ur D * modularPower D.ri (half - z)
  have hΓ (j : D.J) (i : D.I) : Γ j i = amplitude D z (j, i) := by
    rw [amplitude_coordinate M, spectralX_power, exp_ratio j.2 i.2, ← exp_log_half i.2]
    have he : Complex.exp ((Real.log (D.ri i) : ℂ) * (-z)) *
        Complex.exp ((Real.log (D.ri i) : ℂ) * half) =
        Complex.exp ((Real.log (D.ri i) : ℂ) * (half - z)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hmat : Γ = modularPower D.sj z * ((Us D)ᴴ * T * Ur D) *
        modularPower D.ri (half - z) := by
      simp only [Γ, rowFactor, Matrix.mul_assoc]
    rw [hmat]
    simp only [modularPower, Matrix.mul_diagonal, Matrix.diagonal_mul, coordinate_mul]
    change _ = Complex.exp ((Real.log (D.sj j) : ℂ) * z) *
      Complex.exp ((Real.log (D.ri i) : ℂ) * (-z)) *
        (Complex.exp ((Real.log (D.ri i) : ℂ) * half) *
          (star (D.v j) ⬝ᵥ (T *ᵥ D.u i)))
    rw [← he]
    ring
  have hp : overlap D z = ((sourceBlock D)ᴴ * Γ).trace := by
    rw [overlap_eq_pair]
    simp only [dotProduct, Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Pi.star_apply, sourceBlock_apply, hΓ]
    exact Finset.sum_comm
  have hF : (modularPower D.ri (half - z)) * modularPower D.ri half =
      modularPower D.ri (1 - z) := by
    simp only [modularPower, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    rw [← Complex.exp_add]
    congr 1
    rw [← half_add_half]
    ring
  have hHalf : (diagonal (fun i : D.I => (Real.sqrt (D.ri i) : ℂ)))ᴴ =
      modularPower D.ri half := by
    simp only [Matrix.diagonal_conjTranspose, modularPower, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal]
    exact congrArg Matrix.diagonal (funext fun i => by
      change star ((Real.sqrt (D.ri i) : ℂ)) = _
      rw [Complex.star_def, Complex.conj_ofReal, exp_log_half i.2])
  rw [hp]
  calc
    _ = (modularPower D.ri half * ((Ur D)ᴴ * power D.hS.1 z * T * Ur D) *
        modularPower D.ri (half - z)).trace := by
      simp only [Γ, sourceBlock, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHalf]
      have hS := rowFactor_lift D z
      simp only [Matrix.mul_assoc] at hS ⊢
      rw [← hS]
      simp only [Matrix.mul_assoc]
    _ = (modularPower D.ri (1 - z) * (Ur D)ᴴ * power D.hS.1 z * T * Ur D).trace := by
      rw [Matrix.trace_mul_comm _ (modularPower D.ri (half - z))]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (modularPower D.ri (half - z)) (modularPower D.ri half), hF]
    _ = _ := by
      rw [Matrix.trace_mul_comm _ (Ur D)]
      simp only [← Matrix.mul_assoc]
      rfl

/-- On the actual Stinespring product space both Yang numerators are exact
squared distances. The lower amplitude has Hilbert–Schmidt norm-square one because
the marginal is the source output. The upper amplitude has norm-square one
because the reference marginal cancels the inverse powers on its support. -/
private theorem physical_boundary_deficits (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) (t : ℝ) :
    deficit M.data 0 t = ‖commonAmplitude M W t - lowerAmplitude M W t‖ ^ 2 ∧
    deficit M.data (1 / 2) t = ‖commonAmplitude M W t - upperAmplitude M W t‖ ^ 2 := by
  let D := M.data
  have hU : (commonAmplitude M W t)ᴴ =
      dilate W (power D.hR.1 (half - itime t) * power D.hS.1 (itime t)) := by
    rw [commonAmplitude, dilate_adjoint, Matrix.conjTranspose_mul,
      power_conjTranspose, power_conjTranspose, star_add, star_half, star_neg, star_it, neg_neg]
    rw [sub_eq_add_neg]
  constructor
  · rw [sq_sub_of_unit _ _ (commonAmplitude_unit M W hW t) (lowerAmplitude_unit M W hW hAction t),
      deficit, Complex.ofReal_zero, zero_add, hU, lowerAmplitude, sourceRoot,
      ← Matrix.mul_assoc (dilate W _), trace_compress_tensor M W hW hAction, ← Matrix.mul_assoc (power D.hR.1 half),
      power_mul, show (half : ℂ) + (half - itime t) = 1 - itime t by
        rw [← half_add_half]; ring, ← overlap_trace M]
  · rw [sq_sub_of_unit _ _ (commonAmplitude_unit M W hW t) (upperAmplitude_unit M W hW hAction t),
      deficit, hU, upperAmplitude, referenceRoot, ← Matrix.mul_assoc (dilate W _),
      dilate_mul W hW, Matrix.mul_assoc (power D.hR.1 _), power_mul,
      add_comm (itime t) half, trace_dilate_tensor M W hAction,
      show (half : ℂ) - itime t = 1 - (half + itime t) by rw [← half_add_half]; ring, ← overlap_trace M]

private theorem continuous_lifted_outputProduct (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (fun t => tensorId (e := e) (outputProduct M.data (f t))) := by
  apply continuous_matrix
  intro i j
  simp only [tensorId, Matrix.kroneckerMap_apply, outputProduct, qPower, pPower, power,
    supportedFunction, Matrix.mul_apply, Matrix.mul_diagonal]
  fun_prop

private theorem continuous_lowerAmplitude : Continuous (lowerAmplitude M W) :=
  (continuous_lifted_outputProduct (e := e) M (fun t => itime t) (by fun_prop)).mul continuous_const

private def outputSourceColumns := tensorId (e := e) (columns M.data.hT.1)
private def outputReferenceColumns := tensorId (e := e) (columns M.data.hQ.1)

private theorem support_of_sourceRoot (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    (outputSourceColumns M (e := e) * (outputSourceColumns M (e := e))ᴴ) *
      sourceRoot M W = sourceRoot M W := by
  let D := M.data
  have he : spectralSupport D.T = power D.hT.1 0 := (power_zero D.hT).symm
  simp only [outputSourceColumns, tensorId_adjoint, tensorId_mul, columns_support D.hT, matMul]
  refine tensor_projection_of_marginal (e := e) (sourceRoot M W) (spectralSupport D.T) ?_ ?_ ?_
  · rw [he, power_conjTranspose, star_zero]
  · rw [he, power_mul, zero_add]
  · rw [sourceRoot_selfAdjoint, sourceRoot_square M W hW, hAction, act_source, he]
    calc
      _ = power D.hT.1 1 * power D.hT.1 0 := by rw [power_one D.hT]
      _ = _ := by rw [power_mul, add_zero, power_one D.hT]

private theorem support_of_referenceRoot (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    (outputReferenceColumns M (e := e) * (outputReferenceColumns M (e := e))ᴴ) *
      referenceRoot M W = referenceRoot M W := by
  let D := M.data
  have he : spectralSupport D.Q = power D.hQ.1 0 := (power_zero D.hQ).symm
  simp only [outputReferenceColumns, tensorId_adjoint, tensorId_mul, columns_support D.hQ, matMul]
  refine tensor_projection_of_marginal (e := e) (referenceRoot M W) (spectralSupport D.Q) ?_ ?_ ?_
  · rw [he, power_conjTranspose, star_zero]
  · rw [he, power_mul, zero_add]
  · rw [referenceRoot_selfAdjoint, referenceRoot_square M W hW, hAction, act_reference, he]
    calc
      _ = power D.hQ.1 1 * power D.hQ.1 0 := by rw [power_one D.hQ]
      _ = _ := by rw [power_mul, add_zero, power_one D.hQ]

private theorem power_tensor_columns {n : Type u} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    tensorId (e := e) (power hA z) =
      matMul (matMul (tensorId (e := e) (columns hA)) (diagonalPhase
        (((fun i : {i : n // 0 < hA.eigenvalues i} => hA.eigenvalues i.1) ∘ Prod.fst) :
          {i : n // 0 < hA.eigenvalues i} × e → ℝ) z))
        (tensorId (e := e) (columns hA))ᴴ := by
  rw [tensorId_adjoint, ← tensorId_diagonal]
  simp only [matMul, tensorId_mul]
  rfl

set_option maxHeartbeats 900000 in
/-- Each entry of the physical difference is represented in the mixed
reference-left, source-right output eigenbasis, with full environment indices. -/
private theorem physical_mixed_boundary (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) (t : ℝ) :
    let P := outputSourceColumns M (e := e)
    let Q := outputReferenceColumns M (e := e)
    lowerAmplitude M W t - upperAmplitude M W t =
      Q * mixedBoundary M.data.pk M.data.ql (Pᴴ * sourceRoot M W * P)
        (Qᴴ * referenceRoot M W * Q) (Qᴴ * P) t * Pᴴ := by
  dsimp only
  let P : Matrix (b × e) (M.data.K × e) ℂ := outputSourceColumns M (e := e)
  let Q : Matrix (b × e) (M.data.L × e) ℂ := outputReferenceColumns M (e := e)
  let A : Matrix (b × e) (b × e) ℂ := sourceRoot M W
  let B : Matrix (b × e) (b × e) ℂ := referenceRoot M W
  change lowerAmplitude M W t - upperAmplitude M W t = _
  have hA : P * Pᴴ * A = A := support_of_sourceRoot M W hW hAction
  have hAt : A * (P * Pᴴ) = A := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, A, sourceRoot_selfAdjoint]
      using congrArg Matrix.conjTranspose hA
  have hB : Q * Qᴴ * B = B := support_of_referenceRoot M W hW hAction
  have hQ (z : ℂ) : tensorId (e := e) (qPower M.data z) =
      matMul (matMul Q
        (diagonalPhase ((M.data.ql ∘ Prod.fst) : M.data.L × e → ℝ) z)) Qᴴ := power_tensor_columns M.data.hQ.1 z
  have hP (z : ℂ) : tensorId (e := e) (pPower M.data z) =
      matMul (matMul P
        (diagonalPhase ((M.data.pk ∘ Prod.fst) : M.data.K × e → ℝ) z)) Pᴴ := power_tensor_columns M.data.hT.1 z
  have hLift (z : ℂ) : tensorId (e := e) (outputProduct M.data z) =
      matMul (tensorId (e := e) (qPower M.data (-z)))
        (tensorId (e := e) (pPower M.data z)) :=
    (tensorId_mul _ _).symm
  change _ = Q * mixedBoundary M.data.pk M.data.ql (Pᴴ * A * P)
    (Qᴴ * B * Q) (Qᴴ * P) t * Pᴴ
  simp only [lowerAmplitude, upperAmplitude, hLift, hP, hQ, mixedBoundary,
    Matrix.mul_sub, Matrix.sub_mul, neg_add]
  apply congrArg₂ (· - ·)
  · let Qphase : Matrix (M.data.L × e) (M.data.L × e) ℂ :=
      diagonalPhase (M.data.ql ∘ Prod.fst) (-(itime t))
    let Pphase : Matrix (M.data.K × e) (M.data.K × e) ℂ :=
      diagonalPhase (M.data.pk ∘ Prod.fst) (itime t)
    let G : Matrix (b × e) (b × e) ℂ :=
      matMul (matMul (matMul (matMul (matMul Q Qphase) Qᴴ) P) Pphase) Pᴴ
    have h := congrArg (fun Z : Matrix (b × e) (b × e) ℂ => G * Z) hAt
    simpa only [G, Qphase, Pphase, matMul, Matrix.mul_assoc, A] using h.symm
  · let Qphase : Matrix (M.data.L × e) (M.data.L × e) ℂ :=
      diagonalPhase (M.data.ql ∘ Prod.fst) (-half - itime t)
    let Pphase : Matrix (M.data.K × e) (M.data.K × e) ℂ :=
      diagonalPhase (M.data.pk ∘ Prod.fst) (half + itime t)
    have h'' := congrArg (fun Z : Matrix (b × e) (b × e) ℂ =>
      matMul (matMul (matMul (matMul (matMul Z Q) Qphase) Qᴴ) P)
        (matMul Pphase Pᴴ)) hB
    simp only [matMul, Matrix.mul_assoc, B, Qphase, Pphase, sub_eq_add_neg] at h'' ⊢
    exact h''.symm

private theorem physical_mixed_sq (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) (t : ℝ) :
    let P := outputSourceColumns M (e := e)
    let Q := outputReferenceColumns M (e := e)
    ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2 =
      ‖mixedBoundary M.data.pk M.data.ql (Pᴴ * sourceRoot M W * P)
        (Qᴴ * referenceRoot M W * Q) (Qᴴ * P) t‖ ^ 2 := by
  dsimp only
  rw [physical_mixed_boundary M W hW hAction t]
  have hP : (outputSourceColumns M (e := e))ᴴ * outputSourceColumns M (e := e) = 1 :=
    tensorId_isometry (e := e) _ (columns_isometry M.data.hT.1)
  have hQ : (outputReferenceColumns M (e := e))ᴴ * outputReferenceColumns M (e := e) = 1 :=
    tensorId_isometry (e := e) _ (columns_isometry M.data.hQ.1)
  rw [sq_mul_adjoint_isometry _ (by simpa only [one_apply] using hP),
    sq_mul_isometry _ (by simpa only [one_apply] using hQ)]

private theorem lowerAmplitude_zero (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    lowerAmplitude M W 0 = sourceRoot M W := by
  let D := M.data
  have h := support_of_sourceRoot M W hW hAction
  simp only [outputSourceColumns, tensorId_adjoint, tensorId_mul, columns_support D.hT] at h
  have hqp : qPower D 0 * pPower D 0 = spectralSupport D.T := by
    change power D.hQ.1 0 * power D.hT.1 0 = _
    rw [power_zero D.hQ, power_of_support_left D.hT _ (petz_output_support_projection M),
      power_zero D.hT]
  simpa only [lowerAmplitude, outputProduct, Complex.ofReal_zero, zero_mul, neg_zero, hqp] using h

private theorem upperAmplitude_zero_gram
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    upperAmplitude M W 0 * (upperAmplitude M W 0)ᴴ = dilate W (recoveredState M.data) := by
  let D := M.data
  let F := cfc Real.sqrt D.S
  let K := spectralInverseSqrt D.Q
  have hF : (referenceRoot M W) = dilate W F := by rw [referenceRoot, power_half D.hS]
  let L := outputProduct D half
  have hLL : L * Lᴴ = K * D.T * K := by
    have h := outputProduct_gram D 0
    change outputProduct D (half + itime (0 : ℝ)) * (outputProduct D (half + itime (0 : ℝ)))ᴴ =
      qPower D (-(half + itime (0 : ℝ))) * D.T * qPower D (-star (half + itime (0 : ℝ))) at h
    simpa only [L, K, Complex.ofReal_zero, zero_mul, add_zero, star_half, power_neg_half D.hQ] using h
  have hc : (Wᴴ * tensorId (e := e) (K * D.T * K) : Matrix a (b × e) ℂ) * W =
      D.Ψ (K * D.T * K) :=
    compression W M hAction _
  simp only [upperAmplitude, Complex.ofReal_zero, zero_mul, add_zero]
  change (referenceRoot M W * tensorId L) * (referenceRoot M W * tensorId L)ᴴ = _
  rw [Matrix.conjTranspose_mul, referenceRoot_selfAdjoint, Matrix.mul_assoc,
    ← Matrix.mul_assoc (tensorId L), tensorId_adjoint, tensorId_mul, hLL, hF]
  let Lifting := tensorId (e := e) (K * D.T * K)
  let Compression : Matrix a a ℂ := matMul (matMul Wᴴ Lifting) W
  have hComp : Compression = D.Ψ (K * D.T * K) := hc
  calc
    _ = dilate W (F * Compression * F) := by
      simp only [dilate, Compression, Lifting, matMul, Matrix.mul_assoc]
    _ = _ := by
      rw [hComp, recoveredState]
      change dilate W (F * (∑ c, (D.kraus c)ᴴ * (K * D.T * K) * D.kraus c) * F) =
        dilate W (F * (∑ c, ((actual_kraus_representation Φ).kraus c)ᴴ *
          (K * D.T * K) * (actual_kraus_representation Φ).kraus c) * F)
      rw [M.kraus_eq]

private theorem trace_error_le_boundary (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    traceNorm (M.data.R - recoveredState M.data) ^ 2 ≤
      4 * ‖lowerAmplitude M W 0 - upperAmplitude M W 0‖ ^ 2 := by
  let A := lowerAmplitude M W 0
  let B := upperAmplitude M W 0
  have hA : A * Aᴴ = dilate W M.data.R := by
    dsimp only [A]
    rw [lowerAmplitude_zero M W hW hAction, sourceRoot_selfAdjoint, sourceRoot_square M W hW]
  have hB : B * Bᴴ = dilate W (recoveredState M.data) :=
    upperAmplitude_zero_gram M W hAction
  have hAu : ‖A‖ = 1 := by nlinarith [lowerAmplitude_unit M W hW hAction 0, norm_nonneg A]
  have hBu : ‖B‖ = 1 := by nlinarith [upperAmplitude_unit M W hW hAction 0, norm_nonneg B]
  have hTrace : traceNorm (B * Bᴴ - A * Aᴴ) ≤ 2 * ‖A - B‖ := by
    simpa only [hAu, hBu, one_add_one_eq_two, ← neg_sub A B, norm_neg] using
      traceNorm_gram_sub_le A B
  have hIso : traceNorm (B * Bᴴ - A * Aᴴ) = traceNorm (M.data.R - recoveredState M.data) := by
    have hDiff : B * Bᴴ - A * Aᴴ = -(dilate W (M.data.R - recoveredState M.data)) := by
      rw [hA, hB]
      simp only [dilate, Matrix.mul_sub, Matrix.sub_mul, neg_sub]
    rw [hDiff, D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg]
    exact traceNorm_isometry W hW (M.data.R - recoveredState M.data)
  calc
    _ = traceNorm (B * Bᴴ - A * Aᴴ) ^ 2 := by rw [hIso]
    _ ≤ (2 * ‖A - B‖) ^ 2 := pow_le_pow_left₀ (traceNorm_nonneg _) hTrace 2
    _ = _ := by change _ = 4 * ‖A - B‖ ^ 2; ring

private theorem output_rank_le : M.data.T.rank ≤ M.data.Q.rank := by
  let D := M.data
  let C := columns D.hQ.1
  calc
    D.T.rank = ((C * Cᴴ) * D.T).rank := by
      rw [show C * Cᴴ = spectralSupport D.Q from columns_support D.hQ,
        petz_output_support_projection M]
    _ ≤ (C * Cᴴ).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card D.L := (Matrix.rank_mul_le_right C Cᴴ).trans (Matrix.rank_le_card_height _)
    _ = D.Q.rank := card_positive_eigenvalues D.hQ


private def liftCLM : Matrix b b ℂ →L[ℂ] Matrix (b × e) (b × e) ℂ :=
  ({ toFun := tensorId (e := e)
     map_add' := fun X Y => Matrix.add_kronecker X Y _
     map_smul' := fun c X => Matrix.smul_kronecker c X _ } :
      Matrix b b ℂ →ₗ[ℂ] Matrix (b × e) (b × e) ℂ).toContinuousLinearMap

private abbrev dilatedPower {A : Matrix a a ℂ} (hA : A.IsHermitian) (z : ℂ) :=
  dilate W (power hA z)

private def dilateCLM : Matrix a a ℂ →L[ℂ] Matrix (b × e) (b × e) ℂ :=
  ({ toFun := dilate W
     map_add' := fun X Y => by simp only [dilate, Matrix.mul_add, Matrix.add_mul]
     map_smul' := fun c X => by simp only [dilate, Matrix.mul_smul, Matrix.smul_mul,
       RingHom.id_apply] } : Matrix a a ℂ →ₗ[ℂ] Matrix (b × e) (b × e) ℂ).toContinuousLinearMap

private theorem differentiable_dilatedPower {A : Matrix a a ℂ} (hA : A.IsHermitian) :
    Differentiable ℂ (dilatedPower W hA) :=
  (dilateCLM W).differentiable.comp (differentiable_power hA)

private abbrev liftedOutput (z : ℂ) := tensorId (e := e) (outputProduct M.data z)

private abbrev physicalResidual : ℂ → Matrix (b × e) (b × e) ℂ :=
  PetzLogisticMatrixStrip.residual (dilatedPower W M.data.hR.1)
    (dilatedPower W M.data.hS.1) (liftedOutput (e := e) M)

private theorem differentiable_physicalResidual : Differentiable ℂ (physicalResidual M W) := by
  have hO : Differentiable ℂ (liftedOutput (e := e) M) := by
    change Differentiable ℂ (fun z => liftCLM (e := e)
      (qPower M.data (-z) * pPower M.data z))
    exact (liftCLM (e := e)).differentiable.comp
      (((differentiable_power M.data.hQ.1).comp differentiable_neg).mul
        (differentiable_power M.data.hT.1))
  have hR : Differentiable ℂ (fun z : ℂ => dilatedPower W M.data.hR.1 (half - z)) :=
    (differentiable_dilatedPower W M.data.hR.1).comp (by fun_prop)
  unfold physicalResidual PetzLogisticMatrixStrip.residual
  exact (differentiable_const _).sub
    (((differentiable_dilatedPower W M.data.hS.1).mul hO).mul hR)

private theorem bounded_physicalResidual :
    ∃ B : ℝ, ∀ z ∈ PetzLogisticMidline.closedStrip, ‖physicalResidual M W z‖ ≤ B := by
  let D := M.data
  let A := (‖W‖ * powerBound D.hR.1) * ‖Wᴴ‖
  let B := (‖W‖ * powerBound D.hS.1) * ‖Wᴴ‖
  obtain ⟨c, hc, hcBound⟩ := (liftCLM (b := b) (e := e)).bound
  let C := c * (powerBound D.hQ.1 * powerBound D.hT.1)
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (norm_nonneg _) (powerBound_nonneg _)) (norm_nonneg _)
  have hC : 0 ≤ C := mul_nonneg hc.le
    (mul_nonneg (powerBound_nonneg _) (powerBound_nonneg _))
  have bound {H : Matrix a a ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
      ‖dilatedPower W hH z‖ ≤ (‖W‖ * powerBound hH) * ‖Wᴴ‖ :=
    (Matrix.frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_left (norm_power_le hH hz) (norm_nonneg _))) (norm_nonneg _))
  refine ⟨‖dilatedPower W D.hR.1 half‖ + (B * C) * A, fun z hz => ?_⟩
  change 0 ≤ z.re ∧ z.re ≤ 1 / 2 at hz
  have hz' : |z.re| ≤ 1 / 2 := (abs_of_nonneg hz.1).trans_le hz.2
  have hh : |(half - z).re| ≤ 1 / 2 := by
    rw [Complex.sub_re, Complex.ofReal_re, abs_of_nonneg (sub_nonneg.mpr hz.2)]
    linarith [hz.1]
  have hO : ‖liftedOutput (e := e) M z‖ ≤ C := by
    change ‖liftCLM (e := e) (qPower D (-z) * pPower D z)‖ ≤ C
    apply (hcBound _).trans
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply (Matrix.frobenius_norm_mul _ _).trans
    exact mul_le_mul (norm_power_le D.hQ.1 (by simpa only [Complex.neg_re, abs_neg] using hz'))
      (norm_power_le D.hT.1 hz') (norm_nonneg _) (powerBound_nonneg _)
  unfold physicalResidual PetzLogisticMatrixStrip.residual
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  apply (Matrix.frobenius_norm_mul _ _).trans
  exact mul_le_mul ((Matrix.frobenius_norm_mul _ _).trans
      (mul_le_mul (bound D.hS.1 hz') hO (norm_nonneg _) hB))
    (bound D.hR.1 hh) (norm_nonneg _) (mul_nonneg hB hC)

private theorem physical_cross (hW : Wᴴ * W = 1) (t : ℝ) :
    let F := physicalResidual M W
    let X := commonAmplitude M W t - lowerAmplitude M W t
    let Y := commonAmplitude M W t - upperAmplitude M W t
    ((F (PetzLogisticMidline.line (1 / 2) t))ᴴ * F (PetzLogisticMidline.line 0 t)).trace =
      (Yᴴ * X).trace := by
  let D := M.data
  have hS : spectralSupport D.S * D.R = D.R :=
    support_preserves_of_kernel _ _ D.hS D.hR M.inputSupport
  simpa only [physicalResidual, PetzLogisticMatrixStrip.commonAmplitude,
    PetzLogisticMatrixStrip.lowerAmplitude, PetzLogisticMatrixStrip.upperAmplitude,
    commonAmplitude, lowerAmplitude, upperAmplitude, sourceRoot, referenceRoot,
    liftedOutput, dilatedPower, dilate_mul W hW] using
    PetzLogisticMatrixStrip.supported_boundary_cross (dilatedPower W D.hR.1)
      (dilatedPower W D.hS.1) (liftedOutput (e := e) M)
      (fun z w => by rw [dilatedPower, dilatedPower, dilatedPower, dilate_mul W hW, power_mul])
      (fun z w => by rw [dilatedPower, dilatedPower, dilatedPower, dilate_mul W hW, power_mul])
      (fun z => by rw [dilatedPower, dilatedPower, dilate_adjoint, power_conjTranspose])
      (fun z => by rw [dilatedPower, dilatedPower, dilate_adjoint, power_conjTranspose])
      (by rw [dilatedPower, dilatedPower, dilate_mul W hW, power_zero D.hS,
        power_of_support_left D.hR _ hS]) t

private theorem full_logistic_physical (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    (∫ t : ℝ, petzWeight t * ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2) ≤
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
  let U := commonAmplitude M W
  let X (t : ℝ) := U t - lowerAmplitude M W t
  let Y (t : ℝ) := U t - upperAmplitude M W t
  have hDef₀ (t : ℝ) : deficit M.data 0 t = ‖X t‖ ^ 2 :=
    (physical_boundary_deficits M W hW hAction t).1
  have hDef₁ (t : ℝ) : deficit M.data (1 / 2) t = ‖Y t‖ ^ 2 :=
    (physical_boundary_deficits M W hW hAction t).2
  have strip := integral_supported_channel_strip M
  simp only [hDef₀, hDef₁] at strip
  have hU : Continuous U := by
    change Continuous (fun t : ℝ => dilate W
      (power M.data.hS.1 (-(itime t)) * power M.data.hR.1 (half + itime t)))
    exact (dilateCLM W).continuous.comp
      (((differentiable_power M.data.hS.1).continuous.comp
        (show Continuous (fun t : ℝ => -(itime t)) by fun_prop)).mul
       ((differentiable_power M.data.hR.1).continuous.comp
        (show Continuous (fun t : ℝ => half + itime t) by fun_prop)))
  have hX : Integrable (fun t : ℝ => petzWeight t * ‖X t‖ ^ 2) := by
    refine strip.1.mono' ?_ ?_
    · exact (PetzExponentialBoundaryEvaluation.continuous_petzWeight.mul
        ((hU.sub (continuous_lowerAmplitude M W)).norm.pow 2)).aestronglyMeasurable
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg (petzWeight_pos t).le (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (upperWeight_le_lowerWeight ht) (sq_nonneg _)
  obtain ⟨B, hB⟩ := bounded_physicalResidual M W
  have hDiff := differentiable_physicalResidual M W
  have hRemainder := PetzLogisticMatrixStrip.full_logistic_of_boundary_cross
    hDiff.continuous.continuousOn hDiff.differentiableOn hB X Y (physical_cross M W hW)
    strip.1 hX strip.2.1
  dsimp only at hRemainder
  have hYX (t : ℝ) : Y t - X t = lowerAmplitude M W t - upperAmplitude M W t := by
    dsimp only [X, Y]
    abel
  simp only [hYX] at hRemainder
  have hLeft : 0 ≤ ∫ t, (lowerWeight t - petzWeight t) * ‖X t‖ ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
    exact mul_nonneg (sub_nonneg.mpr (upperWeight_le_lowerWeight ht)) (sq_nonneg _)
  have hMid : 0 ≤ ∫ t, PetzLogisticMidline.midlineWeight t *
      ‖physicalResidual M W (PetzLogisticMidline.line (1 / 4) t)‖ ^ 2 := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (by unfold PetzLogisticMidline.midlineWeight; positivity) (sq_nonneg _)
  change ((∫ t, lowerWeight t * ‖X t‖ ^ 2) + ∫ t, petzWeight t * ‖Y t‖ ^ 2) -
      (∫ t, petzWeight t * ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2) =
    (∫ t, (lowerWeight t - petzWeight t) * ‖X t‖ ^ 2) + 2 * (∫ t,
      PetzLogisticMidline.midlineWeight t *
        ‖physicalResidual M W (PetzLogisticMidline.line (1 / 4) t)‖ ^ 2) at hRemainder
  linarith only [strip.2.2, hRemainder, hLeft, hMid]

set_option maxHeartbeats 1000000 in
private theorem trace_sq_le_of_dilation (hW : Wᴴ * W = 1)
    (hAction : ∀ X, partialTraceRight (dilate W X) = act Φ X) :
    traceNorm (M.data.R - recoveredState M.data) ^ 2 ≤
      4 * ((levelCount M.data.pk + levelCount M.data.ql - 1 : ℕ) : ℝ) *
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
  let P := outputSourceColumns M (e := e)
  let Q := outputReferenceColumns M (e := e)
  have hEval := (mixedBoundary_evaluation M.data.pk M.data.ql (Pᴴ * sourceRoot M W * P)
    (Qᴴ * referenceRoot M W * Q) (Qᴴ * P)).2
  have hm (t : ℝ) : ‖mixedBoundary M.data.pk M.data.ql (Pᴴ * sourceRoot M W * P)
      (Qᴴ * referenceRoot M W * Q) (Qᴴ * P) t‖ ^ 2 =
      ‖lowerAmplitude M W t - upperAmplitude M W t‖ ^ 2 :=
    (physical_mixed_sq M W hW hAction t).symm
  change ‖mixedBoundary M.data.pk M.data.ql (Pᴴ * sourceRoot M W * P)
    (Qᴴ * referenceRoot M W * Q) (Qᴴ * P) 0‖ ^ 2 ≤ _ at hEval
  simp only [hm] at hEval
  refine (trace_error_le_boundary M W hW hAction).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (hEval.trans (mul_le_mul_of_nonneg_left (full_logistic_physical M W hW hAction)
      (Nat.cast_nonneg _))) (by norm_num)

end Physical


variable {a b : Type u} [Fintype a] [DecidableEq a] [Nonempty a]
  [Fintype b] [DecidableEq b] [Nonempty b]

/-- The number of distinct positive eigenvalues of a density state. -/
def positiveLevelCount (τ : DensityState b) : ℕ :=
  let h : (CStarMatrix.ofMatrix.symm τ.1).PosSemidef :=
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm τ.2.1).posSemidef
  levelCount (fun i : {i // 0 < h.1.eigenvalues i} => h.1.eigenvalues i.1)

private theorem levelCount_le_card {i : Type*} [Fintype i] (p : i → ℝ) :
    levelCount p ≤ Fintype.card i :=
  Finset.card_image_le.trans_eq Finset.card_univ

set_option maxHeartbeats 1200000 in
/-- The canonical ordinary Petz channel controls the squared trace norm by
`4 * (ν₊(T) + ν₊(Q) - 1)` times the entropy loss, with `ν₊` the number of
distinct positive eigenvalues. This coefficient is at most `4 * (2 * Q.rank - 1)`.
The same channel works for every supported source state. -/
theorem ordinary_petz_traceNorm_sq_le_four_linear_rank
    (Φ : QuantumChannel a b) (σ : DensityState a) :
    let K := (actual_kraus_representation Φ).kraus
    let S := CStarMatrix.ofMatrix.symm σ.1
    let Q := CStarMatrix.ofMatrix.symm (Φ.mapState σ).1
    let H := cfc Real.sqrt S
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    ∃ recovery : QuantumChannel b a,
      (∀ X : Matrix b b ℂ,
        CStarMatrix.ofMatrix.symm
          (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
          (∑ c, H * (K c)ᴴ * W * X * W * K c * H) +
            Matrix.trace ((1 - P) * X) • S) ∧
      recovery.mapState (Φ.mapState σ) = σ ∧
      ∀ ρ : DensityState a, SupportContained ρ σ →
        let Δ := finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
        let error := traceNorm (CStarMatrix.ofMatrix.symm ρ.1 -
          CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1) ^ 2
        error ≤ 4 * ((positiveLevelCount (Φ.mapState ρ) +
          positiveLevelCount (Φ.mapState σ) - 1 : ℕ) : ℝ) * Δ ∧
        error ≤ 4 * ((2 * Q.rank - 1 : ℕ) : ℝ) * Δ := by
  classical
  dsimp only
  obtain ⟨recovery, hAction, hReference, _⟩ :=
    CanonicalPetzEquality.supported_entropy_equality_iff_fixed_petz_recovery Φ σ
  refine ⟨recovery, hAction, hReference, ?_⟩
  intro ρ support
  let M := supported_relative_modular_model Φ ρ σ support
  let D := M.data
  obtain ⟨V, hV, hDilate⟩ := exists_retainedFirst_stinespring Φ
  have he := trace_sq_le_of_dilation M V hV hDilate
  have hP : Matrix.trace ((1 - spectralSupport D.Q) * D.T) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, petz_output_support_projection M, sub_self,
      Matrix.trace_zero]
  have hr := hAction D.T
  rw [hP, zero_smul, add_zero] at hr
  have hRecovered :
      CStarMatrix.ofMatrix.symm (recovery.mapState (Φ.mapState ρ)).1 = recoveredState D := by
    refine hr.trans ?_
    simp only [recoveredState, krausAdjoint, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rw [hRecovered]
  have hLevels : positiveLevelCount (Φ.mapState ρ) + positiveLevelCount (Φ.mapState σ) - 1 ≤
      2 * D.Q.rank - 1 := by
    have hT : levelCount D.pk ≤ D.T.rank :=
      (levelCount_le_card D.pk).trans_eq (card_positive_eigenvalues D.hT)
    have hQ : levelCount D.ql ≤ D.Q.rank :=
      (levelCount_le_card D.ql).trans_eq (card_positive_eigenvalues D.hQ)
    change levelCount D.pk + levelCount D.ql - 1 ≤ _
    have hRank : D.T.rank ≤ D.Q.rank := output_rank_le M
    rw [two_mul]
    exact Nat.sub_le_sub_right (Nat.add_le_add (hT.trans hRank) hQ) 1
  have hΔ : 0 ≤ finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
    have hs := integral_supported_channel_strip M
    rw [← hs.2.2]
    apply add_nonneg
    · exact integral_nonneg (fun t => mul_nonneg
        (div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _)))
        (lower_deficit_nonneg M t))
    · exact integral_nonneg (fun t => mul_nonneg (petzWeight_pos t).le
        (upper_deficit_nonneg M t))
  exact ⟨he, he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hLevels) (by norm_num)) hΔ)⟩

#print axioms ordinary_petz_traceNorm_sq_le_four_linear_rank

end D5.S3.Quantum.Recovery.PetzSupportedLinearRank
