import D5.S3.Quantum.Recovery.PetzPhysicalAmplitude
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The derivative of the physical Petz overlap

Differentiate the complex powers of the verified amplitude on their faithful
Hermitian spectra. Cyclicity of trace and right partial-trace duality identify
the complex derivative of the overlap at zero with a difference of trace-log
expressions. Its real part is the negative Umegaki entropy loss.
-/

set_option autoImplicit false

noncomputable section

open Matrix PetzPhysicalAmplitude
open scoped ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)

namespace PetzOverlapEntropyDerivative

universe u

section SpectralPower

variable {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}

/-- For a fixed positive base, complex exponentiation differentiates in the exponent. -/
theorem hasDerivAt_positive_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (x : ℂ) ^ w)
      ((x : ℂ) ^ z * (Real.log x : ℂ)) z := by
  have hx₀ : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simpa only [Complex.cpow_def_of_ne_zero hx₀, ← Complex.ofReal_log hx.le, mul_one]
    using ((hasDerivAt_id' z).const_mul (Real.log x : ℂ)).cexp

private def spectralDiagonalCLM (hX : X.PosDef) : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    ((Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary).toAlgEquiv.toLinearMap.comp
      (Matrix.diagonalLinearMap n ℂ ℂ))

private theorem spectralDiagonalCLM_apply (hX : X.PosDef) (d : n → ℂ) :
    spectralDiagonalCLM hX d =
      Unitary.conjStarAlgAut ℂ _ hX.isHermitian.eigenvectorUnitary (Matrix.diagonal d) :=
  rfl

/-- The actual Hermitian spectral complex power has this derivative at every exponent. -/
theorem hasDerivAt_spectralCPow (hX : X.PosDef) (z : ℂ) :
    HasDerivAt (spectralCPow hX) (spectralCPow hX z * cfc Real.log X) z := by
  have hEigen :
      HasDerivAt (fun w : ℂ => fun i : n => (hX.isHermitian.eigenvalues i : ℂ) ^ w)
        (fun i : n => (hX.isHermitian.eigenvalues i : ℂ) ^ z *
          (Real.log (hX.isHermitian.eigenvalues i) : ℂ)) z :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_positive_cpow (hX.eigenvalues_pos i) z)
  have hd := (spectralDiagonalCLM hX).hasFDerivAt.comp_hasDerivAt z hEigen
  simpa only [Function.comp_def, spectralDiagonalCLM_apply, spectralCPow,
    hX.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, RCLike.ofReal_eq_complex_ofReal,
    ← map_mul, Matrix.diagonal_mul_diagonal] using! hd

private theorem hasDerivAt_spectralCPow_const_sub (hX : X.PosDef) (c : ℂ) :
    HasDerivAt (fun z : ℂ => spectralCPow hX (c - z))
      (-(spectralCPow hX c * cfc Real.log X)) 0 := by
  have hd := (hasDerivAt_spectralCPow hX (c - 0)).scomp 0
    ((hasDerivAt_id' (0 : ℂ)).const_sub c)
  simpa only [Function.comp_def, sub_zero, neg_smul, one_smul] using hd

private theorem sqrt_mul_sqrt (hX : X.PosDef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hhalf : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Complex.ofReal_one]
  rw [← spectralCPow_half hX, spectralCPow_mul, hhalf, spectralCPow_one]

private theorem trace_sqrt_mul_mul_sqrt (hX : X.PosDef) (M : Matrix n n ℂ) :
    (cfc Real.sqrt X * (M * cfc Real.sqrt X)).trace = (X * M).trace := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, sqrt_mul_sqrt hX]

/-- The faithful Umegaki trace formula on finite matrices. -/
def faithfulRelativeEntropy (X Y : Matrix n n ℂ) : ℝ :=
  (X * (cfc Real.log X - cfc Real.log Y)).trace.re

end SpectralPower

section PartialTrace

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {ρ σ : Matrix (A × B) (A × B) ℂ}

private def liftCLM : Matrix A A ℂ →L[ℂ] Matrix (A × B) (A × B) ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.kroneckerBilinear (R := ℂ)).flip (1 : Matrix B B ℂ))

private theorem liftCLM_apply (X : Matrix A A ℂ) :
    liftCLM (B := B) X = lift (B := B) X :=
  rfl

private theorem lift_one : lift (B := B) (1 : Matrix A A ℂ) = 1 := by
  unfold lift
  exact Matrix.one_kronecker_one

private theorem trace_mul_lift (Y : Matrix (A × B) (A × B) ℂ) (K : Matrix A A ℂ) :
    (Y * lift K).trace = (partialTraceRight Y * K).trace := by
  calc
    _ = (lift K * Y).trace := Matrix.trace_mul_comm _ _
    _ = (K * partialTraceRight Y).trace := trace_lift_mul K Y
    _ = _ := Matrix.trace_mul_comm _ _

/-- Input Umegaki relative entropy minus the relative entropy of the actual marginals. -/
def entropyLoss (ρ σ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  faithfulRelativeEntropy ρ σ -
    faithfulRelativeEntropy (partialTraceRight ρ) (partialTraceRight σ)

variable [Nonempty B]

/-- The trace overlap with the positive square root of the input. -/
def overlap (hρ : ρ.PosDef) (hσ : σ.PosDef) (z : ℂ) : ℂ :=
  (cfc Real.sqrt ρ * gamma hρ hσ z).trace

theorem overlap_zero_eq_trace (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    overlap hρ hσ 0 = ρ.trace := by
  simp only [overlap, gamma, neg_zero, spectralCPow_zero, one_mul, lift_one, sub_zero,
    spectralCPow_half, sqrt_mul_sqrt hρ]

theorem overlap_zero (hρ : ρ.PosDef) (hσ : σ.PosDef) (htrace : ρ.trace = 1) :
    overlap hρ hσ 0 = 1 :=
  (overlap_zero_eq_trace hρ hσ).trans htrace

/-- The derivative of the verified amplitude, with the marginal derivative lifted by tensoring
with the identity. -/
theorem hasDerivAt_gamma_zero (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    HasDerivAt (gamma hρ hσ)
      ((cfc Real.log σ +
          lift (cfc Real.log (partialTraceRight ρ) - cfc Real.log (partialTraceRight σ))) *
        cfc Real.sqrt ρ - cfc Real.sqrt ρ * cfc Real.log ρ) 0 := by
  let hp := partialTraceRight_posDef (R := A) (a := B) ρ hρ
  let hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  let K := cfc Real.log (partialTraceRight ρ) - cfc Real.log (partialTraceRight σ)
  have hσ' : HasDerivAt (spectralCPow hσ) (cfc Real.log σ) 0 := by
    simpa only [spectralCPow_zero, one_mul] using hasDerivAt_spectralCPow hσ 0
  have hp' : HasDerivAt (spectralCPow hp) (cfc Real.log (partialTraceRight ρ)) 0 := by
    simpa only [spectralCPow_zero, one_mul] using hasDerivAt_spectralCPow hp 0
  have hq' : HasDerivAt (fun z : ℂ => spectralCPow hq (-z))
      (-(cfc Real.log (partialTraceRight σ))) 0 := by
    simpa only [zero_sub, spectralCPow_zero, one_mul] using
      hasDerivAt_spectralCPow_const_sub hq 0
  have hRetained :
      HasDerivAt (fun z : ℂ => spectralCPow hq (-z) * spectralCPow hp z) K 0 := by
    dsimp only [K]
    rw [sub_eq_add_neg, add_comm]
    simpa only [Pi.mul_apply, neg_zero, spectralCPow_zero, one_mul, mul_one] using!
      hq'.mul hp'
  have hLift :
      HasDerivAt (fun z : ℂ => lift (B := B) (spectralCPow hq (-z) * spectralCPow hp z))
        (lift (B := B) K) 0 := by
    simpa only [Function.comp_def, liftCLM_apply] using
      (liftCLM (A := A) (B := B)).hasFDerivAt.comp_hasDerivAt 0 hRetained
  have hOuter :
      HasDerivAt (fun z : ℂ => spectralCPow hσ z *
        lift (spectralCPow hq (-z) * spectralCPow hp z)) (cfc Real.log σ + lift K) 0 := by
    simpa only [Pi.mul_apply, neg_zero, spectralCPow_zero, one_mul, mul_one, lift_one]
      using! hσ'.mul hLift
  have hTail : HasDerivAt (fun z : ℂ => spectralCPow hρ (((1 / 2 : ℝ) : ℂ) - z))
      (-(cfc Real.sqrt ρ * cfc Real.log ρ)) 0 := by
    simpa only [spectralCPow_half] using
      hasDerivAt_spectralCPow_const_sub hρ ((1 / 2 : ℝ) : ℂ)
  simpa only [gamma, hp, hq, K, Pi.mul_apply, neg_zero, spectralCPow_zero, sub_zero,
    one_mul, mul_one, lift_one, spectralCPow_half, Matrix.mul_neg, ← sub_eq_add_neg]
      using! hOuter.mul hTail

/-- The trace derivative at zero, as a complex difference of actual trace-log expressions. -/
theorem hasDerivAt_overlap_zero (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    HasDerivAt (overlap hρ hσ)
      (-((ρ * (cfc Real.log ρ - cfc Real.log σ)).trace -
        (partialTraceRight ρ *
          (cfc Real.log (partialTraceRight ρ) - cfc Real.log (partialTraceRight σ))).trace)) 0 := by
  let S := cfc Real.sqrt ρ
  let K := cfc Real.log (partialTraceRight ρ) - cfc Real.log (partialTraceRight σ)
  let H := cfc Real.log σ + lift K
  let tr : Matrix (A × B) (A × B) ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap (A × B) ℂ ℂ).toContinuousLinearMap
  have hd := tr.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_gamma_zero hρ hσ).const_mul S)
  change HasDerivAt (overlap hρ hσ) (S * (H * S - S * cfc Real.log ρ)).trace 0 at hd
  have hTrace :
      (S * (H * S - S * cfc Real.log ρ)).trace =
        -((ρ * (cfc Real.log ρ - cfc Real.log σ)).trace -
          (partialTraceRight ρ * K).trace) := by
    calc
      _ = (ρ * H).trace - (ρ * cfc Real.log ρ).trace := by
        dsimp only [S]
        rw [Matrix.mul_sub, Matrix.trace_sub, trace_sqrt_mul_mul_sqrt hρ H,
          ← Matrix.mul_assoc, sqrt_mul_sqrt hρ]
      _ = (ρ * cfc Real.log σ).trace + (partialTraceRight ρ * K).trace -
          (ρ * cfc Real.log ρ).trace := by
        dsimp only [H]
        rw [Matrix.mul_add, Matrix.trace_add, trace_mul_lift]
      _ = _ := by
        rw [Matrix.mul_sub ρ, Matrix.trace_sub]
        ring
  rw [hTrace] at hd
  exact hd

/-- The real part of the overlap derivative equals minus the faithful Umegaki loss. -/
theorem overlap_deriv_zero_re (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    (deriv (overlap hρ hσ) 0).re = -entropyLoss ρ σ := by
  rw [(hasDerivAt_overlap_zero hρ hσ).deriv]
  simp only [Complex.neg_re, Complex.sub_re, entropyLoss, faithfulRelativeEntropy]

end PartialTrace

end PetzOverlapEntropyDerivative
