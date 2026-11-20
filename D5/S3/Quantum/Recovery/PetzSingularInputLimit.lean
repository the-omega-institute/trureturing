import D5.S3.Quantum.Recovery.PetzFaithfulDimensionRecovery
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Partial-trace Petz recovery for positive semidefinite inputs

Mix the input with the fixed faithful reference and take the right limit at zero.
The self-log continuity argument is the one used in `UmegakiSupportedNoise`.
The cross-log term is continuous by multiplication by a fixed matrix.
-/

set_option autoImplicit false

noncomputable section

open Matrix Filter
open scoped Topology ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight marginalRight density_posSemidef)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy (finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)
open PetzPhysicalAmplitude (ordinaryPetz lift)
open PetzOverlapEntropyDerivative (faithfulRelativeEntropy entropyLoss)

namespace PetzSingularInputLimit

section MatrixLimits

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mix a matrix with the fixed reference using a real weight. -/
def faithfulMixture (X Y : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  (1 - t) • X + t • Y

@[simp] theorem faithfulMixture_zero (X Y : Matrix n n ℂ) :
    faithfulMixture X Y 0 = X := by
  simp [faithfulMixture]

theorem faithfulMixture_posDef {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosDef)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    (faithfulMixture X Y t).PosDef :=
  Matrix.PosDef.posSemidef_add (hX.smul (sub_nonneg.mpr ht₁)) (hY.smul ht)

theorem trace_faithfulMixture {X Y : Matrix n n ℂ} (hX : X.trace = 1) (hY : Y.trace = 1)
    (t : ℝ) : (faithfulMixture X Y t).trace = 1 := by
  simp only [faithfulMixture, Matrix.trace_add, Matrix.trace_smul, hX, hY,
    Complex.real_smul, mul_one]
  rw [← Complex.ofReal_add, sub_add_cancel, Complex.ofReal_one]

private theorem continuous_faithfulMixture (X Y : Matrix n n ℂ) :
    Continuous (faithfulMixture X Y) := by
  unfold faithfulMixture
  fun_prop

private theorem faithfulMixture_isHermitian {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (t : ℝ) :
    (faithfulMixture X Y t).IsHermitian :=
  (hX.smul (show IsSelfAdjoint (1 - t) from rfl)).add
    (hY.smul (show IsSelfAdjoint t from rfl))

omit [DecidableEq n] in
private theorem continuous_reTrace : Continuous (fun X : Matrix n n ℂ => X.trace.re) := by
  unfold Matrix.trace
  fun_prop

-- The finite spectrum allows the factor Real.log even when zero is an eigenvalue.
private theorem self_log_eq_cfc {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    X * cfc Real.log X = cfc (fun x : ℝ => x * Real.log x) X := by
  symm
  change cfc (fun x : ℝ => id x * Real.log x) X = _
  rw [cfc_mul id Real.log X continuousOn_id (X.finite_real_spectrum.continuousOn _)]
  change cfc (fun x : ℝ => x) X * cfc Real.log X = _
  rw [cfc_id' ℝ X hX.isSelfAdjoint]

/-- The finite trace-log expression is continuous along a Hermitian path with a fixed
reference. In particular, the first argument may have zero eigenvalues. -/
theorem continuous_fixedReference_traceLog {T : Type*} [TopologicalSpace T]
    {X : T → Matrix n n ℂ} (hX : Continuous X) (hHerm : ∀ t, (X t).IsHermitian)
    (Y : Matrix n n ℂ) :
    Continuous (fun t => faithfulRelativeEntropy (X t) Y) := by
  have hSelf : Continuous (fun t => cfc (fun x : ℝ => x * Real.log x) (X t)) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := Set.univ)
      (by simp (config := { congrConsts := false })) hX
      (fun t => (hHerm t).isSelfAdjoint) Real.continuous_mul_log.continuousOn
  have hCross : Continuous (fun t => X t * cfc Real.log Y) :=
    hX.mul continuous_const
  have hFormula (t : T) : faithfulRelativeEntropy (X t) Y =
      (cfc (fun x : ℝ => x * Real.log x) (X t)).trace.re -
        (X t * cfc Real.log Y).trace.re := by
    rw [faithfulRelativeEntropy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
      self_log_eq_cfc (hHerm t)]
  simp only [hFormula]
  exact (continuous_reTrace.comp hSelf).sub (continuous_reTrace.comp hCross)

/-- The actual trace-log value at the unregularized input is the right limit. -/
theorem tendsto_fixedReference_traceLog_faithfulMixture {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Tendsto (fun t => faithfulRelativeEntropy (faithfulMixture X Y t) Y)
      (𝓝[>] (0 : ℝ)) (𝓝 (faithfulRelativeEntropy X Y)) := by
  have h := continuous_fixedReference_traceLog (continuous_faithfulMixture X Y)
    (faithfulMixture_isHermitian hX hY) Y
  simpa only [faithfulMixture_zero] using
    (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

private theorem continuous_traceNorm :
    Continuous (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm : Matrix n n ℂ → ℝ) := by
  have hGram : Continuous (fun X : Matrix n n ℂ => Xᴴ * X) := by fun_prop
  have hSqrt : Continuous (fun X : Matrix n n ℂ => cfc Real.sqrt (Xᴴ * X)) :=
    Continuous.cfc_of_mem_nhdsSet Real.sqrt (s := Set.univ)
      (by simp (config := { congrConsts := false })) hGram
      (fun X => (Matrix.isHermitian_conjTranspose_mul_self X).isSelfAdjoint)
      Real.continuous_sqrt.continuousOn
  have hFormula (X : Matrix n n ℂ) :
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm X =
        (cfc Real.sqrt (Xᴴ * X)).trace.re := by
    change (CFC.sqrt (Xᴴ * X)).trace.re = _
    rw [CFC.sqrt_eq_real_sqrt (Xᴴ * X) X.posSemidef_conjTranspose_mul_self.nonneg,
      cfcₙ_eq_cfc (a := Xᴴ * X) Real.continuous_sqrt.continuousOn Real.sqrt_zero]
  rw [funext hFormula]
  exact continuous_reTrace.comp hSqrt

open scoped CStarAlgebra in
/-- The raw formula used in the faithful theorem is the canonical finite trace-log
branch on density matrices, including singular inputs. -/
theorem finiteTraceLog_eq_raw (X Y : DensityState n) :
    finiteTraceLogRelativeEntropy X Y =
      faithfulRelativeEntropy (CStarMatrix.ofMatrix.symm X.1) (CStarMatrix.ofMatrix.symm Y.1) := by
  have mapLog (M : Matrix n n ℂ) (hM : M.IsHermitian) :
      CStarMatrix.ofMatrix (cfc Real.log M) = CFC.log (CStarMatrix.ofMatrix M) :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous
      hM.isSelfAdjoint hM.isSelfAdjoint
  let U := CStarMatrix.ofMatrix.symm X.1
  let V := CStarMatrix.ofMatrix.symm Y.1
  change (CStarMatrix.ofMatrix U * (CFC.log (CStarMatrix.ofMatrix U) -
    CFC.log (CStarMatrix.ofMatrix V)) : CStarMatrix n n ℂ).trace.re = _
  rw [← mapLog U (density_posSemidef X).isHermitian,
    ← mapLog V (density_posSemidef Y).isHermitian] <;> rfl

end MatrixLimits

section Recovery

universe u

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {ρ σ : Matrix (A × B) (A × B) ℂ}

private theorem continuous_partialTraceRight :
    Continuous (partialTraceRight : Matrix (A × B) (A × B) ℂ → Matrix A A ℂ) := by
  apply continuous_matrix
  intro i j
  unfold partialTraceRight
  exact continuous_finsetSum _ fun b _ => continuous_apply_apply (i, b) (j, b)

private theorem partialTraceRight_isHermitian {X : Matrix (A × B) (A × B) ℂ}
    (hX : X.IsHermitian) : (partialTraceRight X).IsHermitian := by
  ext i j
  simp only [partialTraceRight, Matrix.conjTranspose_apply, star_sum]
  exact Finset.sum_congr rfl fun b _ => hX.apply (i, b) (j, b)

private theorem continuous_lift :
    Continuous (lift (A := A) (B := B)) := by
  apply continuous_matrix
  rintro ⟨i, b⟩ ⟨j, d⟩
  simp only [lift, Matrix.kronecker_apply]
  exact (continuous_apply_apply i j).mul continuous_const

private theorem continuous_ordinaryPetz (σ : Matrix (A × B) (A × B) ℂ) :
    Continuous (ordinaryPetz σ) := by
  let Q := spectralInverseSqrt (partialTraceRight σ)
  have hSandwich : Continuous (fun p : Matrix A A ℂ => Q * p * Q) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hLift := (continuous_lift (A := A) (B := B)).comp hSandwich
  change Continuous (fun p => cfc Real.sqrt σ * lift (Q * p * Q) * cfc Real.sqrt σ)
  exact (continuous_const.mul hLift).mul continuous_const

/-- At fixed reference, the trace norm of the ordinary Petz error is continuous
as a function of the raw input matrix. -/
theorem continuous_traceNorm_ordinaryPetz_error (σ : Matrix (A × B) (A × B) ℂ) :
    Continuous (fun X : Matrix (A × B) (A × B) ℂ =>
      traceNorm (X - ordinaryPetz σ (partialTraceRight X))) :=
  continuous_traceNorm.comp
    (continuous_id.sub ((continuous_ordinaryPetz σ).comp continuous_partialTraceRight))

private theorem continuous_entropyLoss_faithfulMixture (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) : Continuous (fun t => entropyLoss (faithfulMixture ρ σ t) σ) := by
  have hMixture := continuous_faithfulMixture ρ σ
  have hHerm (t : ℝ) := faithfulMixture_isHermitian hρ hσ t
  exact (continuous_fixedReference_traceLog hMixture hHerm σ).sub
    (continuous_fixedReference_traceLog (continuous_partialTraceRight.comp hMixture)
      (fun t => partialTraceRight_isHermitian (hHerm t)) (partialTraceRight σ))

/-- The squared trace norm of the ordinary Petz error for a PSD trace-one input is bounded
by `8 * (1 + (card A)^2)` times the actual full-minus-marginal trace-log defect. -/
theorem traceNorm_sub_ordinaryPetz_sq_le (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (hρtrace : ρ.trace = 1) (hσtrace : σ.trace = 1) :
    traceNorm (ρ - ordinaryPetz σ (partialTraceRight ρ)) ^ 2 ≤
      (8 * (1 + (Fintype.card A : ℝ) ^ 2)) * entropyLoss ρ σ := by
  let ρₜ := faithfulMixture ρ σ
  let c : ℝ := 8 * (1 + (Fintype.card A : ℝ) ^ 2)
  have hMixture : Continuous ρₜ := continuous_faithfulMixture ρ σ
  have hLeft : Continuous (fun t =>
      traceNorm (ρₜ t - ordinaryPetz σ (partialTraceRight (ρₜ t))) ^ 2) :=
    ((continuous_traceNorm_ordinaryPetz_error σ).comp hMixture).pow 2
  have hRight : Continuous (fun t => c * entropyLoss (ρₜ t) σ) :=
    continuous_const.mul (continuous_entropyLoss_faithfulMixture
      hρ.isHermitian hσ.isHermitian)
  have hLeftLim : Tendsto
      (fun t => traceNorm (ρₜ t - ordinaryPetz σ (partialTraceRight (ρₜ t))) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (traceNorm (ρ - ordinaryPetz σ (partialTraceRight ρ)) ^ 2)) := by
    simpa only [ρₜ, faithfulMixture_zero] using
      (hLeft.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hRightLim : Tendsto (fun t => c * entropyLoss (ρₜ t) σ) (𝓝[>] (0 : ℝ))
      (𝓝 (c * entropyLoss ρ σ)) := by
    simpa only [ρₜ, faithfulMixture_zero] using
      (hRight.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  letI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  apply le_of_tendsto_of_tendsto hLeftLim hRightLim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  exact PetzFaithfulDimensionRecovery.traceNorm_sub_ordinaryPetz_sq_le
    (faithfulMixture_posDef hρ hσ ht.1 ht.2.le) hσ
    (trace_faithfulMixture hρtrace hσtrace t)

open scoped CStarAlgebra in
/-- The same bound stated with the canonical finite trace-log relative entropy for the
two density states and their actual marginals. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_finiteTraceLog (X Y : DensityState (A × B))
    (hY : (CStarMatrix.ofMatrix.symm Y.1).PosDef) :
    traceNorm (CStarMatrix.ofMatrix.symm X.1 -
        ordinaryPetz (CStarMatrix.ofMatrix.symm Y.1)
          (partialTraceRight (CStarMatrix.ofMatrix.symm X.1))) ^ 2 ≤
      (8 * (1 + (Fintype.card A : ℝ) ^ 2)) *
        (finiteTraceLogRelativeEntropy X Y -
          finiteTraceLogRelativeEntropy (marginalRight X) (marginalRight Y)) := by
  rw [finiteTraceLog_eq_raw X Y, finiteTraceLog_eq_raw (marginalRight X) (marginalRight Y)]
  exact traceNorm_sub_ordinaryPetz_sq_le (density_posSemidef X) hY X.2.2 Y.2.2

end Recovery

end PetzSingularInputLimit
