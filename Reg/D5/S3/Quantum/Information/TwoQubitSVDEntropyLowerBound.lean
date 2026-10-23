import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
open _root_.D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
open _root_.D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
open _root_.D5.S3.Quantum.Matrix.CartesianVariance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

private theorem svd_hermitian (T : QubitMatrix) : (svdDensity T).IsHermitian :=
  ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))).smul
    (inv_nonneg.mpr (Complex.nonneg_iff.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Tᴴ * T))).trace_nonneg).1)).isHermitian

/-- Observe the SVD entropy as Alice's coefficient matrix varies at fixed Bob matrix. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature QubitMatrix (fun _ => QubitMatrix) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ B A => spectralEntropy (svd_hermitian (reducedTransition A B)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B : QubitMatrix),
    RHLinalg.frobSq A = 1 → RHLinalg.frobSq B = 1 → reducedTransition A B ≠ 0 →
    min
      (spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd A)).isHermitian)
      (spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd B)).isHermitian)
      ≤ R.readout () B A

private theorem transition_mul (A B : QubitMatrix) : reducedTransition A B = A * Bᴴ := by
  ext i j
  simp only [reducedTransition, partialTraceRight, Matrix.vecMulVec, Function.uncurry,
    Pi.star_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

private theorem entropy_det_zero (τ : QubitMatrix) (hτ : τ.PosSemidef)
    (ht : τ.trace = 1) (hd : τ.det.re = 0) : spectralEntropy hτ.isHermitian = 0 := by
  have he := qubit_entropy_det τ hτ ht
  rw [S, dif_pos hτ.isHermitian, hd] at he
  norm_num [_root_.D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb] at he
  exact he

private abbrev product : QubitMatrix := Matrix.diagonal ![1, 0]

private theorem product_psd : product.PosSemidef :=
  Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> simp)

private theorem product_mul : product * productᴴ = product := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [product, Matrix.mul_apply, Fin.sum_univ_two]

private theorem product_entropy :
    spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd product)).isHermitian = 0 := by
  have he := entropy_det_zero product product_psd
    (by norm_num [product, Matrix.trace_fin_two])
    (by norm_num [product, Matrix.det_fin_two])
  have hm : partialTraceRight (pureCoupling product) = product := by
    rw [ptrace2_pure, product_mul]
  simpa only [hm] using he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : RHLinalg.frobSq product = 1 := by
    norm_num [frobSq_eq_sum, product, Fin.sum_univ_two]
  have ht : reducedTransition product product ≠ 0 := by
    rw [transition_mul, product_mul]
    intro he
    have hc := congrArg (fun M : QubitMatrix => M 0 0) he
    norm_num [product] at hc
  have he := h product product hn hn ht
  change min
    (spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd product)).isHermitian)
    (spectralEntropy (partialTraceRight_posSemidef (pureCoupling_psd product)).isHermitian)
    ≤ (-1 : ℝ) at he
  rw [product_entropy] at he
  norm_num at he

private theorem entropy_svd_zero : spectralEntropy (svd_hermitian 0) = 0 := by
  have hm : svdDensity (0 : QubitMatrix) = 0 := by simp [svdDensity]
  have he := (svd_hermitian 0).eigenvalues_eq_zero_iff.mpr hm
  simp only [spectralEntropy, he, Pi.zero_apply, Real.negMulLog_zero, Finset.sum_const_zero]

private theorem entropy_svd_one : spectralEntropy (svd_hermitian 1) = Real.log 2 := by
  have hm : svdDensity (1 : QubitMatrix) = (1 / 2 : ℝ) • (1 : QubitMatrix) := by
    norm_num [svdDensity, Matrix.trace_one]
  have hp : ((1 / 2 : ℝ) • (1 : QubitMatrix)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by norm_num)
  have ht : ((1 / 2 : ℝ) • (1 : QubitMatrix)).trace = 1 := by
    norm_num [Matrix.trace_smul, Matrix.trace_one]
  have hd : ((1 / 2 : ℝ) • (1 : QubitMatrix)).det.re = 1 / 4 := by
    norm_num [Matrix.det_smul_of_tower]
  have he := qubit_entropy_det _ hp ht
  rw [S, dif_pos hp.isHermitian, hd] at he
  have hz : Real.log 2 ≠ 0 := by positivity
  norm_num [_root_.D5.S3.Quantum.CloningMachine.binaryEntropyBits, Real.logb,
    Real.log_inv, neg_div, hz] at he
  have he' : spectralEntropy hp.isHermitian = Real.log 2 := by
    have hh := (div_eq_iff hz).mp he
    field_simp [hz] at hh
    rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at hh
    linarith only [hh]
  simpa only [hm] using he'

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change spectralEntropy (svd_hermitian (reducedTransition 0 1)) ≠
    spectralEntropy (svd_hermitian (reducedTransition 1 1))
  have h0 : reducedTransition (0 : QubitMatrix) 1 = 0 := by simp [transition_mul]
  have h1 : reducedTransition (1 : QubitMatrix) 1 = 1 := by simp [transition_mul]
  simpa only [h0, h1, entropy_svd_zero, entropy_svd_one] using
    (ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.unit
  realizationName := `Reg.D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ B A => spectralEntropy (svd_hermitian (reducedTransition A B)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
    definition := some {
      owner := `D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
      name := `D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.claim
      path := #[] }
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound
