import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Calculus.Deriv.Abs

open _root_.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
open _root_.D5.S3.Quantum.Matrix.StolarskyMean
open _root_.D5.S3.Analytic.Fourier.SinhLogIntegral
open _root_.D5.S3.Analytic.Fourier.PositiveDefinite
open _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder ContDiff

noncomputable section
namespace Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor

abbrev smoothSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

abbrev familySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℂ)

def factorActual : Realization familySignature :=
  realize familySignature (fun _ _ p t => (factor p t : ℂ)) (fun e => nomatch e)

def defectActual : Realization familySignature :=
  realize familySignature (fun _ _ γ t => (Reduction.f γ t : ℂ)) (fun e => nomatch e)

def negativeFamily : Realization familySignature :=
  realize familySignature (fun _ _ _ _ => -1) (fun e => nomatch e)

private theorem factor_one_one : factor 1 1 = 0 := by
  have hs : Real.sinh 1 ≠ 0 := by simp
  simp [factor, SecondDifference.Q, phi, E, hs]

private theorem factor_two_one_pos : 0 < factor 2 1 := by
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
  have hc : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr (by norm_num)
  have hc0 := Real.cosh_pos 1
  have hsn : Real.sinh 2 = 2 * Real.sinh 1 * Real.cosh 1 := by
    simpa using Real.sinh_two_mul 1
  have hratio : E 1 1 / E 2 1 = 1 / Real.cosh 1 := by
    norm_num [E]
    rw [hsn]
    field_simp
    <;> ring
  have hphi : phi 2 1 < 1 := by
    rw [phi, hratio]
    exact pow_lt_one₀ (by positivity) ((div_lt_one hc0).mpr hc) (by norm_num)
  have he1 : 0 < E 1 1 := by simpa [E] using hs
  unfold factor
  apply mul_pos
  · exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
      (sq_pos_of_pos (inv_pos.mpr he1))
  · simpa [SecondDifference.Q, phi, E] using sub_pos.mpr hphi

private theorem defect_two_one : Reduction.f 2 1 = 0 := by
  rw [f_eq_factor (by norm_num : (2 : ℝ) ≤ 2)]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  exact factor_one_one

private theorem defect_three_one_pos : 0 < Reduction.f 3 1 := by
  rw [f_eq_factor (by norm_num : (2 : ℝ) ≤ 3)]
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num]
  exact factor_two_one_pos

private theorem factorDependence : ObservationalDependence familySignature factorActual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  intro he
  have h := congrFun he 1
  change (factor 1 1 : ℂ) = (factor 2 1 : ℂ) at h
  have hr := Complex.ofReal_injective h
  rw [factor_one_one] at hr
  exact factor_two_one_pos.ne' hr.symm

private theorem defectDependence : ObservationalDependence familySignature defectActual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  intro he
  have h := congrFun he 1
  change (Reduction.f 2 1 : ℂ) = (Reduction.f 3 1 : ℂ) at h
  have hr := Complex.ofReal_injective h
  rw [defect_two_one] at hr
  exact defect_three_one_pos.ne' hr.symm

abbrev factorArena : Arena where
  signature := familySignature
  Law R := ∀ {p : ℝ}, 1 ≤ p → PositiveDefinite (R.readout () () p)

abbrev defectArena : Arena where
  signature := familySignature
  Law R := ∀ {γ : ℝ}, 2 ≤ γ → PositiveDefinite (R.readout () () γ)

private theorem factor_rejected : ¬ factorArena.Law negativeFamily := by
  intro H
  have h := (H (p := 1) le_rfl 1 (fun _ => 0)).diag_nonneg (i := 0)
  norm_num [negativeFamily, realize] at h

private theorem defect_rejected : ¬ defectArena.Law negativeFamily := by
  intro H
  have h := (H (γ := 2) le_rfl 1 (fun _ => 0)).diag_nonneg (i := 0)
  norm_num [negativeFamily, realize] at h

def factorSource : Registration factorArena (type_of% @factor_positiveDefinite) where
  actual := factorActual
  bridge := Iff.rfl
  variation := ⟨factor_positiveDefinite, negativeFamily, factor_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    factorArena.Law factorActual negativeFamily factor_rejected
  dependence := factorDependence

def defectSource : Registration defectArena (type_of% @positiveDefinite_f) where
  actual := defectActual
  bridge := Iff.rfl
  variation := ⟨positiveDefinite_f, negativeFamily, defect_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    defectArena.Law defectActual negativeFamily defect_rejected
  dependence := defectDependence

def factorAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@factor_positiveDefinite) (Realization familySignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor.factorUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor.factorSource
  realizationSource := none
  generated := false
  arena := .source ⟨factorArena⟩
  objectArena := .source ⟨factorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source factorArena ⟨factorSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize familySignature (fun _ _ p t => (factor p t : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms factorAudit

def defectAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@positiveDefinite_f) (Realization familySignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor.defectUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor.defectSource
  realizationSource := none
  generated := false
  arena := .source ⟨defectArena⟩
  objectArena := .source ⟨defectArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source defectArena ⟨defectSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize familySignature (fun _ _ γ t => (Reduction.f γ t : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms defectAudit

def smoothActual : Realization smoothSignature :=
  realize smoothSignature (fun _ _ γ => Reduction.psi γ) (fun e => nomatch e)

def absFamily : Realization smoothSignature :=
  realize smoothSignature (fun _ _ _ => abs) (fun e => nomatch e)

abbrev smoothArena : Arena where
  signature := smoothSignature
  Law R := ∀ {n : ℕ∞ω} {γ : ℝ}, 2 ≤ γ → ContDiff ℝ n (R.readout () () γ)

private theorem smooth_rejected : ¬ smoothArena.Law absFamily := by
  intro H
  exact not_differentiableAt_abs_zero
    ((H (n := 1) (γ := 2) le_rfl).differentiable (by norm_num) 0)

private theorem smoothDependence : ObservationalDependence smoothSignature smoothActual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  intro he
  have hf := congrArg (fun g : ℝ → ℝ => deriv (deriv g) 1 - g 1) he
  change Reduction.f 2 1 = Reduction.f 3 1 at hf
  rw [defect_two_one] at hf
  exact defect_three_one_pos.ne' hf.symm

def smoothSource : Registration smoothArena (type_of% @psi_contDiff) where
  actual := smoothActual
  bridge := Iff.rfl
  variation := ⟨psi_contDiff, absFamily, smooth_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    smoothArena.Law smoothActual absFamily smooth_rejected
  dependence := smoothDependence

def smoothAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@psi_contDiff) (Realization smoothSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor.smoothUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor.smoothSource
  realizationSource := none
  generated := false
  arena := .source ⟨smoothArena⟩
  objectArena := .source ⟨smoothArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source smoothArena ⟨smoothSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize smoothSignature (fun _ _ γ => Reduction.psi γ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms smoothAudit

end Reg.D5.S3.Quantum.Matrix.StolarskyMean.KernelFactor
