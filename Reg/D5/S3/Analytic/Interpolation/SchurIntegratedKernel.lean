import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SchurIntegratedKernel
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.Analytic.Interpolation.SchurIntegratedKernel
open _root_.D5.S3.Analytic.Interpolation.SchurBoundaryKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory Complex

namespace Reg.D5.S3.Analytic.Interpolation.SchurIntegratedKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b x : ℝ) (_hb : b ∈ Icc (0 : ℝ) 1) (_hx : |x| < 1),
    R.readout () () ((2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
      |integratedPoisson x θ - boundaryKernel b θ|)) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @boundary_l1_control) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_l1_control, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_l1_control) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurIntegratedKernel.boundary_l1_control.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurIntegratedKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurIntegratedKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev boundArena : Arena where
  signature := signature
  Law R := ∀ (h H : ℂ → ℂ) (hh : Differentiable ℂ h)
    (hH : ∀ z : ℂ, HasDerivAt H (h z) z) (hH0 : H 0 = 0)
    (b : ℝ) (hb : b ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1),
    R.readout () ()
      (‖H (x : ℂ) - (1 / (2 * b) : ℝ) • (∫ t in -b..b, H ((t : ℂ) * I))‖)
      (sSup ((fun z => ‖h z‖) '' Metric.closedBall (0 : ℂ) 1))

private theorem boundRejectedLaw : ¬ boundArena.Law rejected := by
  intro h
  exact h (fun _ => 0) (fun _ => 0) (differentiable_const 0)
    (fun z => hasDerivAt_const z 0) rfl 1 (by norm_num) 0 (by norm_num)

def boundFamily : Registration boundArena (type_of% @primitive_error_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primitive_error_bound, rejected, boundRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    boundArena.Law actual rejected boundRejectedLaw
  dependence := dependence

def boundAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@primitive_error_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurIntegratedKernel.primitive_error_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurIntegratedKernel.boundFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena ⟨boundFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurIntegratedKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms boundAudit

#print axioms audit
end Reg.D5.S3.Analytic.Interpolation.SchurIntegratedKernel
