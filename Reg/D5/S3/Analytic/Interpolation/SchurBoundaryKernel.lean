import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SchurBoundaryKernel
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.Analytic.Interpolation.SchurBoundaryKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Reg.D5.S3.Analytic.Interpolation.SchurBoundaryKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b θ : ℝ) (_hb : b ∈ Icc (0 : ℝ) 1),
    Continuous (boundaryKernel b) ∧
    boundaryKernel b (Real.pi - θ) = -boundaryKernel b θ ∧
    R.readout () () (Real.cos θ * boundaryKernel b θ) 0 ∧
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ j ∈ Finset.range n, boundaryTerm p.1 p.2 j)
      (fun p => boundaryKernel p.1 p.2) atTop {p | p.1 ∈ Icc (0 : ℝ) 1} ∧
    ContinuousOn (fun p : ℝ × ℝ => boundaryKernel p.1 p.2)
      {p | p.1 ∈ Icc (0 : ℝ) 1} ∧
    (∫ φ in (0 : ℝ)..(2 * Real.pi), boundaryKernel b φ) = 0 ∧
    |boundaryKernel b θ| ≤ 3067 / 8100 ∧ (3067 / 8100 : ℝ) < 19 / 50

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0 0 (by norm_num)).2.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @boundary_kernel_control) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_kernel_control, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_kernel_control) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurBoundaryKernel.boundary_kernel_control.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurBoundaryKernel.family
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
    owner := `D5.S3.Analytic.Interpolation.SchurBoundaryKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev primitiveSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def primitiveActual : Realization primitiveSignature :=
  realize primitiveSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def primitiveRejected : Realization primitiveSignature :=
  realize primitiveSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev primitiveArena : Arena where
  signature := primitiveSignature
  Law R := ∀ (h H : ℂ → ℂ) (_hh : Differentiable ℂ h)
    (_hH : ∀ z : ℂ, HasDerivAt H (h z) z) (_hH0 : H 0 = 0)
    (b : ℝ) (_hb : b ∈ Ioc (0 : ℝ) 1),
    R.readout () ()
      ((1 / (2 * b) : ℝ) • (∫ t in -b..b, H ((t : ℂ) * Complex.I)))
      (((2 * Real.pi)⁻¹ : ℝ) • (∫ θ in (0 : ℝ)..(2 * Real.pi),
        h (circleMap 0 1 θ) * (boundaryKernel b θ : ℂ)))

private theorem primitiveRejectedLaw : ¬ primitiveArena.Law primitiveRejected := by
  intro h
  exact h (fun _ => 0) (fun _ => 0) (differentiable_const 0)
    (fun z => hasDerivAt_const z 0) rfl 1 (by norm_num)

private theorem primitiveDependence : ObservationalDependence primitiveSignature primitiveActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [primitiveActual, realize] at hh

def primitiveFamily : Registration primitiveArena (type_of% @boundary_primitive_representation) where
  actual := primitiveActual
  bridge := Iff.rfl
  variation := ⟨@boundary_primitive_representation, primitiveRejected, primitiveRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    primitiveArena.Law primitiveActual primitiveRejected primitiveRejectedLaw
  dependence := primitiveDependence

def primitiveAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_primitive_representation) (Realization primitiveSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.SchurBoundaryKernel.boundary_primitive_representation.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.SchurBoundaryKernel.primitiveFamily
  realizationSource := none
  generated := false
  arena := .source ⟨primitiveArena⟩
  objectArena := .source ⟨primitiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source primitiveArena ⟨primitiveFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize primitiveSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.SchurBoundaryKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms primitiveAudit

#print axioms audit
end Reg.D5.S3.Analytic.Interpolation.SchurBoundaryKernel
