import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.SchurBoundaryKernel
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.Analytic.Interpolation.SchurBoundaryKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter
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
      (fun p => boundaryKernel p.1 p.2) atTop {p | p.1 ∈ Icc (0 : ℝ) 1}

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

#print axioms audit
end Reg.D5.S3.Analytic.Interpolation.SchurBoundaryKernel
