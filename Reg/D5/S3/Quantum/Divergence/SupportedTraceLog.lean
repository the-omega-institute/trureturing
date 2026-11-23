import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.SupportedTraceLog

/-! Source-bound registration of the trace-log inequality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

open Matrix LeanInformationAudit
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.SupportedTraceLog

namespace Reg.D5.S3.Quantum.Divergence.SupportedTraceLog

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} {ι : Type v} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (S T : ι → Matrix n n ℂ)
    (_ : ∀ i, 0 ≤ w i) (_ : ∀ i, (S i).PosSemidef) (_ : ∀ i, (T i).PosSemidef)
    (_ : ∀ i x, T i *ᵥ x = 0 → S i *ᵥ x = 0),
    let A := ∑ i, w i • S i
    let C := ∑ i, w i • T i
    R.readout () () (A * (CFC.log A - CFC.log C)).trace.re
      (∑ i, w i * (S i * (CFC.log (S i) - CFC.log (T i))).trace.re)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let Z : ULift.{v} Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  have hZ (i : ULift.{v} Unit) : (Z i).PosSemidef := Matrix.PosSemidef.zero
  exact h (fun _ => 0) Z Z (fun _ => le_rfl) hZ hZ (fun _ _ hx => hx)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have h' := congrFun h 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at h'
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (h'.mp le_rfl)

def family : Registration arena.{u,v} (type_of% @traceLog_jointConvex.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceLog_jointConvex.{u,v}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@traceLog_jointConvex.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.SupportedTraceLog.traceLog_jointConvex.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.SupportedTraceLog.family
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
    owner := `D5.S3.Quantum.Divergence.SupportedTraceLog
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.SupportedTraceLog
