import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.CommutingMidpoint.Fidelity
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.CommutingMidpoint
open scoped ComplexOrder MatrixOrder

namespace Reg.D5.S3.Quantum.CommutingMidpoint.Fidelity

namespace TraceSquare

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => (ℝ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (_hM : M.PosSemidef),
    R.readout () () ((trace (CFC.sqrt M)).re ^ 2)
      ((trace M).re + 2 * Real.sqrt M.det.re)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 Matrix.PosSemidef.zero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

def source_registration : Registration arena (type_of% @sqrt_trace_square_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sqrt_trace_square_two, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sqrt_trace_square_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.CommutingMidpoint.sqrt_trace_square_two.__information_unit
  realizationName := `Reg.D5.S3.Quantum.CommutingMidpoint.Fidelity.TraceSquare.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.CommutingMidpoint.Fidelity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TraceSquare

namespace RootTrace

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ) (fun _ => (Matrix (Fin 2) (Fin 2) ℂ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (_hM : M.PosSemidef),
    R.readout () () (((trace (CFC.sqrt M)).re : ℂ) • CFC.sqrt M)
      (M + (Real.sqrt M.det.re : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 Matrix.PosSemidef.zero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : Matrix (Fin 2) (Fin 2) ℂ), (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  intro he
  have hbad : (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  have hentry := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 0) hbad
  norm_num at hentry

def source_registration : Registration arena (type_of% @sqrt_times_trace_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sqrt_times_trace_two, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sqrt_times_trace_two) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.CommutingMidpoint.sqrt_times_trace_two.__information_unit
  realizationName := `Reg.D5.S3.Quantum.CommutingMidpoint.Fidelity.RootTrace.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.CommutingMidpoint.Fidelity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RootTrace

end Reg.D5.S3.Quantum.CommutingMidpoint.Fidelity
