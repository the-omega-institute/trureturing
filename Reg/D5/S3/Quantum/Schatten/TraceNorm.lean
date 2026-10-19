import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Schatten.TraceNorm
import Reg.Support.DependentFamily

/-! Source-bound registrations for the two-dimensional trace-norm identities. -/

namespace Reg.D5.S3.Quantum.Schatten.TraceNorm
open _root_.D5.S3.Quantum.Schatten.TraceNorm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Determinant

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T : Matrix (Fin 2) (Fin 2) ℂ),
    R.readout () () (CFC.sqrt (Tᴴ * T)).det (‖T.det‖ : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def source_registration : Registration arena (type_of% @det_transitionAbs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@det_transitionAbs, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℂ), 1, ?_⟩
    intro he
    have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Schatten.TraceNorm.det_transitionAbs) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.TraceNorm.det_transitionAbs.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.TraceNorm.Determinant.source_registration
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
    owner := `D5.S3.Quantum.Schatten.TraceNorm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Determinant

namespace Square

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T : Matrix (Fin 2) (Fin 2) ℂ),
    R.readout () () ((CFC.sqrt (Tᴴ * T)).trace.re ^ 2)
      (RHLinalg.frobSq T + 2 * ‖T.det‖)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0

def source_registration : Registration arena (type_of% @transitionMass_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@transitionMass_sq, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Schatten.TraceNorm.transitionMass_sq) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Schatten.TraceNorm.transitionMass_sq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Schatten.TraceNorm.Square.source_registration
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
    owner := `D5.S3.Quantum.Schatten.TraceNorm
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Square

end
end Reg.D5.S3.Quantum.Schatten.TraceNorm
