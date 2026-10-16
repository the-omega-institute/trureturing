import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.PartialTransposeTrace

namespace Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace
open _root_.D5.S3.Quantum.Matrix.PartialTransposeTrace
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit _root_.Matrix
noncomputable section

abbrev signature : Signature where
  Params := (A : Type) × Type
  State p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => partialTranspose M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the actual partial-transpose occurrence is replaced by the readout. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B]
    (M : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ),
    star v ⬝ᵥ (O.readout () ⟨A,B⟩ M *ᵥ v) =
      (M * partialTranspose (vecMulVec v (star v))).trace

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (A := Fin 1) (B := Fin 1) 1 (fun _ => 1)
  norm_num [rejected, realize, partialTranspose, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec, Matrix.one_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ] at bad
  change (0 : ℂ) = 1 at bad
  exact zero_ne_one bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Fin 1,Fin 1⟩,0,1,?_⟩
  intro he
  have h := congrFun (congrFun he (0,0)) (0,0)
  norm_num [actual, realize, partialTranspose, Matrix.one_apply] at h
  change (0 : ℂ) = 1 at h
  exact zero_ne_one h

def evidence : Registration arena (type_of% (@partial_transpose_trace_duality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partial_transpose_trace_duality,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality)
      (type_of% (realize signature (fun _ _ M => partialTranspose M) (fun e => nomatch e)))
      (type_of% (@partialTranspose.{0,0})) Unit := {
  unitName := `D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => partialTranspose M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PartialTransposeTrace
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body",
        "fn","arg","arg","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace
