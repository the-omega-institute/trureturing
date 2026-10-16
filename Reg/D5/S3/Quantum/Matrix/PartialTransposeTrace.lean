import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.PartialTransposeTrace

namespace Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace
open _root_.D5.S3.Quantum.Matrix.PartialTransposeTrace
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
noncomputable section

structure Parameters where
  A : Type
  B : Type
  fintypeA : Fintype A
  fintypeB : Fintype B
  vector : A × B → ℂ

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Matrix (p.A × p.B) (p.A × p.B) ℂ) (fun _ => ℂ)

def observation (p : Parameters) (M : Matrix (p.A × p.B) (p.A × p.B) ℂ) : ℂ := by
  letI := p.fintypeA
  letI := p.fintypeB
  exact star p.vector ⬝ᵥ (partialTranspose M *ᵥ p.vector)

def actual : Realization signature :=
  realize signature (fun _ p M => observation p M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {A B : Type} [fA : Fintype A] [fB : Fintype B]
    (M : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ),
    O.readout () ⟨A,B,fA,fB,v⟩ M =
      (M * partialTranspose (vecMulVec v (star v))).trace

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h (A := Fin 1) (B := Fin 1) 0 0
  norm_num [rejected, realize] at bad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Fin 1,Fin 1,inferInstance,inferInstance,fun _ => 1⟩,0,1,?_⟩
  norm_num [actual, realize, observation, partialTranspose, Matrix.mulVec,
    dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

def evidence : Registration arena (type_of% (@partial_transpose_trace_duality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨partial_transpose_trace_duality,rejected,rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality)
      (type_of% (realize signature (fun _ p M => observation p M) (fun e => nomatch e)))
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
  readout := some (realize signature (fun _ p M => observation p M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@partialTranspose.{0,0})
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PartialTransposeTrace
    definition := none
    coordinates := #[0,1,2,3,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace
