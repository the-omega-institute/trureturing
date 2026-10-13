import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_adj)
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (tensorOp)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The tensor product observes the entire family of single-qubit factors. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun N => Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (fun N => Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ A => tensorOp A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The full adjoint identity, observing the tensor product on the right. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ),
    (tensorOp A)ᴴ = R.readout () N (fun i => (A i)ᴴ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun M => M (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2)))
    (h (N := 1) (fun _ => 1))
  change (tensorOp (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)))ᴴ
    (fun _ => 0) (fun _ => 0) = 0 at he
  simp [tensorOp, Matrix.conjTranspose_apply, Matrix.one_apply] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  change tensorOp (fun _ : Fin 1 => (0 : Matrix (Fin 2) (Fin 2) ℂ)) ≠
    tensorOp (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ))
  intro h
  have he := congrArg (fun M => M (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2))) h
  simp [tensorOp, Matrix.one_apply] at he

def source_registration : Registration arena (type_of% @tensor_adj) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensor_adj, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_adj)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.unit,
  realizationName :=
    `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ A => tensorOp A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
