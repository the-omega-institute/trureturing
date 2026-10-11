import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (tensorOp)
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_one)

set_option linter.style.longLine false

noncomputable section
namespace Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
namespace TensorOne

abbrev signature : Signature where
  Params := ℕ
  State N := Fin N → Matrix (Fin 2) (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ
  Anchor := Unit
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ A => tensorOp A) (fun _ _ _ => 1)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun _ _ _ => 1)

def rejectedAnchor : Realization signature :=
  realize signature (fun _ _ A => tensorOp A) (fun _ _ _ => 0)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, R.readout () N (R.anchor () N) = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have entry := congrFun (congrFun (h (N := 1)) (fun _ => 0)) (fun _ => 0)
  change (0 : ℂ) = 1 at entry
  exact zero_ne_one entry

theorem rejected_anchor_law : ¬ arena.Law rejectedAnchor := by
  intro h
  have entry := congrFun (congrFun (h (N := 1)) (fun _ => 0)) (fun _ => 0)
  change tensorOp (fun _ : Fin 1 => (0 : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => 0) (fun _ => 0) = 1 at entry
  norm_num [tensorOp] at entry

def family : Registration arena (type_of% @tensor_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensor_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      refine ⟨rejectedAnchor, rfl, ?_, rejected_anchor_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
  dependence := by
    intro i
    refine ⟨1, (fun _ => 1), (fun _ => 0), ?_⟩
    intro h
    have entry := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simp [actual, realize, tensorOp] at entry

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_one)
      (type_of% (realize signature (fun _ _ A => tensorOp A) (fun _ _ _ => 1))) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorOne.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => tensorOp A) (fun _ _ _ => 1))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end TensorOne

end Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
