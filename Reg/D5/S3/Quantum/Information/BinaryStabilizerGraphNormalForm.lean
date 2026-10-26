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

namespace TensorUnitary
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_unitary)

/-- Unitary membership observes the tensor product of the complete factor family. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ) →
      R.readout () N A ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := Matrix.mem_unitaryGroup_iff.mp
    (h (N := 1) (fun _ => 1) (fun _ => (Matrix.unitaryGroup (Fin 2) ℂ).one_mem))
  change (0 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ) * star 0 = 1 at hz
  have he := congrArg (fun M => M (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2))) hz
  simp at he

def source_registration : Registration arena (type_of% @tensor_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensor_unitary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_unitary)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorUnitary.unit,
  realizationName :=
    Lean.Name.str
      `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorUnitary
      "source_registration",
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
      path := #["body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms source_registration
#print axioms registration

end TensorUnitary
namespace TensorScalar
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_smul)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ N : ℕ, Fin N → ℂ)
    (fun p => Fin p.1 → Matrix (Fin 2) (Fin 2) ℂ)
    (fun p => Matrix (Fin p.1 → Fin 2) (Fin p.1 → Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ A => tensorOp A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (r : Fin N → ℂ) (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ),
    tensorOp (fun i => r i • A i) = (∏ i, r i) • R.readout () ⟨N, r⟩ A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun M => M (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2)))
    (h (N := 1) (fun _ => 1) (fun _ => 1))
  change tensorOp (fun _ : Fin 1 => (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ => 0) (fun _ => 0) = (∏ i : Fin 1, (1 : ℂ)) • (0 : ℂ) at he
  simp [tensorOp, Matrix.one_apply] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, fun _ => 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change tensorOp (fun _ : Fin 1 => (0 : Matrix (Fin 2) (Fin 2) ℂ)) ≠
    tensorOp (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ))
  intro h
  have he := congrArg (fun M => M (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2))) h
  simp [tensorOp, Matrix.one_apply] at he

def source_registration : Registration arena (type_of% @tensor_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensor_smul, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_smul)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorScalar.unit,
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorScalar
    "source_registration",
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
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms source_registration
#print axioms registration
end TensorScalar

namespace GateUnitary
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (gate gate_unitary)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Bool
    (fun _ => ZMod 2) (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ h d => gate h d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h : Bool) (d : ZMod 2),
    R.readout () h d ∈ Matrix.unitaryGroup (Fin 2) ℂ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := Matrix.mem_unitaryGroup_iff.mp (h false 0)
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) * star 0 = 1 at hz
  have he := congrArg (fun M => M 0 0) hz
  simp at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨false, 0, 1, ?_⟩
  change gate false 0 ≠ gate false 1
  intro h
  have he := congrArg (fun M => M 1 1) h
  norm_num [gate] at he
  have him := congrArg Complex.im he
  norm_num at him

def source_registration : Registration arena (type_of% @gate_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gate_unitary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.gate_unitary)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.GateUnitary.unit,
  realizationName :=
    `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.GateUnitary.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ h d => gate h d) (fun e => nomatch e)),
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

end GateUnitary

namespace TensorWeyl
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_weyl)
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient (complexSign)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ N : ℕ, (Fin N → ZMod 2) × (Fin N → ZMod 2))
    (fun p => (Fin p.1 → ZMod 2) → ℂ) (fun p => (Fin p.1 → ZMod 2) → ℂ)

def actual : Realization signature :=
  realize signature (fun _ p f => fun t =>
    complexSign (∑ i, p.2.2 i * (t i + p.2.1 i)) * f (t + p.2.1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (v : (Fin N → ZMod 2) × (Fin N → ZMod 2))
    (f : (Fin N → ZMod 2) → ℂ),
    tensorOp (fun i => Matrix.of fun t s : Fin 2 =>
      if id (α := ZMod 2) s = id (α := ZMod 2) t + v.1 i then
        complexSign (v.2 i * id (α := ZMod 2) s) else 0) *ᵥ f =
      R.readout () ⟨N, v⟩ f

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrFun (h (N := 0) (0, 0) (fun _ => 1)) (fun i => nomatch i)
  change (∑ _ : Fin 0 → Fin 2, (∏ _ : Fin 0, (1 : ℂ)) * (1 : ℂ)) = 0 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, (0, 0)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun h (fun i => nomatch i)
  change complexSign (∑ i : Fin 0, _) * (0 : ℂ) =
    complexSign (∑ i : Fin 0, _) * (1 : ℂ) at he
  norm_num [_root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_zero] at he

def source_registration : Registration arena (type_of% @tensor_weyl) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tensor_weyl, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_weyl)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorWeyl.unit,
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.TensorWeyl
    "source_registration",
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p f => fun t =>
    complexSign (∑ i, p.2.2 i * (t i + p.2.1 i)) * f (t + p.2.1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm,
    definition := none,
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end TensorWeyl

end
end Reg.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
