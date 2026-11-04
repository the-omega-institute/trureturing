import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
import Reg.Support.DependentFamily

/-! Source-bound audit of nilpotence from the vanishing self-anticommutator. -/

namespace Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
open _root_.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_1

/-- Evaluate the left multiplication operand at the element being squared. -/
abbrev signature : Signature where
  Params := Σ R : Type u_1, R
  State p := p.1 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ p op => op p.2) (fun e => Empty.elim e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ p _ => p.2) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law r := ∀ {R : Type u_1} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
    (b : R) (_hbb : b * b + b * b = 0),
    r.readout () ⟨R, b⟩ (fun x => b * x) = 0

theorem rejected_law : ¬ arena.{u_1}.Law rejected.{u_1} := by
  intro h
  let n := ULift.{u_1} (Fin 2)
  let b : Matrix n n ℂ := Matrix.single ⟨0⟩ ⟨1⟩ 1
  have hbb : b * b = 0 := by
    apply Matrix.single_mul_single_of_ne
    decide
  have he := h b (by rw [hbb, zero_add])
  change b = 0 at he
  have hc := congrArg (fun X : Matrix n n ℂ => X ⟨0⟩ ⟨1⟩) he
  change (1 : ℂ) = 0 at hc
  exact one_ne_zero hc

theorem dependence : ObservationalDependence signature.{u_1} actual.{u_1} := by
  intro i
  refine ⟨⟨ULift.{u_1} Bool, ⟨false⟩⟩, (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  intro h
  have hc := congrArg ULift.down h
  change false = true at hc
  cases hc

def source_registration : Registration arena.{u_1} (type_of% @CAR_nilpotent.{u_1}) where
  actual := realize signature (fun _ p op => op p.2) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨CAR_nilpotent, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@CAR_nilpotent.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum.unit
  realizationName :=
    .str
      `Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p op => op p.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
    definition := none
    coordinates := #[0, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum

namespace Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
namespace Anticommutator

open _root_.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_1 u_2

/-- Evaluate the source linear-combination operator at its coefficient vector. -/
abbrev signature : Signature where
  Params := Σ _R : Type u_1, Σ ι : Type u_2, ι → ℂ
  State p := (Sigma.fst (Sigma.snd p) → ℂ) → Sigma.fst p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Sigma.fst p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1, u_2} :=
  realize signature (fun _ p op => op (Sigma.snd (Sigma.snd p))) (fun e => Empty.elim e)

def rejected : Realization signature.{u_1, u_2} :=
  realize signature (fun _ _ op => op (fun _ => 0)) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u_1, u_2}
  Law r := ∀ {R : Type u_1} [Ring R] [Algebra ℂ R]
    {ι : Type u_2} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (_hsq : ∀ j, g j * g j = 1)
    (_hanti : ∀ j k, j ≠ k → g j * g k = -(g k * g j)) (c d : ι → ℂ),
    r.readout () ⟨R, ι, c⟩ (Fintype.linearCombination ℂ g) *
        Fintype.linearCombination ℂ g d +
      Fintype.linearCombination ℂ g d * Fintype.linearCombination ℂ g c =
        (2 * ∑ j, c j * d j) • (1 : R)

theorem rejected_law : ¬ arena.{u_1, u_2}.Law rejected := by
  intro h
  have he := @h (ULift.{u_1} ℂ) inferInstance inferInstance
    (ULift.{u_2} Unit) inferInstance inferInstance (fun _ => 1)
    (by intro j; simp) (by intro j k hjk; exact (hjk (Subsingleton.elim j k)).elim)
    (fun _ => 1) (fun _ => 1)
  have hd := congrArg ULift.down he
  norm_num [rejected, realize, Fintype.linearCombination_apply] at hd

theorem dependence : ObservationalDependence signature.{u_1, u_2} actual := by
  intro i
  refine ⟨⟨ULift.{u_1} Bool, ULift.{u_2} Unit, fun _ => 0⟩,
    (fun _ => ⟨false⟩), (fun _ => ⟨true⟩), ?_⟩
  intro h
  have hd := congrArg ULift.down h
  change false = true at hd
  cases hd

def source_registration :
    Registration arena.{u_1, u_2} (type_of% @cliffordLinear_anticommutator.{u_1, u_2}) where
  actual := realize signature
    (fun _ p op => op (Sigma.snd (Sigma.snd p))) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨cliffordLinear_anticommutator, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cliffordLinear_anticommutator.{u_1, u_2})
      (Realization signature.{u_1, u_2}) Unit Unit := {
  unitName := .str
    (.str
      `Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
      "Anticommutator")
    "unit"
  realizationName := .str
    (.str
      `Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
      "Anticommutator")
    "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p op => op (Sigma.snd (Sigma.snd p))) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
    definition := none
    coordinates := #[0, 3, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Anticommutator
end Reg.D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
