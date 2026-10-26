import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.QuantumBounds.CHSHWitness renaming TwoQubitMatrix → TwoQubit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker

noncomputable section
namespace ConjugateKroneckerTrace

/-- Observe the trace paired with the conjugated Kronecker coefficient. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => TwoQubit) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ Z => trace Z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K A : Matrix (Fin 2) (Fin 2) ℂ) (ρ : TwoQubit),
    trace (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K) * ρ *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ K)ᴴ *
      (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) =
        R.readout () () (ρ * (A ⊗ₖ (Kᴴ * K)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 0
  norm_num [rejected, realize] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change trace (0 : TwoQubit) ≠ trace (1 : TwoQubit)
  norm_num [trace_one]

def source_registration : Registration arena (type_of% @trace_conj_kron) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_conj_kron, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_conj_kron) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "ConjugateKroneckerTrace") "unit"
  realizationName := Lean.Name.str
    (Lean.Name.str
      `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
      "ConjugateKroneckerTrace") "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ Z => trace Z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ConjugateKroneckerTrace
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (pauli pauli_zero pauli_one pauli_two)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace PauliReadout

/-- Observe the Pauli matrix as its index varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3)
    (fun _ => Matrix (Fin 2) (Fin 2) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ i => pauli i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  change pauli 0 ≠ pauli 2
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  norm_num [pauli_zero, pauli_two] at he

end PauliReadout

namespace PauliZero
abbrev arena : Arena where
  signature := PauliReadout.signature
  Law R := R.readout () () 0 = !![0, 1; 1, 0]

theorem rejected_law : ¬ arena.Law PauliReadout.rejected := by
  intro h
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) h
  norm_num [PauliReadout.rejected, realize, Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @pauli_zero) where
  actual := PauliReadout.actual
  bridge := Iff.rfl
  variation := ⟨pauli_zero, PauliReadout.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    PauliReadout.actual PauliReadout.rejected rejected_law
  dependence := PauliReadout.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli_zero)
      (Realization PauliReadout.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliZero.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliZero
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PauliReadout.signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end PauliZero

namespace PauliOne
abbrev arena : Arena where
  signature := PauliReadout.signature
  Law R := R.readout () () 1 = !![0, -Complex.I; Complex.I, 0]

theorem rejected_law : ¬ arena.Law PauliReadout.rejected := by
  intro h
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -Complex.I; Complex.I, 0] at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) h
  norm_num [PauliReadout.rejected, realize, Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @pauli_one) where
  actual := PauliReadout.actual
  bridge := Iff.rfl
  variation := ⟨pauli_one, PauliReadout.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    PauliReadout.actual PauliReadout.rejected rejected_law
  dependence := PauliReadout.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli_one)
      (Realization PauliReadout.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliOne.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliOne
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PauliReadout.signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end PauliOne

namespace PauliTwo
abbrev arena : Arena where
  signature := PauliReadout.signature
  Law R := R.readout () () 2 = !![1, 0; 0, -1]

theorem rejected_law : ¬ arena.Law PauliReadout.rejected := by
  intro h
  change (0 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] at h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) h
  norm_num [PauliReadout.rejected, realize, Matrix.zero_apply] at he

def source_registration : Registration arena (type_of% @pauli_two) where
  actual := PauliReadout.actual
  bridge := Iff.rfl
  variation := ⟨pauli_two, PauliReadout.rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    PauliReadout.actual PauliReadout.rejected rejected_law
  dependence := PauliReadout.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.pauli_two)
      (Realization PauliReadout.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliTwo.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.PauliTwo
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize PauliReadout.signature (fun _ _ i => pauli i) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0, functionOperand := false
      stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end PauliTwo
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction

namespace Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
open _root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
  (vlen vlen_e3 vlen_nonneg)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace VectorLengthNonnegative

/-- Observe the Euclidean length of a real three-vector. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 3 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ v => vlen v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fin 3 → ℝ, 0 ≤ R.readout () () v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  change (0 : ℝ) ≤ -1 at he
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, ![0, 0, 1], ?_⟩
  change vlen (0 : Fin 3 → ℝ) ≠ vlen ![0, 0, 1]
  rw [vlen_e3]
  norm_num [vlen]

def source_registration : Registration arena (type_of% @vlen_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨vlen_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.vlen_nonneg)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.VectorLengthNonnegative
    "unit"
  realizationName := Lean.Name.str
    `Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.VectorLengthNonnegative
    "source_registration"
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => vlen v) (fun e => nomatch e))
  variation := .absent, sensitivity := .absent
  partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn"]
      stateBinder := 0, functionOperand := true
      stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none, options := #[] }

#print axioms source_registration
#print axioms registration

end VectorLengthNonnegative
end
end Reg.D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction
