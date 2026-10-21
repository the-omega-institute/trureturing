import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
import Reg.Support.SingleDependentReadout

/-! Source-bound registration for the local-unitary partial-trace identity. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
open _root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
abbrev TwoQubit := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Qubit (fun _ => TwoQubit) (fun _ => Qubit)

def actual : Realization signature :=
  realize signature (fun _ U P =>
    partialTraceRight ((U ⊗ₖ (1 : Qubit)) * P * ((U ⊗ₖ (1 : Qubit))).conjTranspose)
  ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Qubit) (P : TwoQubit),
    R.readout () U P = U * partialTraceRight P * U.conjTranspose

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (1 : Qubit) (1 : TwoQubit)
  have he' : (0 : Qubit) = partialTraceRight (1 : TwoQubit) := by
    simpa [rejected, realize, Matrix.one_mul, Matrix.mul_one] using he
  have hentry := congrArg (fun X : Qubit => X 0 0) he'
  change (0 : ℂ) = ∑ k : Fin 2, (1 : TwoQubit) (0, k) (0, k) at hentry
  norm_num [Fin.sum_univ_two, Matrix.one_apply] at hentry

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : TwoQubit), (1 : TwoQubit), ?_⟩
  intro h
  have he := congrArg (fun X : Qubit => X 0 0) h
  norm_num [actual, realize, partialTraceRight, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.one_apply] at he

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_left) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_left,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace2_left)
      (Realization signature) Qubit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.unit
  realizationName := `Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ U P =>
    partialTraceRight ((U ⊗ₖ (1 : Qubit)) * P * ((U ⊗ₖ (1 : Qubit))).conjTranspose)
  ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 1
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings
