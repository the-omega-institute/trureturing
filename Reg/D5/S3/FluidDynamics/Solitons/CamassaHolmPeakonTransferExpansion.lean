import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
open _root_.D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the coefficient-family witness in its equality with the universal formula. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => CoeffFamily) (fun _ => CoeffFamily)

def actual : Realization signature :=
  realize signature (fun _ _ a => a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

/-- Only the equality's left operand is observed; both remaining clauses retain their witness. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∃ a : CoeffFamily,
    R.readout () () a = universalCoeff ∧ prescribedValues a ∧ expansion a

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha, _⟩ := h
  obtain ⟨b, hb, hp, _⟩ := result
  have hu : prescribedValues universalCoeff := hb ▸ hp
  have hzero := congrArg (fun c : CoeffFamily => c 1 (Nat.Partition.indiscrete 1)) ha
  change (0 : ℚ) = universalCoeff 1 (Nat.Partition.indiscrete 1) at hzero
  have hone := hu.1 1 (Nat.Partition.indiscrete 1) (by decide)
    (Nat.Partition.indiscrete_parts (by decide))
  exact zero_ne_one (hzero.trans hone)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrArg (fun c : CoeffFamily => c 1 (Nat.Partition.indiscrete 1)) h
  exact zero_ne_one he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.result)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion "unit",
  realizationName :=
    `Reg.D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ a => a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion,
    definition := some {
      owner := `D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion,
      name := `D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.claim,
      path := #[] },
    coordinates := #[],
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms signature
#print axioms actual
#print axioms rejected
#print axioms arena
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion
