import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S1.Depth.ContinuedFractions.FiniteRationalConvergentsLength

namespace Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergentsLength.Length
open QuantumShorContinuedFractions
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ x => (convergents x).length) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => 2 * Nat.log 2 x.den + 2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ x : ℚ, R.readout () () x ≤ 2 * Nat.log 2 x.den + 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 2, ?_⟩
  change (convergents 0).length ≠ (convergents (1 / 2)).length
  norm_num [convergents, Int.fract]

def source_registration : Registration arena (type_of% @QuantumShorContinuedFractions.convergents_length_log) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@QuantumShorContinuedFractions.convergents_length_log, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@QuantumShorContinuedFractions.convergents_length_log) (Realization signature) Unit Unit := {
  unitName := `QuantumShorContinuedFractions.convergents_length_log.__information_unit
  realizationName := `Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergentsLength.Length.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (convergents x).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Depth.ContinuedFractions.FiniteRationalConvergentsLength
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S1.Depth.ContinuedFractions.FiniteRationalConvergentsLength.Length
