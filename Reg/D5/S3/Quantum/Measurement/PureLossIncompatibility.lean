import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.PureLossIncompatibility
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility
open _root_.D5.S3.Quantum.Measurement.PureLossIncompatibility
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the effect of a binary measurement at the chosen outcome. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2)
    (fun _ => Fin 2 → Op) (fun _ => Op)

def actual : Realization signature :=
  realize signature (fun _ b M => M b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : Op)) (fun e => nomatch e)

/-- The complete claim, observing only the effect fed to the loss channel. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n),
    ∃ M : Fin (n + 1) → Fin 2 → Op,
      (∀ j, IsBinaryPOVM (fun b => R.readout () b (M j))) ∧
      (∃ N : Fin (n + 1) → Fin 2 → Op,
        ∀ j b, IsLossDual (inverseTransmissivity n hn) (R.readout () b (M j)) (N j b)) ∧
      ∀ N : Fin (n + 1) → Fin 2 → Op,
        (∀ j b, IsLossDual (inverseTransmissivity n hn) (R.readout () b (M j)) (N j b)) →
          ¬ HasParent N

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, hM, _⟩ := h 1 (by norm_num)
  have he := (hM 0).2
  change (1 : Op) + 1 = 1 at he
  have hv := congrArg (fun T : Op => (T (lp.single (p := 2) 0 (1 : ℂ))) 0) he
  norm_num at hv

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun b => if b = 0 then 0 else 1),
    (fun b => if b = 0 then 1 else 0), ?_⟩
  change (0 : Op) ≠ 1
  intro h01
  have he := congrArg (fun T : Op => (T (lp.single (p := 2) 0 (1 : ℂ))) 0) h01
  simp at he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Measurement.PureLossIncompatibility.result)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility "unit",
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ b M => M b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility,
    definition := some {
      owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility,
      name := `D5.S3.Quantum.Measurement.PureLossIncompatibility.claim,
      path := #[] },
    coordinates := #[5],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "arg",
        "body", "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility
