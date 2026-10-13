import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
  (fockPair_apply)
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter (fockPair)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- At each retained occupation, observe the full two-mode vector as the environment varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ)
    (fun _ => lp (fun _ : ℕ => lp (fun _ : ℕ => ℂ) 2) 2)

def actual : Realization signature :=
  realize signature (fun _ m n => fockPair m n) (fun e => Empty.elim e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => Empty.elim e)

/-- The complete coefficient identity, with only the two-mode vector observed. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m n p q : ℕ,
    R.readout () m n q p = if p = m ∧ q = n then (1 : ℂ) else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 0 0 0
  change (0 : ℂ) = if (0 : ℕ) = 0 ∧ (0 : ℕ) = 0 then 1 else 0 at he
  norm_num at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change fockPair 0 0 ≠ fockPair 0 1
  intro h
  have he := congrArg (fun v : lp (fun _ : ℕ => lp (fun _ : ℕ => ℂ) 2) 2 => v 0 0) h
  rw [fockPair_apply, fockPair_apply] at he
  norm_num at he

def source_registration : Registration arena (type_of% @fockPair_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fockPair_apply, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fockPair_apply)
      (Realization signature) Unit Unit := {
  unitName :=
    Lean.Name.str
      `Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
      "unit",
  realizationName :=
    Lean.Name.str
      `Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
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
  readout := some (realize signature (fun _ m n => fockPair m n) (fun e => Empty.elim e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner :=
      `D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
