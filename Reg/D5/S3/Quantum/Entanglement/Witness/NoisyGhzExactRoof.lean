import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

abbrev phaseSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun d => (Fin d → ZMod 3) → ℂ) (fun _ => ℂ)

def phaseActual : Realization phaseSignature :=
  realize phaseSignature (fun _ _ f => ∑ θ, f θ) (fun e => nomatch e)

def phaseRejected : Realization phaseSignature :=
  realize phaseSignature (fun _ _ _ => 0) (fun e => nomatch e)

def phaseArena : Arena where
  signature := phaseSignature
  Law R := ∀ {d : ℕ} (v : Fin d → ZMod 3),
    R.readout () d (phaseCharacter v) = if v = 0 then (3^d : ℕ) else 0

private theorem phase_rejected_law : ¬ phaseArena.Law phaseRejected := by
  intro h
  have hh := h (d := 0) 0
  norm_num [phaseRejected,realize] at hh

def phaseRegistration : Registration phaseArena (phaseArena.Law phaseActual) where
  actual := phaseActual
  bridge := Iff.rfl
  variation := ⟨@phaseCharacter_sum,phaseRejected,phase_rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    phaseArena.Law phaseActual phaseRejected phase_rejected_law
  dependence := by
    change ObservationalDependence phaseSignature phaseActual
    intro i
    refine ⟨(0 : ℕ),(fun _ => (0 : ℂ)),(fun _ => (1 : ℂ)),?_⟩
    change (∑ θ : Fin 0 → ZMod 3, (0 : ℂ)) ≠ ∑ θ : Fin 0 → ZMod 3, (1 : ℂ)
    simp

noncomputable def registration_phase :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.phaseCharacter_sum)
    (type_of% (realize phaseSignature (fun _ _ f => ∑ θ, f θ) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.phase_sum_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.phaseRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨phaseArena⟩
  objectArena := .source ⟨phaseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source phaseArena ⟨phaseRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phaseSignature (fun _ _ f => ∑ θ, f θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
