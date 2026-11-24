import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
import Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation

/-! Source-bound audit of the entropy readout in the pinching gain identity. -/

namespace Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open _root_.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
open _root_.D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open _root_.D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u

open Reg.D5.S3.Quantum.Information.PartialTraceMutualInformation.EntropySpectral
  (signature actual rejected singletonDensity dependence)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {k : ℕ}
    (p : CompletePVM n k) (ρ : DensityState n),
    finiteTraceLogRelativeEntropy ρ (pinch p ρ) =
      vonNeumannEntropy (pinch p ρ) - R.readout () ⟨n, inferInstance, inferInstance⟩ ρ

private theorem bridge :
    (type_of% @finiteTraceLogRelativeEntropy_pinch.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p := coordinatePVM (fun _ : ULift.{u} Unit => (0 : Fin 1))
  let ρ : DensityState (ULift.{u} Unit) := singletonDensity
  have he : finiteTraceLogRelativeEntropy ρ (pinch p ρ) =
      vonNeumannEntropy (pinch p ρ) - (vonNeumannEntropy ρ + 1) := h p ρ
  rw [finiteTraceLogRelativeEntropy_pinch p ρ] at he
  linarith

def source_registration :
    Registration arena.{u} (type_of% @finiteTraceLogRelativeEntropy_pinch.{u}) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @finiteTraceLogRelativeEntropy_pinch.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@finiteTraceLogRelativeEntropy_pinch.{u}) (Realization signature.{u})
      (type_of% @DensityState.{u}) Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity.entropyGain
  realizationName := `Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p ρ => @vonNeumannEntropy p.1 p.2.1 p.2.2 ρ)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
