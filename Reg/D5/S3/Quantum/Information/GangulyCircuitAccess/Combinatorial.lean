import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial.Gram
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.GangulyCircuitAccess
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

def observed (s t : Fin 2) : ℤ :=
  ∑ p : Config (discarded witnessDealer witnessPlayers) × Config witnessPlayers,
    signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers p s) *
    signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers p t)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2) (fun _ => Fin 2) (fun _ => ℤ)

def actual : Realization signature := realize signature (fun _ s t => observed s t) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ s t : Fin 2, R.readout () s t = if s = t then 64 else 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (by decide : (0 : ℤ) ≠ 64) (h 0 0)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change observed 0 0 ≠ observed 0 1
  have ha : observed 0 0 = 64 := witness_signed_gram 0 0
  have hb : observed 0 1 = 0 := witness_signed_gram 0 1
  rw [ha, hb]
  decide

def source_registration : Registration arena (type_of% witness_signed_gram) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨witness_signed_gram, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      witness_signed_gram (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial.Gram.unit,
  realizationName := `Reg.D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial.Gram.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ s t => observed s t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
end Reg.D5.S3.Quantum.Information.GangulyCircuitAccess.Combinatorial.Gram
