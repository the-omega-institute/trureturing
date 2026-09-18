/- GID: D5/S3/ConceptDynamics/InformationEscape/CiDeclaredTemplateProbe
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exercise declared-template admission with a temporary compiler fixture. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.CiDeclaredTemplateProbe

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

register_information_template cutRealization

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not

instance : DecidableEq arena.State := instDecidableEqBool

def good : PrimitiveRealization arena.signature :=
  cutRealization (fun x : Bool => x)

def bad : PrimitiveRealization arena.signature :=
  cutRealization (fun _ : Bool => true)

theorem lawVariation : arena.Law good ∧ ¬arena.Law bad := by
  constructor
  · intro x
    exact (Bool.not_not x).symm
  · intro h
    exact Bool.noConfusion (h false)

theorem slotSensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    refine ⟨good, bad, ?_, ?_, ?_⟩
    · intro j ne
      cases i
      cases j
      exact (ne rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => lawVariation.2, fun _ => lawVariation.1⟩
  · intro i
    exact Fin.elim0 i

information_theorem declared in arena
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  variation lawVariation sensitivity slotSensitivity
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

open Lean in
run_cmd Elab.Command.liftTermElabM do
  let some entry := InformationRegistry.find? (← getEnv) ``declared
    | throwError "DTR probe registration is missing"
  if let some diagnostic ← RegistrationGates.validateFinite entry then
    throwError "DTR probe registration gate failed: {diagnostic}"

open Lean in
run_meta do
  let rows ← TemplateBinding.assessJoined
  let selected := rows.filter
    (·.occurrence.key.registrationModule == (← getEnv).header.mainModule)
  unless selected.size == 1 do
    throwError "DTR probe requires exactly one current-module occurrence"
  for row in selected do
    match row.result with
    | .declaredValidated _ => throwError "DTR negative probe unexpectedly declared"
    | .declaredUnresolved diagnostic => throwError "DTR probe unresolved: {diagnostic}"
    | .undeclared => logInfo m!"DTR_PROBE_UNDECLARED {row.occurrence.key.theoremName}"

end D5.S3.ConceptDynamics.InformationEscape.CiDeclaredTemplateProbe
