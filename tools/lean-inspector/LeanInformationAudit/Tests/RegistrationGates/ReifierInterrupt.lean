import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests.ReifierInterrupt
open Lean Meta Elab Command Term RegistrationReifier
open D5.S3.ConceptDynamics.InformationEscape PointwiseRegistrationTemplates

def arena := pointwiseEqArena (Arena.ofFintype Bool) Bool
theorem clean (x : Bool) : x.not.not = x := Bool.not_not _

/-- An uncaught exception at the command boundary, after real derivation has
returned its generated declarations to CommandElabM. -/
elab "interrupt_after_derive" : command => registrationTransaction do
  liftTermElabM do
    let descriptor ← elabTerm (← `(term|
      D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates.pointwise
        (fun x : Bool => x.not.not) (fun x => x))) none
    synthesizeSyntheticMVarsNoPostponing
    let descriptor ← instantiateMVars descriptor
    let env ← getEnv
    let entry ← prepareRegistrationEntry env {
      theoremName := ``clean
      unitName := localCompanionName env ``clean theoremUnitSuffix
      arenaName := ``arena
      realizationName := localCompanionName env ``clean primitiveRealizationSuffix
      statementIdentity := theoremStatementIdentity env ``clean }
    discard <| derive entry (← freezeArena ``arena) descriptor
  unless (← getEnv).contains (localCompanionName (← getEnv) ``clean theoremUnitSuffix) do
    throwError "interrupt control did not derive"
  throw (.internal interruptExceptionId)

interrupt_after_derive
end LeanInformationAudit.Tests.ReifierInterrupt
