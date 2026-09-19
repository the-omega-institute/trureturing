import LeanInformationAudit.Tests.RegistrationGates.DependentFamilyWitnesses
import LeanInformationAudit.Syntax

namespace LeanInformationAudit.Tests.DependentFamily
open Lean Meta Elab Command
open LeanInformationAudit.DependentFamily
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
universe u v
noncomputable section

def signature : Signature where
  Θ := Fiber.{u,v}
  State θ := θ.1 × History θ.2.1 θ.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ θ := History θ.2.1 θ.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def template (s : Signature)
    (readout : ∀ role θ, s.State θ → s.Output role θ)
    (anchor : ∀ (_ : s.Anchor) θ, s.State θ) : Realization s where
  readout := readout
  anchor := anchor

register_information_template template dependent_family

-- The Law retains all original binders and dictionaries, including N=0.
def arena : Arena where
  signature := signature.{u,v}
  Law r := FullLaw (fun J Z N => r.readout () ⟨J,Z,N⟩)

def bad : Realization signature.{u,v} where
  readout _ θ := badFamily θ.1 θ.2.1 θ.2.2
  anchor i := Empty.elim i

-- Proofs are fields of the registration. No companion theorem is introduced.
def registration : Registration arena.{u,v} (FullLaw identityFamily) where
  realization := template signature (fun _ _ ω => ω.2) Empty.elim
  bridge := fun h => h
  variation := ⟨template signature (fun _ _ ω => ω.2) Empty.elim, bad, @history_law_conditional_expectation.{u,v}, bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨template signature (fun _ _ ω => ω.2) Empty.elim, bad, ?_, rfl,
        ⟨fun _ => bad_not_law, fun _ => @history_law_conditional_expectation.{u,v}⟩⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit inferInstance j i))
    · intro i; exact Empty.elim i

register_information_family history_law_conditional_expectation in arena
  readout via (template signature (fun _ _ ω => ω.2) Empty.elim) realization registration
  escape from coordinates [0, 1, 11]
  state ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
  output ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg"]
  escape continues (open)

run_cmd do
  let events := TemplateBinding.inventory (← getEnv)
  let some event := events.find? (·.key.mode == .dependentFamily)
    | throwError "family event missing"
  let some record := (TemplateBinding.records (← getEnv)).find? (·.occurrence.key == event.key)
    | throwError "family record missing"
  match record.result with
  | .declaredValidated certificate =>
    unless certificate.escape.family.isSome && certificate.escape.continuation == some { kind := "open" } do
      throwError "family four slots missing"
    logInfo "[PASS] unchanged_source_family_declared_validated"
  | .declaredUnresolved diagnostic => throwError diagnostic
  | _ => throwError "family declaration missing"

end
end LeanInformationAudit.Tests.DependentFamily
