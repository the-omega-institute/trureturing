import LeanInformationAudit.Tests.RegistrationGates.DependentFamilyUnicode

namespace LeanInformationAudit.Tests.DependentFamilyReuse
open Lean Elab Command
open _root_.LeanInformationAudit.DependentFamily
universe 𝒰 𝒱

theorem additional_source (_α : Type 𝒰) (_β : Type 𝒱) : ∀ x : Bool, x = x := fun _ => rfl

-- A second real enrollment supplies distinct plan and descriptor identities for
-- transplantation controls while reusing the very same typed registration.
def alternateTemplate (s : Signature)
    (anchor : ∀ (_ : s.Anchor) θ, s.State θ)
    (readout : ∀ role θ, s.State θ → s.Output role θ) : Realization s where
  readout := readout
  anchor := anchor

register_information_template alternateTemplate dependent_family

register_information_family additional_source in DependentFamilyUnicode.arena
  readout via (alternateTemplate DependentFamilyUnicode.signature Empty.elim (fun _ _ x => x))
  realization DependentFamilyUnicode.registration
  escape from coordinates [0, 1]
  state ["body", "body", "domain"] output ["body", "body", "domain"]
  escape continues (open)

run_cmd do
  let some row := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``additional_source) | throwError "missing reused family"
  match row.result with
  | .declaredValidated _ => logInfo "[PASS] reused_registration_second_source_declared_validated"
  | .declaredUnresolved diagnostic => throwError diagnostic
  | _ => throwError "reused family undeclared"

end LeanInformationAudit.Tests.DependentFamilyReuse
