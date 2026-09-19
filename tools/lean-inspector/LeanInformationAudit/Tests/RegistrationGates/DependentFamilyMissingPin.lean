import LeanInformationAudit.Registry.Enrollment
import LeanInformationAudit.DependentFamilyRealization

open Lean Meta Elab Command LeanInformationAudit

run_meta do
  withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLocalDeclD `i (mkApp (mkConst ``Fin) n) fun i => do
      let value := mkApp (mkConst ``Fin) (mkApp2 (mkConst ``Fin.val) n i)
      let rejected ← try
        discard <| TemplateAudit.checkExtractionType value 524288 #[] .dependentFamily
        pure false
      catch error => pure ((← error.toMessageData.toString) == "incomplete_closure:E2.family_pin")
      unless rejected do throwError "[FAIL] family_missing_pin"
      logInfo "[PASS] family_missing_pin"
