import LeanInformationAudit.Tests.RegistrationGates.DependentFamily

namespace LeanInformationAudit.Tests.DependentFamilyDictionaries
open Lean Meta Elab Command

abbrev DictionaryAlias := Fintype Unit
abbrev DataAlias := Nat

theorem directSource (_d : Fintype Unit) : ∀ x : Bool, x = x := fun _ => rfl
theorem aliasSource (_d : DictionaryAlias) : ∀ x : Bool, x = x := fun _ => rfl
theorem dataAliasSource (_n : DataAlias) : ∀ x : Bool, x = x := fun _ => rfl

run_meta do
  let selection : FamilySourceSelection := {
    coordinates := #[0], statePath := #["body", "domain"], outputPath := #["body", "domain"] }
  for name in #[``directSource, ``aliasSource] do
    let rejected ← try
      discard <| FamilySource.resolve (← getConstInfo name) selection
      pure false
    catch error => pure ((← error.toMessageData.toString) ==
      "unclassified_form:family.map.dictionary_coordinate")
    unless rejected do throwError "[FAIL] dictionary coordinate admitted: {name}"
    logInfo m!"[PASS] dictionary_coordinate_rejected {name}"
  let info ← getConstInfo ``dataAliasSource
  let (scope, _) ← FamilySource.resolve info selection
  unless scope.sourceType.equal info.type &&
      scope.coordinateDomains[0]!.domain.isConstOf ``DataAlias do
    throwError "[FAIL] legitimate alias lost its raw source identity"
  logInfo "[PASS] non_dictionary_alias_retains_raw_source"

end LeanInformationAudit.Tests.DependentFamilyDictionaries
