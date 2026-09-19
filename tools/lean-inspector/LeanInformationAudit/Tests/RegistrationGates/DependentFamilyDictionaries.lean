import LeanInformationAudit.Tests.RegistrationGates.DependentFamily

namespace LeanInformationAudit.Tests.DependentFamilyDictionaries
open Lean Meta Elab Command

abbrev DictionaryAlias := Fintype Unit
abbrev DataAlias := Nat
@[irreducible] def IrreducibleDictionaryAlias := Fintype Unit
@[irreducible] def IrreducibleDataAlias := Nat
@[irreducible] def IrreducibleIndexedDictionaryAlias (n : Nat) := Fintype (Fin n)
@[irreducible] def IrreducibleDictionaryFamily :=
  (n : Nat) → IrreducibleIndexedDictionaryAlias n

theorem directSource (_d : Fintype Unit) : ∀ x : Bool, x = x := fun _ => rfl
theorem aliasSource (_d : DictionaryAlias) : ∀ x : Bool, x = x := fun _ => rfl
theorem dataAliasSource (_n : DataAlias) : ∀ x : Bool, x = x := fun _ => rfl
theorem irreducibleAliasSource (_d : IrreducibleDictionaryAlias) :
    ∀ x : Bool, x = x := fun _ => rfl
theorem irreducibleDataAliasSource (_n : IrreducibleDataAlias) :
    ∀ x : Bool, x = x := fun _ => rfl
theorem dependentDictionarySource (_d : (n : Nat) → Fintype (Fin n)) :
    ∀ x : Bool, x = x := fun _ => rfl
theorem irreducibleDictionaryFamilySource (_d : IrreducibleDictionaryFamily) :
    ∀ x : Bool, x = x := fun _ => rfl

run_meta do
  let selection : FamilySourceSelection := {
    coordinates := #[0], statePath := #["body", "domain"], outputPath := #["body", "domain"] }
  for name in #[``directSource, ``aliasSource, ``irreducibleAliasSource,
      ``dependentDictionarySource, ``irreducibleDictionaryFamilySource] do
    let rejected ← try
      discard <| FamilySource.resolve (← getConstInfo name) selection
      pure false
    catch error => pure ((← error.toMessageData.toString) ==
      "unclassified_form:family.map.dictionary_coordinate")
    unless rejected do throwError "[FAIL] dictionary coordinate admitted: {name}"
    logInfo m!"[PASS] dictionary_coordinate_rejected {name}"
  for (name, aliasName) in #[(``dataAliasSource, ``DataAlias),
      (``irreducibleDataAliasSource, ``IrreducibleDataAlias)] do
    let info ← getConstInfo name
    let (scope, _) ← FamilySource.resolve info selection
    unless scope.sourceType.equal info.type && scope.selection == selection &&
        scope.telescope[0]!.domain.isConstOf aliasName &&
        scope.coordinateDomains[0]!.domain.isConstOf aliasName &&
        scope.state.context[0]!.domain.isConstOf aliasName &&
        scope.output.context[0]!.domain.isConstOf aliasName &&
        scope.state.raw.isConstOf ``Bool && scope.output.raw.isConstOf ``Bool do
      throwError "[FAIL] legitimate alias lost its raw source identity: {name}"
    discard <| FamilySource.validate info scope
    logInfo m!"[PASS] non_dictionary_alias_retains_raw_source {name}"

end LeanInformationAudit.Tests.DependentFamilyDictionaries
