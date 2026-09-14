import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Registry

namespace LeanInformationAudit.Tests.ReifierProviderBinding
open Lean Meta Elab Command
open LeanInformationAudit RegistrationReifier

-- The complete binding suite shares one dependency import. Environment values
-- are persistent: each fixture adds only a small delta and always restores saved.
private def expectFailure (label reason : String) (action : MetaM Unit) : MetaM Unit := do
  let outcome ← try action; pure none catch e => pure (some (← e.toMessageData.toString))
  let some actual := outcome | throwError "{label}: expected rejection"
  unless (actual.splitOn reason).length > 1 do throwError "{label}: {actual}"
  logInfo m!"P1_REJECTION {label} {actual}"
  logInfo m!"P1_NEGATIVE {label} {reason}"

-- A4: independently loaded environment, with kernel-checked impostor declarations.
-- Changing binder information leaves the applied source intact but violates its pin.
private def providerIdentityProbe (fresh : Environment) (suffix : String) (changeType : Bool) : MetaM Unit := do
  let name := (`D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates).str suffix
  let .thmInfo info ← getConstInfo name | throwError "provider control: not theorem"
  let saved ← getEnv
  try
    setEnv (fresh.setMainModule `P1.ImpostorProvider)
    let type := if changeType then
      match info.type with
      | .forallE n domain body bi => .forallE n domain body
          (if bi == .default then .implicit else .default)
      | other => other
      else info.type
    addDecl (.thmDecl { name, levelParams := info.levelParams, type, value := info.value })
    expectFailure ("provider_" ++ (if changeType then "type_" else "module_") ++ suffix)
      ("P1.UnsupportedDescriptor: provider " ++ (if changeType then "type pin" else "module")) do
        discard <| checkedProvider name
  finally setEnv saved


-- Every candidate is kernel checked, then tested in an independently loaded environment.
private def providerPinProbe (fresh : Environment) (name : Name) (change : String) : MetaM Unit := do
  let .thmInfo info ← getConstInfo name | throwError "pin control: not theorem"
  let saved ← getEnv
  try
    setEnv (fresh.setMainModule providerModule)
    let type := if change == "raw_type" then mkAnnotation `changedProviderType info.type
      else if change == "binder" then
        match info.type with
        | .forallE n t b bi => .forallE n t b (if bi == .default then .implicit else .default)
        | t => t
      else info.type
    let levels := if change == "universe_order" then info.levelParams.reverse else info.levelParams
    let (levels, type, value) := if change == "universe_rename" then
      let renamed := levels.map (fun n => n.str "renamed")
      (renamed, type.instantiateLevelParams levels (renamed.map Level.param),
        info.value.instantiateLevelParams levels (renamed.map Level.param))
      else (levels, type, info.value)
    if change == "kind" then
      addDecl (.defnDecl { name, levelParams := levels, type, value, hints := .abbrev, safety := .safe })
    else addDecl (.thmDecl { name, levelParams := levels, type, value })
    let label := s!"provider_pin_{change}_{name.getString!}"
    if change == "same_module" || change == "universe_rename" then
      discard <| checkedProvider name
      logInfo m!"P1_A5 {label} accepted"
    else
      expectFailure label (if change == "kind" then "provider is not a theorem" else "provider type pin") do
        discard <| checkedProvider name
  finally setEnv saved


-- Serialize kernel-checked fixtures and import them through explicit artifacts.
-- This makes the foreign-owner arm self-contained under a single make target.
private def providerForeignProbe (fresh : Environment) (imports : ImportState) : MetaM Unit := do
  let saved ← getEnv
  let foreignName := `P1ForeignProvider
  IO.FS.withTempDir fun dir => do
    try
      setEnv (fresh.setMainModule foreignName)
      for name in #[pointwiseProvider, sensitivityProvider, variationProvider] do
        let some (.thmInfo info) := saved.find? name | throwError "missing provider fixture"
        addDecl (.thmDecl { name, levelParams := info.levelParams, type := info.type, value := info.value })
      let file := dir / "P1ForeignProvider.olean"
      writeModule (← getEnv) file (writeIR := false)
      -- The import state retains the already loaded dependency regions. Extending it
      -- reads the explicit artifact only; finalizeImport supplies genuine imported
      -- ownership and constants without rereading any dependency olean.
      let foreignImports := #[{ module := foreignName : Import }]
      let (_, imports) ← withImporting <| (importModulesCore foreignImports
        (arts := ({} : NameMap ImportArtifacts).insert foreignName (.ofArrays #[#[file]]))).run imports
      let foreign ← finalizeImport imports foreignImports {} (leakEnv := false) (loadExts := false)
      setEnv (foreign.setMainModule `P1.ForeignConsumer)
      for name in #[pointwiseProvider, sensitivityProvider, variationProvider] do
        unless foreign.isImportedConst name do throwError "foreign provider was not imported"
        expectFailure s!"provider_foreign_import_{name.getString!}" "provider module" do
          discard <| checkedProvider name
    finally setEnv saved

run_meta do
  -- pointwiseEqLegacy and pointwiseEq_sensitivity occur in the providers' proof
  -- values, so their defining module is required even for the smallest import set.
  let modules := #[{
    module := `D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates : Import }]
  let (_, imports) ← withImporting <| (importModulesCore modules).run
  let fresh ← finalizeImport imports modules {} (leakEnv := false) (loadExts := false)
  for changeType in #[true, false] do
    for suffix in #["pointwise", "sensitivity", "variation"] do
      providerIdentityProbe fresh suffix changeType
  for name in #[pointwiseProvider, sensitivityProvider, variationProvider] do
    for change in #["same_module", "binder", "raw_type", "kind"] do
      providerPinProbe fresh name change
  providerPinProbe fresh variationProvider "universe_order"
  providerPinProbe fresh variationProvider "universe_rename"
  providerForeignProbe fresh imports

end LeanInformationAudit.Tests.ReifierProviderBinding
