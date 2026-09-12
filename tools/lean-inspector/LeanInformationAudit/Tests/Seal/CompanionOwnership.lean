import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

/-! Inspect actual imported constants and persisted records, independently of the
producer naming rule. Import order must not select a different companion owner. -/

private def checkOwner (env : Environment) (root name : Name) : IO Unit := do
  let some index := env.getModuleIdx? root
    | throw <| IO.userError s!"companionOwnership: missing module {root}"
  unless env.header.moduleData[index.toNat]!.constNames.contains name &&
      env.getModuleIdxFor? name == some index do
    throw <| IO.userError s!"companionOwnership: {name} is not owned by {root}"

private def checkRoot (env : Environment) (root : Name) (frozen : Bool) : IO Unit := do
  let records := SealRecords.forRoot env root
  unless records.size == (if frozen then 11 else 2) do
    throw <| IO.userError s!"companionOwnership: seal records lost in {root}: {records.size}"
  for record in records do
    let arena := record.catalog.arenaName
    let localArena := root.isPrefixOf arena
    let arenaName := fun suffix =>
      if frozen || localArena then arena.str suffix
      else mkPrivateNameCore root (arena.str suffix)
    unless record.catalog.catalogName == arenaName "__information_catalog" &&
        record.irredundantCertificateName == arenaName "__catalog_irredundant" do
      throw <| IO.userError s!"companionOwnership: wrong catalog names in {root}"
    checkOwner env root record.catalog.catalogName
    checkOwner env root record.irredundantCertificateName
    for unit in record.theorems do
      let theoremName := fun suffix =>
        if frozen || root.isPrefixOf unit.theoremName then unit.theoremName.str suffix
        else mkPrivateNameCore root (unit.theoremName.str suffix)
      unless unit.unitName == theoremName "__information_unit" &&
          unit.certificateName == theoremName "__lowers_escape" do
        throw <| IO.userError s!"companionOwnership: wrong theorem names in {root}"
      let registrations := InformationRegistry.entries env |>.filter fun entry =>
        entry.registrationModuleName == root && entry.theoremName == unit.theoremName
      unless registrations.size == 1 &&
          (registrations[0]?).any (·.unitName == unit.unitName) do
        throw <| IO.userError "companionOwnership: registry lost actual unit name"
      for name in #[unit.unitName, unit.certificateName, theoremName "__escape_enriched"] do
        checkOwner env root name

unsafe def companionOwnershipBothOrders : IO Unit := do
  initSearchPath (← findSysroot)
  let frozen := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot
  let reflected := `LeanInformationAudit.Tests.Seal.ReflectedRoute
  for roots in #[#[frozen, reflected], #[reflected, frozen]] do
    enableInitializersExecution
    let env ← importModules (roots.map fun root => { module := root }) {}
      (trustLevel := 0) (loadExts := true)
    checkRoot env frozen true
    checkRoot env reflected false
  IO.println "companionOwnershipBothOrders: passed (five families, registry, seals, module owners)"

unsafe def main : IO Unit := do
  try companionOwnershipBothOrders
  catch error => throw <| IO.userError s!"[FAIL] companionOwnershipBothOrders: {error}"
