import LeanInformationAuditRegAnalysis.K2FactsGeneratorCore

open Lean Meta
open LeanInformationAudit.Contract

private def declarationCacheSummary : IO Json := do
  let cache ← K2FactsGenerator.declarationRows.get
  let groups := cache.toList.map fun ((declaration, part), rows) =>
    Json.mkObj [("declaration", toJson declaration), ("part", toJson part),
      ("rows", toJson rows.size)]
  return Json.mkObj [("groups", toJson cache.size),
    ("rows", toJson (cache.fold (fun total _ rows => total + rows.size) 0)),
    ("declarations", toJson groups)]

private def failureRowSummary : IO Json := do
  let rows ← K2FactsGenerator.diagnosticFailureRows.get
  let mut groups : Std.HashMap (Name × String) (Nat × Nat × Nat) := {}
  let mut knownNonCanonical := 0
  let mut canonicalLevelRows := 0
  for row in rows do
    let canonicalLevels := row.levels == row.declarationLevels &&
      row.coordinateLevels == row.declarationLevels.map (fun level =>
        K2FactsGenerator.levelText (.param level))
    let excludedOwner := row.owner.getRoot == `Reg
    if excludedOwner || !canonicalLevels then
      knownNonCanonical := knownNonCanonical + 1
    else
      canonicalLevelRows := canonicalLevelRows + 1
    let key := (row.declName, row.part)
    let (count, excluded, roots) := groups[key]?.getD (0, 0, 0)
    groups := groups.insert key (count + 1,
      excluded + if excludedOwner || !canonicalLevels then 1 else 0,
      roots + if !excludedOwner && canonicalLevels && row.path.isEmpty then 1 else 0)
  let declarations := groups.toList.map fun ((declaration, part), (count, excluded, roots)) =>
    Json.mkObj [("declaration", toJson declaration), ("part", toJson part),
      ("rows", toJson count), ("knownNonCanonicalRows", toJson excluded),
      ("canonicalRootRows", toJson roots)]
  return Json.mkObj [("rows", toJson rows.size),
    ("groups", toJson groups.size), ("knownNonCanonicalRows", toJson knownNonCanonical),
    ("canonicalLevelRows", toJson canonicalLevelRows), ("declarations", toJson declarations),
    ("scope", toJson "captured completed row array, grouped outside Meta budget; Reg owner or noncanonical level scope proves noncanonical visitRoot; other rows are canonical-level candidates, and empty paths locate eligible root rows; no invocation lineage inference")]

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (moduleText, output, moduleList) ← match args with
    | [moduleText, output] => pure (moduleText, output, none)
    | [moduleText, output, moduleList] => pure (moduleText, output, some moduleList)
    | _ => throw <| IO.userError "MODULE OUTPUT or --all/--all-once OUTPUT_DIR MODULE_LIST required"
  let all := moduleText == "--all" || moduleText == "--all-once"
  let deferredRetry := moduleText == "--all"
  let module := if all then `Reg else moduleText.toName
  let opts := ({} : Options).setBool `pp.all true |>.setBool `pp.notation false
    |>.setBool `pp.fullNames true |>.setBool `pp.universes true
    |>.setBool `pp.proofs true |>.set `maxHeartbeats (200000 : Nat)
  enableInitializersExecution
  let imports ← if all then do
    let some moduleList := moduleList | throw <| IO.userError "module list required"
    let names ← IO.FS.lines moduleList
    pure <| names.filterMap fun name =>
      if name.isEmpty then none else some ({ module := name.toName, importAll := true } : Import)
    else pure #[{ module, importAll := true }]
  let producerImport : Import := {
    module := `LeanInformationAuditRegAnalysis.K2FactsGenerator
    importAll := true }
  let env ← importModules (imports.push producerImport) opts (loadExts := true)
  let modules := imports.map (·.module)
  let wanted := modules.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut grouped : Std.HashMap Name (Array (Name × ConstantInfo)) := {}
  for (name, info) in env.constants.toList do
    let owner := K2FactsGenerator.ownerOf env name
    if wanted.contains owner then
      grouped := grouped.insert owner ((grouped[owner]?).getD #[] |>.push (name, info))
  if all then IO.FS.createDirAll output
  let mut pending := modules.toList
  let mut retried : NameSet := {}
  while let current :: rest := pending do
    pending := rest
    let infos := (grouped[current]?).getD #[]
    unless !all || infos.any (fun (_, info) =>
        #[``Registration, ``TemplateEnrollment].contains (info.type.getAppFn.constName?.getD .anonymous)) do
      continue
    IO.println s!"extract {current}"
    K2FactsGenerator.setScope env current
    let beforeCounts ← K2FactsGenerator.diagnosticCounts.get
    let beforeSubtreeReuse ← K2FactsGenerator.diagnosticSubtreeReuse.get
    let beforeHeartbeats ← IO.getNumHeartbeats
    let result ← try
      (K2FactsGenerator.collect current infos.toList).run' |>.toIO'
        { fileName := "k2-generator", fileMap := default, options := opts }
        { env := env.setExporting false }
      catch error =>
        IO.eprintln s!"stage: {repr (← K2FactsGenerator.diagnosticStage.get)} nodes={← K2FactsGenerator.diagnosticNodes.get}"
        IO.eprintln s!"diagnostics module={current} completedSnapshots={(K2FactsGenerator.diagnosticDelta beforeCounts (← K2FactsGenerator.diagnosticCounts.get)).compress} rawHeartbeatDelta={(← IO.getNumHeartbeats) - beforeHeartbeats} subtreeReuse={(K2FactsGenerator.subtreeReuseDelta beforeSubtreeReuse (← K2FactsGenerator.diagnosticSubtreeReuse.get)).compress}"
        IO.eprintln s!"declarationCacheSummary module={current} {(← declarationCacheSummary).compress}"
        IO.eprintln s!"failureRowSummary module={current} {(← failureRowSummary).compress}"
        if all then
          IO.FS.writeFile (output ++ "/" ++ current.toString ++ ".error") error.toString
          IO.eprintln s!"extraction_failed {current}: {error}"
          unless !deferredRetry || retried.contains current do
            retried := retried.insert current
            pending := pending ++ [current]
          continue
        else throw error
    IO.println s!"diagnostics module={current} completedSnapshots={(K2FactsGenerator.diagnosticDelta beforeCounts (← K2FactsGenerator.diagnosticCounts.get)).compress} rawHeartbeatDelta={(← IO.getNumHeartbeats) - beforeHeartbeats} subtreeReuse={(K2FactsGenerator.subtreeReuseDelta beforeSubtreeReuse (← K2FactsGenerator.diagnosticSubtreeReuse.get)).compress}"
    IO.FS.writeFile (if all then output ++ "/" ++ current.toString ++ ".json" else output) result.pretty
    if all then
      let errorFile := output ++ "/" ++ current.toString ++ ".error"
      if ← System.FilePath.pathExists errorFile then IO.FS.removeFile errorFile
    IO.println current
