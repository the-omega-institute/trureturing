import LeanInformationAuditRegAnalysis.K2HeadFamiliesGenerator

namespace K2PostprocessGenerator
open Lean Meta K2FactsGenerator K2HeadFamiliesGenerator

private def field (data : Json) (name : String) : MetaM Json :=
  do return ← IO.ofExcept (data.getObjVal? name)

private def stringField (data : Json) (name : String) : MetaM String :=
  do return ← IO.ofExcept <| (← field data name).getStr?

private def arrayField (data : Json) (name : String) : MetaM (Array Json) :=
  do return ← IO.ofExcept <| (← field data name).getArr?

private abbrev SerializedNames := Std.HashMap String (Array Name)

private def serializedNames (env : Environment) : SerializedNames :=
  env.constants.toList.foldl (fun names (name, _) =>
    let text := name.toString
    names.insert text ((names[text]?).getD #[] |>.push name)) {}

private def referenceName (names : SerializedNames) (rowIndex : Nat)
    (field text : String) : MetaM Name := do
  let some choices := names[text]? |
    throwError "postprocess.reference_missing:row={rowIndex}:field={field}:text={text}"
  unless choices.size == 1 do
    throwError "postprocess.reference_ambiguous:row={rowIndex}:field={field}:text={text}:matches={choices.size}"
  return choices[0]!

private def originalReferences (names : SerializedNames) (rowIndex : Nat)
    (row : Json) : MetaM (List Name) := do
  let original ← arrayField row "directReferences"
  original.toList.mapM fun value => do
    let text ← IO.ofExcept value.getStr?
    referenceName names rowIndex "nodes.directReferences" text

private def sourceLeaves (names : SerializedNames) (data : Json) : MetaM NameSet := do
  let inputs := match data.getObjVal? "inputs" >>= Json.getArr? with
    | .ok values => values
    | .error _ => #[]
  let mut result : NameSet := {}
  let mut initialized := false
  for inputIndex in [:inputs.size] do
    let input := inputs[inputIndex]!
    let type ← stringField input "type"
    if type.contains "LeanInformationAudit.Contract.TemplateEnrollment" then return {}
    if type.contains "LeanInformationAudit.Contract.Registration" then
      let current := match input.getObjVal? "sourceLeaves" >>= Json.getArr? with
        | .ok values => values
        | .error _ => #[]
      let leaves ← current.toList.mapM fun value => do
        referenceName names inputIndex "inputs.sourceLeaves" (← IO.ofExcept value.getStr?)
      let set := leaves.foldl (fun set name => set.insert name) ({} : NameSet)
      if initialized then
        result := result.toList.foldl (fun retained name =>
          if set.contains name then retained.insert name else retained) {}
      else
        result := set
        initialized := true
  return result

private def genericRoots (env : Environment) (rows : Array Json) : MetaM NameSet := do
  let mut result : NameSet := {}
  for row in rows do
    unless (← stringField row "part") == "type" && (← arrayField row "path").isEmpty do
      continue
    let name ← IO.ofExcept <| decodeName (← field row "declarationComponents")
    let some info := env.find? name | throwError "postprocess.missing:{name}"
    let levels ← arrayField row "coordinateLevelTrees"
    if levels == (info.levelParams.map (fun level => levelTree (.param level))).toArray then
      result := result.insert name
  return result

private def familyCount (row : Json) : MetaM Nat := do
  match row.getObjVal? "headFamilies" >>= fun data => data.getObjVal? "families" >>= Json.getArr? with
  | .ok values => return values.size
  | .error _ => return 0

private def originalFields : Array String := #[
  "owner", "declName", "declarationComponents", "part", "path", "role", "type",
  "levels", "usedLevels", "headUsedLevels", "coordinateLevels", "coordinateLevelTrees",
  "declarationLevels", "directReferences", "rigidInductive", "hasHead"]

private def preserve (original actual : Json) : MetaM Unit := do
  for name in originalFields do
    unless (← field original name) == (← field actual name) do
      throwError "postprocess.original_payload_changed:{name}"
  if (← familyCount actual) == 0 then
    unless (← field original "head") == (← field actual "head") do
      throwError "postprocess.original_head_changed"

-- All modules share the native key intern and raw declaration caches. Every
-- module still receives a fresh Core context with its original heartbeat limit.
def process (module : Name) (data : Json) (names : SerializedNames) : MetaM Json := do
  let env ← getEnv
  K2FactsGenerator.setScope env module
  K2HeadFamiliesGenerator.resetCompletedHeads
  let original ← arrayField data "nodes"
  let mut rows := #[]
  let mut referenceGroups := #[]
  for index in [:original.size] do
    diagnosticStage.set ("postprocess-original", module, "nodes", [toString index])
    let (actual, additionalReferences) ←
      K2HeadFamiliesGenerator.updateRow module index original[index]!
    preserve original[index]! actual
    rows := rows.push actual
    referenceGroups := referenceGroups.push
      ((← originalReferences names index original[index]!) ++ additionalReferences)
  let leaves ← sourceLeaves names data
  let mut seen ← genericRoots env original
  let mut pending := referenceGroups.toList.flatten
  let mut addedDeclarations := 0
  while let name :: rest := pending do
    pending := rest
    if seen.contains name || (`K2HeadFamiliesPlaceholder).isPrefixOf name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "postprocess.closure_missing:{name}"
    let action : K2FactsGenerator.M Unit := do
      visitRoot name "type" info.levelParams [] #[] info.type
      if (← K2FactsGenerator.protectedNode env name) && !leaves.contains name then
        if let .defnInfo definition := info then
          if definition.safety == .safe then
            let classification ← isPropQuick info.type
            let proof := match classification with | .true => true | _ => false
            unless proof do visitRoot name "value" info.levelParams [] #[] definition.value
    let (_, added) ← action.run #[]
    for addedRow in added do
      let row := toJson addedRow
      let (actual, additionalReferences) ← if addedRow.hasHead then
        K2HeadFamiliesGenerator.updateRow module rows.size row
        else pure (row, [])
      rows := rows.push actual
      pending := addedRow.directReferences ++ additionalReferences ++ pending
    if let .inductInfo inductiveInfo := info then pending := inductiveInfo.ctors ++ pending
    addedDeclarations := addedDeclarations + 1
  let mut families := 0
  let mut keys : Std.HashSet String := {}
  let mut headKeys : Std.HashSet String := {}
  for row in rows do
    families := families + (← familyCount row)
    keys := keys.insert (← stringField row "rawBindingKey")
    headKeys := headKeys.insert (← stringField row "headKey")
  return data.setObjVal! "nodes" (toJson rows)
    |>.setObjVal! "postprocess" (Json.mkObj [
      ("originalNodes", toJson original.size), ("nodes", toJson rows.size),
      ("addedClosureNodes", toJson (rows.size - original.size)),
      ("addedClosureDeclarations", toJson addedDeclarations),
      ("familyCount", toJson families), ("rawBindingKeyCount", toJson keys.size),
      ("headKeyCount", toJson headKeys.size),
      ("originalPayloadPreserved", toJson true),
      ("scope", toJson "actual source coordinates and protected-module policy"),
      ("bindingKeyScope", toJson "single native process; exact raw Expr/type/level collision guard"),
      ("dedupApplied", toJson false)])

end K2PostprocessGenerator

open Lean

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (input, output, moduleList) ← match args with
    | [input, output, moduleList] => pure (input, output, moduleList)
    | _ => throw <| IO.userError "INPUT_DIR OUTPUT_DIR MODULE_LIST required"
  let lines ← IO.FS.lines moduleList
  let modules := lines.filterMap fun line => if line.isEmpty then none else some line.toName
  let opts := ({} : Options).setBool `pp.all true |>.setBool `pp.notation false
    |>.setBool `pp.fullNames true |>.setBool `pp.universes true |>.setBool `pp.proofs true
    |>.set `maxHeartbeats (200000 : Nat)
  enableInitializersExecution
  let imports := modules.map fun module => ({ module, importAll := true } : Import)
  let env ← importModules (imports.push {
    module := `LeanInformationAuditRegAnalysis.K2PostprocessGenerator,
    importAll := true }) opts (loadExts := true)
  let names := K2PostprocessGenerator.serializedNames env
  IO.FS.createDirAll output
  for module in modules do
    IO.println s!"postprocess {module}"
    let path := input ++ "/" ++ module.toString ++ ".json"
    let data ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
    let result ← try
      (K2PostprocessGenerator.process module data names).run' |>.toIO'
        { fileName := "k2-postprocess", fileMap := default, options := opts }
        { env := env.setExporting false }
      catch error =>
        IO.FS.writeFile (output ++ "/" ++ module.toString ++ ".error") error.toString
        let (phase, declaration, part, path) ← K2FactsGenerator.diagnosticStage.get
        IO.eprintln s!"postprocess_failed {module}: {error} phase={phase} declaration={declaration} part={part} path={path}"
        let (hits, misses) ← K2HeadFamiliesGenerator.completedHeadReuse.get
        IO.eprintln s!"postprocess_head_reuse {module}: hits={hits} misses={misses}"
        let (typeHits, typeMisses) ← K2HeadFamiliesGenerator.sourceTypeReuse.get
        IO.eprintln s!"postprocess_source_type_reuse {module}: hits={typeHits} misses={typeMisses}"
        let (closedHits, closedMisses) ← K2HeadFamiliesGenerator.closedSourceReuse.get
        IO.eprintln s!"postprocess_closed_source_reuse {module}: hits={closedHits} misses={closedMisses}"
        continue
    IO.FS.writeFile (output ++ "/" ++ module.toString ++ ".json") (result.compress ++ "\n")
    let errorFile := output ++ "/" ++ module.toString ++ ".error"
    if ← System.FilePath.pathExists errorFile then IO.FS.removeFile errorFile
    IO.println s!"postprocess_done {module}"
    let (hits, misses) ← K2HeadFamiliesGenerator.completedHeadReuse.get
    IO.println s!"postprocess_head_reuse {module}: hits={hits} misses={misses}"
    let (typeHits, typeMisses) ← K2HeadFamiliesGenerator.sourceTypeReuse.get
    IO.println s!"postprocess_source_type_reuse {module}: hits={typeHits} misses={typeMisses}"
    let (closedHits, closedMisses) ← K2HeadFamiliesGenerator.closedSourceReuse.get
    IO.println s!"postprocess_closed_source_reuse {module}: hits={closedHits} misses={closedMisses}"
