import LeanInformationAuditRegAnalysis.SearchReduction.DiskLookup

/-! Read-only compiled-input inventory. Fingerprints use the index producer's
module order, module parts and hash formula. No search result is synthesized. -/
namespace LeanInformationAudit.SearchReduction.IndexDomain
open Lean Elab Command

private def readJson (path : System.FilePath) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- Only allocated JSON bytes and scalar hashes survive releasing module data. -/
@[noinline] private unsafe def inventoryModule (module : String)
    (files : Array System.FilePath) (selected : Bool) (output : IO.FS.Handle) :
    IO (UInt64 × Nat) := do
  let (result, regions) ← do
    let main ← readModuleData files[0]!
    let parts ← if !main.1.isModule then pure #[main] else do
      let parts ← readModuleDataParts files
      main.2.free
      pure parts
    let mut fingerprint : UInt64 := 0
    let mut known : NameSet := {}
    let mut count := 0
    let mut partIndex := 0
    for part in parts do
      for info in part.1.constants do
        fingerprint := mixHash fingerprint (mixHash info.type.hash (hash info.value?))
        if known.contains info.name then continue
        known := known.insert info.name
        count := count + 1
        if selected then
          output.putStrLn (Json.mkObj [
            ("module", toJson module), ("name", toJson info.name.toString),
            ("ordinal", toJson count), ("first_part", toJson partIndex),
            ("kind", toJson (declarationKind info)), ("type_hash", toJson info.type.hash),
            ("value_hash", toJson (hash info.value?))]).compress
      partIndex := partIndex + 1
    pure ((fingerprint, if selected then count else 0), parts.map (·.2))
  for region in regions.reverse do region.free
  return result

set_option maxHeartbeats 0 in
run_cmd do
  let some destination ← IO.getEnv "SEARCH_REDUCTION_DOMAIN_DIR" | return
  if destination.isEmpty then return
  let some directory ← IO.getEnv "SEARCH_REDUCTION_INDEX"
    | throwError "index-domain requires SEARCH_REDUCTION_INDEX"
  let headerJson ← readJson (System.FilePath.mk directory / "header.json")
  let header : DiskLookup.Header ← IO.ofExcept (fromJson? headerJson)
  let index ← DiskLookup.openIndex directory header.basis header.mathlib
  let files : Array String ← IO.ofExcept (fromJson? (← readJson
    (System.FilePath.mk directory / "input-files.json")))
  let partitions : Array (Array String) ← IO.ofExcept (fromJson? (← readJson
    (System.FilePath.mk directory / "import-partitions.json")))
  let selected := partitions.foldl (fun names part =>
    part.foldl (fun names name => names.insert name) names) ({} : Std.HashSet String)
  unless files.size % 3 == 0 do throwError "index-domain: malformed input triples"
  IO.FS.createDirAll destination
  let outputPath := System.FilePath.mk destination / "declarations.jsonl"
  let temporary := outputPath.addExtension "tmp"
  let (inputs, declarations, selectedModules) ← IO.FS.withFile temporary .write fun output => do
    let mut inputs : UInt64 := hash
      (DiskLookup.version, header.basis, header.mathlib, Lean.versionString)
    let mut declarations := 0
    let mut selectedModules := 0
    for i in [:files.size / 3] do
      let paths := #[files[i * 3]!, files[i * 3 + 1]!, files[i * 3 + 2]!].map
        System.FilePath.mk
      let path := paths[0]!.toString
      unless path.endsWith ".olean" && (path.splitOn "/lib/lean/").length > 1 do
        throw (IO.userError s!"index-domain: unrecognized module input {path}")
      let relative := (path.splitOn "/lib/lean/").getLast!
      let module := ((relative.dropEnd ".olean".length).toString.replace "/" ".")
      let (fingerprint, count) ← inventoryModule module paths (selected.contains module) output
      declarations := declarations + count
      if selected.contains module then selectedModules := selectedModules + 1
      let mut fileFingerprint := hash (← IO.FS.readBinFile paths[0]!)
      for part in paths[1:] do
        if ← part.pathExists then
          fileFingerprint := mixHash fileFingerprint (hash (← IO.FS.readBinFile part))
      inputs := mixHash inputs (mixHash (hash module.toName)
        (mixHash fingerprint fileFingerprint))
      if i % 1000 == 0 then IO.eprintln s!"INDEX_DOMAIN modules={i} declarations={declarations}"
    return (inputs, declarations, selectedModules)
  IO.FS.rename temporary outputPath
  let summary := Json.mkObj [
    ("header", headerJson), ("computed_inputs", toJson inputs),
    ("inputs_match", toJson (inputs == header.inputs)),
    ("manifest_digest_verified", toJson (index.header.digest == header.digest)),
    ("input_modules", toJson (files.size / 3)), ("selected_modules", toJson selectedModules),
    ("declarations", toJson declarations),
    ("declarations_match", toJson (declarations == header.declarations)),
    ("declaration_scope", toJson "unique declarations per selected compiled module; main/server/private order"),
    ("historical_plus_59", toJson "not investigated")]
  IO.FS.writeFile (System.FilePath.mk destination / "compiled-summary.json")
    (summary.pretty ++ "\n")
  logInfo s!"INDEX_DOMAIN {summary.compress}"
  unless inputs == header.inputs && declarations == header.declarations &&
      selectedModules == header.modules do
    throwError "index-domain: current compiled inputs or declaration population differ from header"

end LeanInformationAudit.SearchReduction.IndexDomain
