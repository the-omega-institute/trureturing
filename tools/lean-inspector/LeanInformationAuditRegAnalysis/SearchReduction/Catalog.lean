import LeanInformationAuditRegAnalysis.SearchReduction.Runner
import Lean.Elab.Import

/-! The protected commit, rather than delivery imports, determines the catalog. -/
namespace LeanInformationAudit.SearchReduction
open Lean

structure BaselineCatalog where
  commit : String
  frozen : Array Name
  excluded : Array Name
  eligible : Array Name
  loaded : Array Name
  fixtures : Array Name := #[]
  deriving Inhabited

def BaselineCatalog.scope (c : BaselineCatalog) : String :=
  if !c.fixtures.isEmpty then "fixture"
  else if c.loaded.size == c.eligible.size then "B0" else "B_load"

private initialize catalogs : IO.Ref (Std.HashMap String (Array Name × Array (Name × Array Name))) ← IO.mkRef {}

private def gitLines (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output {cmd := "git", args}
  unless result.exitCode == 0 do throw <| IO.userError s!"search.catalog_git_failed: {result.stderr}"
  return result.stdout.splitOn "\n" |>.filter (· != "") |>.toArray

private def readExactly (stream : IO.FS.Handle) (size : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size < size do
    let next ← stream.read (size - bytes.size).toUSize
    if next.isEmpty then throw <| IO.userError "search.catalog_truncated_blob"
    bytes := bytes ++ next
  return bytes

/-- Parse protected source headers with Lean's own module parser. A single git
batch supplies source blobs; neither delivery imports nor candidate pins select B0. -/
private def protectedCatalog (commit : String) : IO (Array Name × Array (Name × Array Name)) := do
  if let some cached := (← catalogs.get)[commit]? then return cached
  let states ← gitLines #["ls-tree", "-r", "--name-only", commit, "--", "Golden/Frozen/state/D5"]
  let frozen := states.filterMap fun path => do
    unless path.endsWith ".lean.json" do none
    let path := (path.drop "Golden/Frozen/state/".length).toString
    return ((path.dropEnd ".lean.json".length).toString.replace "/" ".").toName
  if frozen.isEmpty then throw <| IO.userError "search.catalog_empty"
  let paths ← gitLines #["ls-tree", "-r", "--name-only", commit, "--", "D5"]
  let child ← IO.Process.spawn {
    cmd := "git", args := #["cat-file", "--batch"],
    stdin := .piped, stdout := .piped, stderr := .inherit }
  let (graph, child) ← do
    let (input, child) ← child.takeStdin
    let mut graph := #[]
    for path in paths do
      unless path.endsWith ".lean" do continue
      input.putStrLn s!"{commit}:{path}"
      input.flush
      let blobHeader ← child.stdout.getLine
      let some size := (blobHeader.trimAscii.toString.splitOn " ").getLast!.toNat?
        | throw <| IO.userError s!"search.catalog_missing_blob: {path}"
      let bytes ← readExactly child.stdout size
      discard <| child.stdout.getLine
      let some source := String.fromUTF8? bytes
        | throw <| IO.userError s!"search.catalog_invalid_source: {path}"
      let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
      if messages.hasErrors then throw <| IO.userError s!"search.catalog_header_error: {path}"
      let imports := (Elab.headerToImports header).map (·.module)
      let name := ((path.dropEnd ".lean".length).toString.replace "/" ".").toName
      graph := graph.push (name, imports)
    pure (graph, child)
  let code ← child.wait
  unless code == 0 do throw <| IO.userError "search.catalog_batch_failed"
  let result := (frozen, graph)
  catalogs.modify (·.insert commit result)
  return result

/-- Pollution is the reverse import closure of the registered delivery owners.
Existing prerequisites used only by that delivery remain eligible. -/
def baselineCatalog (commit : String) (delivery : Array Name) (base : Environment) : IO BaselineCatalog := do
  let (frozen, graph) ← protectedCatalog commit
  let mut polluted := delivery.foldl (fun s n => s.insert n) ({} : NameSet)
  let mut changed := true
  while changed do
    changed := false
    for (name, imports) in graph do
      if !polluted.contains name && imports.any polluted.contains then
        polluted := polluted.insert name
        changed := true
  let eligible := frozen.filter (!polluted.contains ·)
  let loaded := base.header.moduleNames.filter (fun n => n.toString.startsWith "D5.")
  let allowed := eligible.foldl (fun s n => s.insert n) ({} : NameSet)
  for n in loaded do
    unless allowed.contains n do throw <| IO.userError s!"search.loaded_outside_catalog: {n}"
  let fixtures := base.header.moduleNames.filter fun n =>
    n.toString.startsWith "LeanInformationAuditRegTests.SearchReduction."
  return {commit, frozen, excluded := frozen.filter polluted.contains, eligible, loaded, fixtures}

/-- Protected ancestors of the target owner, excluding the delivery pollution
closure. Only these already registered modules enter the implication table. -/
def targetBaselineImports (commit : String) (delivery : Array Name)
    (source : Environment) (target : Name) : IO (Array Name) := do
  let (frozen, graph) ← protectedCatalog commit
  let mut polluted := delivery.foldl (fun names n => names.insert n) ({} : NameSet)
  let mut changed := true
  while changed do
    changed := false
    for (name, imports) in graph do
      if !polluted.contains name && imports.any polluted.contains then
        polluted := polluted.insert name
        changed := true
  let some owner := source.getModuleIdxFor? target | return #[]
  let ownerName := source.header.moduleNames[owner.toNat]!
  let mut closure := ({} : NameSet).insert ownerName
  changed := true
  while changed do
    changed := false
    for i in [:source.header.moduleNames.size] do
      if !closure.contains source.header.moduleNames[i]! then continue
      for imported in source.header.moduleData[i]!.imports do
        unless closure.contains imported.module do
          closure := closure.insert imported.module
          changed := true
  return frozen.filter fun name => closure.contains name && !polluted.contains name

end LeanInformationAudit.SearchReduction
