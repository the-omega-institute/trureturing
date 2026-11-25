import Lean
import Lean.Replay

open Lean

/-- Recompute the pinned compiler's axiom entries on the unsealed, replayed terms.
Its writer sorts entries using the same name order as its import-time binary search. -/
private def compilerAxiomEntries (full : Environment) :
    IO (Name × NameMap EnvExtensionEntry) := do
  for (n, ci) in full.constants.toList do
    if ci.isUnsafe || ci.isPartial || ci.isAxiom || ci matches .quotInfo _ then
      throw <| IO.userError s!"inadmissible strict declaration {n}"
  let checked ← (← mkEmptyEnvironment).toKernelEnv.replay full.constants.map₁
  let env := Environment.ofKernelEnv checked
  let data ← mkModuleData env
  let some (ext, entries) := data.entries.find? (fun e => privateToUserName e.1 == `Lean.exportedAxiomsExt)
    | throw <| IO.userError "compiler failed to export axiom information"
  let names := data.constNames.qsort Name.quickLt
  unless names.size == entries.size && names.size == full.constants.map₁.size do
    throw <| IO.userError "incomplete compiler axiom information after replay"
  let mut byName := {}
  for name in names, entry in entries do byName := byName.insert name entry
  return (ext, byName)

private def writeModule (lib : System.FilePath) (name ext : Name)
    (byName : NameMap EnvExtensionEntry) : IO Unit := do
  let path := modToFilePath lib name "olean"
  let paths := #[path, path.addExtension "server", path.addExtension "private"]
  let old ← readModuleDataParts paths
  let exported := (old.map (·.1))[0]!.constNames.qsort Name.quickLt
  let axioms ← exported.mapM fun n => do
    let some entry := byName.find? n | throw <| IO.userError s!"missing compiler axiom entry for {n}"
    return entry
  let mut parts := #[]
  for (data, _) in old, file in paths do
    let rest := data.entries.filter (·.1 != ext)
    let entries := if axioms.isEmpty then rest else rest.push (ext, axioms)
    parts := parts.push (file, {data with entries})
  saveModuleDataParts name parts

/-- Ordinary imports consult the public axiom extension when bodies are sealed.
Read the persisted exported module level and ask the same API as `#print axioms`. -/
private def checkPublic (imports : Array Import) : IO Unit := do
  unsafe enableInitializersExecution
  let env ← importModules imports {} (loadExts := true) (level := .exported)
  let check : CoreM Nat := do
    let mut count := 0
    for (n, _) in env.constants.toList do
      let axs ← collectAxioms n
      unless axs.isEmpty do throwError "ordinary import attributes axioms {axs} to {n}"
      count := count + 1
    return count
  let count ← check.toIO' {fileName := "<ordinary import>", fileMap := default} {env}
  IO.println s!"Verified zero axiom dependencies for {count} declarations under ordinary imports."

def main (args : List String) : IO Unit := do
  let dir :: names := args | throw <| IO.userError "expected compiled library and module roots"
  if names.isEmpty then throw <| IO.userError "expected at least one module"
  let imports := names.toArray.map fun n => {module := n.toName : Import}
  searchPathRef.set [dir]
  let full ← importModules imports {} (level := .private)
  let (ext, byName) ← compilerAxiomEntries full
  for i in imports do writeModule dir i.module ext byName
  checkPublic imports
