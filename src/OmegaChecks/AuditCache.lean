import Lean

open Lean

namespace OmegaChecks.AuditCache

/-- Record all importable parts of the modules actually loaded in this search path. -/
def artifacts (env : Environment) : IO (Array (String × String)) := do
  let mut files := #[]
  for name in env.allImportedModuleNames do
    let path ← findOLean name
    for ext in ["olean", "olean.server", "olean.private", "ir", "ir.sig"] do
      let part := path.withExtension ext
      if ← part.pathExists then
        files := files.push (s!"{name}/{ext}", part.toString)
  return files

/-- Look up one successful invocation. Its output, when present, belongs to the same record. -/
def withResult (kind : String) (args : Array String) (files : Array (String × String))
    (action : IO Unit) (report : Option System.FilePath := none) : IO Unit := do
  unless (← IO.getEnv "OMEGA_AUDIT_CACHE").isSome do return ← action
  IO.FS.withTempDir fun directory => do
    let manifest := directory / "inputs.json"
    let mut inputs := files.push ("driver/omegaAudit", (← IO.appPath).toString)
    inputs := inputs.push ("driver/lean", ((← findSysroot) / "bin" / "lean").toString)
    let data := Json.mkObj [("kind", toJson kind), ("arguments", toJson args), ("files", toJson inputs),
      ("report", toJson (report.map (·.toString)))]
    IO.FS.writeFile manifest data.compress
    let invoke := fun (operation : String) => do
      let process ← IO.Process.spawn {cmd := "python3", args := #["-B", "src/OmegaChecks/audit_cache.py",
        operation, manifest.toString]}
      process.wait
    if (← invoke "lookup") == 0 then return
    action
    discard <| invoke "store"

end OmegaChecks.AuditCache
