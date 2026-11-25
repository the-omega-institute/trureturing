import Lean
import OmegaBuild.Commands

open Lean

/-- Imported modules are in dependency order. Keep one import path to the explicit selection. -/
private def mathlibOnlyPaths (env : Environment) : NameMap (List Name) := Id.run do
  let mut paths : NameMap (List Name) := {}
  for owner in env.header.moduleNames, data in env.header.moduleData, i in [:env.header.moduleNames.size] do
    if OmegaBuild.isMathlibOnly env i then
      paths := paths.insert owner [owner]
    else
      for dep in data.imports do
        if let some path := paths.find? dep.module then
          paths := paths.insert owner (owner :: path)
          break
  return paths

/-- Report selection and the published declarations of requested Mathlib-only modules. -/
def main (args : List String) : IO Unit := do
  let path :: first :: rest := args | throw <| IO.userError "expected official search path and module names"
  let names := (first :: rest).map String.toName
  searchPathRef.set (System.SearchPath.parse path)
  let env ← importModules (names.toArray.map fun name => { module := name }) {}
  let paths := mathlibOnlyPaths env
  let mut reasons := []
  let mut declarations := #[]
  for name in names do
    if let some reason := paths.find? name then
      reasons := (name.toString, toJson (reason.map Name.toString)) :: reasons
      let some idx := env.getModuleIdx? name | throw <| IO.userError s!"missing module {name}"
      for decl in env.header.moduleData[idx]!.constNames do
        unless decl.isInternal || isPrivateName decl do
          declarations := declarations.push (name, decl)
  let report : CoreM Json := do
    let mut rows := #[]
    for (owner, decl) in declarations do
      rows := rows.push <| Json.mkObj [("name", toJson decl.toString), ("module", toJson owner.toString),
        ("axioms", toJson ((← collectAxioms decl).map Name.toString))]
    return Json.mkObj [("mathlibOnly", Json.mkObj reasons), ("declarations", toJson rows)]
  let result ← report.toIO' {fileName := "<Omega backend plan>", fileMap := default} {env}
  IO.println result.compress
