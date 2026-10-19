import LeanInformationAudit.DependencyReadout
import LeanInformationAudit.Registry.Repository

unsafe def main (args : List String) : IO UInt32 := do
  let [request, destination] := args
    | throw <| IO.userError "dependencyReadout requires request and destination paths"
  Lean.initSearchPath (← Lean.findSysroot)
  let workspace ← LeanInformationAudit.Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  Lean.searchPathRef.modify (workspace :: ·)
  let input ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile request))
  let owners ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let result ← LeanInformationAudit.DependencyReadout.readModules (owners.map String.toName)
  IO.FS.writeFile destination (result.compress ++ "\n")
  return 0
