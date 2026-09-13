import Lake
import Lake.Load.Workspace

open Lean Lake

/- Read only the current root Lake configuration. Old configurations and source
   bodies are never executed; dependency resolution and updates are not requested. -/
unsafe def main (args : List String) : IO Unit := do
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | throw <| IO.userError "current Lean installation is unavailable"
  let some lake := lake? | throw <| IO.userError "current Lake installation is unavailable"
  if args == ["--plugin-path"] then
    IO.println lake.sharedLib.toString
    return
  let env ← IO.ofExcept (← (Env.compute lake lean elan?).toBaseIO)
  let action : LoggerIO Workspace := loadWorkspaceRoot { lakeEnv := env, wsDir := args.head! }
  let some workspace ← action.toBaseIO | throw <| IO.userError "current Lake configuration is unavailable"
  let module := args[1]!.toName
  let selected := workspace.findModule? module
  let opts := selected.map (·.leanOptions) |>.getD workspace.leanOptions
  let flags := selected.map (fun m => m.weakLeanArgs ++ m.leanArgs) |>.getD workspace.leanArgs
  IO.println (Json.mkObj [("options", toJson opts), ("flags", toJson flags)]).compress
