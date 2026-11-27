module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
import all Lean.OriginalConstKind
import Lean

open Lean OmegaChecks.InitPort.NativeState

/-- Compile the official state transformer setter using the strict lifted reference write. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  searchPathRef.set [lib]
  let owner := `OmegaInit.Control.StateRef
  let name := `Omega.StateRefT'.set
  let env ← importModules #[{module := owner}] {}
  unless env.contains name do return
  let context ← localEnv env owner #[name]
  let compiled ← compile context do
    modifyEnv fun e => Lean.privateConstKindsExt.insert e name .defn
    (← compileDeclsRef.get) #[name] {}
  writeCode lib owner compiled (codeExtensions ++ #[Lean.privateConstKindsExt.name])
  emitBridge compiled owner none output
