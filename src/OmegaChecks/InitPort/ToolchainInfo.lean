module
import Lean
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean OmegaChecks.InitPort.NativeState

/-- Check the getters in the initialized shared library used by ordinary IR consumers. -/
public unsafe def main (args : List String) : IO Unit := do
  let [library] := args | throw <| IO.userError "expected the strict library"
  searchPathRef.set [library]
  let env ← importModules #[{module := `OmegaInit.Meta.Defs, importAll := true}] {} (level := .private)
  for (getter, value, expected) in [
      (`Omega.Lean.getGithash, `Omega.Lean.githash, Lean.githash),
      (`Omega.Lean.version.getSpecialDesc, `Omega.Lean.version.specialDesc, Lean.version.specialDesc)] do
    let get ← IO.ofExcept <| env.evalConst (Unit → StringRepr) {} getter
    let stored ← IO.ofExcept <| env.evalConst StringRepr {} value
    let bytes := expected.toUTF8.data.toList.map UInt8.toNat
    unless (get ()).bytes.data == bytes && stored.bytes.data == bytes do throw <| IO.userError s!"incorrect pinned {getter} or {value}"
  for (getter, expected) in [(`Omega.Lean.version.getIsRelease, Lean.version.isRelease),
      (`Omega.Lean.Internal.isStage0, Lean.Internal.isStage0 ()),
      (`Omega.Lean.Internal.hasLLVMBackend, Lean.Internal.hasLLVMBackend ())] do
    let get ← IO.ofExcept <| env.evalConst (Unit → Bool) {} getter
    unless get () == expected do throw <| IO.userError s!"incorrect pinned compiler flag {getter}"
