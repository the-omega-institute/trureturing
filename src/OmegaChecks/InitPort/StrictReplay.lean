module
public import Lean.Replay
public import OmegaChecks.InitPort.Translation

open Lean InitKernelPort

namespace OmegaChecks.InitPort

/-- Import the proof helpers from the inventory and use the existing strict declarations for Init. -/
public partial def restoreEvidence (source : Environment) (kernel : Kernel.Environment)
    (n : Name) : IO Kernel.Environment := do
  let name := portName n
  if (kernel.find? name).isSome then return kernel
  let some proof := source.find? n | throw <| IO.userError s!"missing source {n}"
  let some modIdx := source.getModuleIdxFor? n | throw <| IO.userError s!"missing module {n}"
  unless (`OmegaChecks.InitInventory).isPrefixOf source.header.moduleNames[modIdx.toNat]! do
    throw <| IO.userError s!"missing strict dependency {name}"
  let mut kernel := kernel
  for dep in proof.getUsedConstantsAsSet do
    kernel ← restoreEvidence source kernel dep
  let type := translate portName proof.type
  let some body := proof.value? (allowOpaque := true) | throw <| IO.userError s!"missing proof body {n}"
  let value := translate portName body
  let decl ← match proof with
    | .thmInfo t => pure (Declaration.thmDecl {t with name, type, value, all := [name]})
    | .defnInfo d => pure (Declaration.defnDecl {d with name, type, value, all := [name]})
    | _ => throw <| IO.userError s!"unsupported witness dependency {name}"
  let .ok next := kernel.addDeclCore 0 1000 decl none | throw <| IO.userError s!"failed to check evidence {name}"
  return next

/-- Replay the named declarations and their transitive dependencies in an empty kernel. -/
public def replayStrict (env : Kernel.Environment) (roots : Array Name) : IO Nat := do
  let mut closure : Std.HashMap Name ConstantInfo := {}
  let mut pending := roots.toList
  while let name :: rest := pending do
    pending := rest
    if closure.contains name then continue
    let some info := env.find? name | throw <| IO.userError s!"missing strict declaration {name}"
    if info.isAxiom || info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"inadmissible strict dependency {name}"
    closure := closure.insert name info
    pending := info.getUsedConstantsAsSet.toList ++ pending
  let _ ← (← mkEmptyEnvironment).toKernelEnv.replay closure
  return closure.size

end OmegaChecks.InitPort
