module
public import Lean.Replay

open Lean

namespace OmegaChecks.InitPort

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
