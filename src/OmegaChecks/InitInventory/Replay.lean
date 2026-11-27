module
public import Lean
import Lean.Replay

open Lean
namespace OmegaChecks.InitBoundaries

/-- Recheck the transitive bodies required by a boundary in a kernel containing no axioms.
The pinned private declarations supply the original bodies of imported constants. -/
public def replayBoundaryDependencies (official env : Environment) (roots : List Name) : IO Environment := do
  let mut terms : Std.HashMap Name ConstantInfo := {}
  let mut todo := roots
  while let n :: more := todo do
    todo := more
    if terms.contains n then continue
    let some ci := (official.find? n).orElse fun _ => env.find? n
      | throw <| IO.userError s!"missing witness dependency {n}"
    if let .quotInfo _ := ci then
      -- Replay regenerates the four native primitives from the kernel quotient declaration.
      -- Quot.sound is a separate axiom and still fails the following check.
      unless [`Quot, `Quot.mk, `Quot.ind, `Quot.lift].contains n &&
          official.getModuleIdxFor? n == official.getModuleIdx? `Init.Prelude do
        throw <| IO.userError s!"unexpected quotient primitive in a boundary witness: {n}"
    if ci.isAxiom || ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"forbidden dependency in a boundary witness: {n}"
    terms := terms.insert n ci
    todo := ci.getUsedConstantsAsSet.toList ++ todo
    if let .inductInfo ind := ci then todo := ind.all ++ todo
    if let .ctorInfo ctor := ci then todo := ctor.induct :: todo
  return Environment.ofKernelEnv (← (← mkEmptyEnvironment).toKernelEnv.replay terms)

end OmegaChecks.InitBoundaries
