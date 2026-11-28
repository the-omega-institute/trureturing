module
meta import OmegaChecks.InitInventory.Order
import OmegaChecks.InitInventory.Order
meta import OmegaChecks.InitPort.Alternatives.InternalOrder
import OmegaChecks.InitPort.Alternatives.InternalOrder
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay

open Lean InitKernelPort OmegaChecks.InitPort

/-- Check the pinned formula with the port's definition of admissibility. In the two
flat orders, projecting the pinned CCPO to its partial order removes the missing instance. -/
public def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected strict library"
  let source ← importModules #[{module := `OmegaChecks.InitInventory.Order, importAll := true},
      {module := `OmegaChecks.InitPort.Alternatives.InternalOrder, importAll := true}] {} (level := .private)
  let evidence := `OmegaChecks.InitBoundaries.InternalOrder
  let owner := `Init.Internal.Order.Basic
  let strictAdmissible := `OmegaChecks.InitPort.Alternatives.Lean.Order.admissible
  let small := Level.succ .zero
  for (n, formula, level) in [(`Lean.Order.admissible_or, `OrClosure, small),
      (`Lean.Order.admissible_flatOrder, `FlatClosure, small),
      (`Lean.Order.Option.admissible_eq_some, `OptionClosure, .zero)] do
    let some rule := source.find? n | throw <| IO.userError s!"missing pinned rule {n}"
    let expected := mkConst (evidence ++ formula) [level]
    let replacement n := if n == `Lean.Order.admissible then strictAdmissible else n
    let actual := translate replacement (rule.type.instantiateLevelParams rule.levelParams [level])
    unless rule.isTheorem && rule.levelParams.length == 1 &&
        source.getModuleIdxFor? n == source.getModuleIdx? owner && Kernel.isDefEqGuarded source {} actual expected do
      throw <| IO.userError s!"pinned admissibility statement differs from {formula}"
  searchPathRef.set [lib]
  let strict ← importModules #[{module := `OmegaInit.Internal.Order.Basic}] {} (level := .private)
  let mut kernel := strict.toKernelEnv
  let mut roots := #[]
  for witness in [`weakExcludedMiddleOfOr, `orIffUpperBounds, `flatAdmissibleIffEM, `someAdmissibleIffEM] do
    kernel ← restoreEvidence source kernel (evidence ++ witness)
    roots := roots.push (portName (evidence ++ witness))
  let name := `Lean.Order.admissible_or
  let some rule := source.find? name | throw <| IO.userError s!"missing {name}"
  let actual := translate portName (rule.type.instantiateLevelParams rule.levelParams [small])
  let formula := mkConst (portName (evidence ++ `OrClosure)) [small]
  unless Kernel.isDefEqGuarded (.ofKernelEnv kernel) {} actual formula do
    throw <| IO.userError s!"strict admissibility differs from {formula}"
  let count ← replayStrict kernel roots
  IO.println s!"Verified 3 pinned admissibility formulas and replayed {roots.size} reductions, {count} declarations, zero axioms."
