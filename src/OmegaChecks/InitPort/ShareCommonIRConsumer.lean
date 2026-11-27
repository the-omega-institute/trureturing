module
import Lean
import Lean.Util.ShareCommon

open Lean

/-- Separate allocations let the test observe the sharing performed by the allocator. -/
@[noinline] private def singleton (r : IO.Ref Bool) : IO (List Bool) := do
  return [← r.get]

public unsafe def main (args : List String) : IO Unit := do
  let [lib, dir] := args | throw <| IO.userError "expected the strict library and compiled consumer directory"
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `ShareCommonConsumer, importAll := true}] {} (level := .private)
  let b := mkConst `Omega.Bool
  let list := mkApp (mkConst `Omega.List [.zero]) b
  let prod := mkApp2 (mkConst `Omega.Prod [.zero, .zero]) list list
  let ty := .forallE `factory (mkConst `Omega.ShareCommon.StateFactory)
    (.forallE `x list (.forallE `y list prod .default) .default) .default
  unless (env.find? `sharePair).any (·.type == ty) do throw <| IO.userError "unexpected sharePair interface"
  let some (.inductInfo bool) := env.find? `Omega.Bool | throw <| IO.userError "missing Boolean type"
  unless bool.numParams == 0 && bool.ctors == [`Omega.Bool.false, `Omega.Bool.true] do
    throw <| IO.userError "unexpected Boolean representation"
  let apply ← IO.ofExcept <| env.evalConst
    (_root_.ShareCommon.StateFactory → List Bool → List Bool → List Bool × List Bool) {} `sharePair
  for factory in [Lean.ShareCommon.objectFactory, Lean.ShareCommon.persistentObjectFactory] do
    for x in [false, true] do
      for y in [false, true] do
        let a ← singleton (← IO.mkRef x)
        let b ← singleton (← IO.mkRef y)
        if ptrEq a b then throw <| IO.userError "test inputs must occupy separate cells"
        let (left, right) := apply factory a b
        unless left == a && right == b && ptrEq left right == (x == y) do
          throw <| IO.userError s!"unexpected sharing of {x} and {y}"
