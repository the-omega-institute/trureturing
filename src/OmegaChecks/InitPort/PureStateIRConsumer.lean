module
import Lean

open Lean

public unsafe def main (args : List String) : IO Unit := do
  let [lib, dir] := args | throw <| IO.userError "expected strict library and consumer directory"
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `PureStateConsumer, importAll := true}] {} (level := .private)
  let b := mkConst `Bool
  let result := mkApp2 (mkConst `Omega.Except [.zero, .zero]) b b
  let arrows (count : Nat) (codomain : Expr) := Nat.repeat (fun t => .forallE .anonymous b t .default) count codomain
  for (name, ty) in [(`pureState, arrows 1 b), (`stateInstances, arrows 1 b),
      (`eliminateOutput, arrows 2 b), (`exceptionState, arrows 3 result), (`exceptionInstances, arrows 3 result)] do
    unless (env.find? name).any (·.type == ty) do throw <| IO.userError s!"unexpected interface for {name}"
  let state ← IO.ofExcept <| env.evalConst (Bool → Bool) {} `pureState
  let except ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool → Except Bool Bool) {} `exceptionState
  let dictState ← IO.ofExcept <| env.evalConst (Bool → Bool) {} `stateInstances
  let dictExcept ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool → Except Bool Bool) {} `exceptionInstances
  let elim ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool) {} `eliminateOutput
  for a in [false, true] do
    unless state a == !a && dictState a == !a do throw <| IO.userError "ST.bind returned the wrong value"
    for raise in [false, true] do
      unless elim raise a == (if raise then a else !a) do throw <| IO.userError "incorrect EST elimination"
      for recover in [false, true] do
        let actual := except raise recover a
        let valid := match actual with
          | .ok value => (!raise || recover) && value == (if raise then a else !a)
          | .error err => raise && !recover && err == a
        unless valid do throw <| IO.userError s!"unexpected EST return for {raise}, {recover}, {a}"
        let viaDict := match dictExcept raise recover a with
          | .ok value => (!raise || recover) && value == !a
          | .error err => raise && !recover && err == !a
        unless viaDict do throw <| IO.userError s!"unexpected EST finalization for {raise}, {recover}, {a}"
