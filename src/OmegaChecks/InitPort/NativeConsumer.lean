import Lean

open Lean

private def consumer := "module
prelude
public import OmegaInit.Data.Function
public def firstValue (x y : Omega.Bool) : Omega.Bool :=
  Omega.Function.curry (fun p => Omega.Prod.fst p) x y
public def secondValue (x y : Omega.Bool) : Omega.Bool :=
  Omega.Function.uncurry (fun _ y => y) (Omega.Prod.mk x y)

public def additionFirst (x y : Omega.Bool) : Omega.Bool :=
  @Omega.HAdd.hAdd _ _ _ (@Omega.instHAdd _ (Omega.Add.mk (fun a _ => a))) x y

public def stateSecond (x y : Omega.Bool) : Omega.Bool :=
  Omega.EStateM.Result.casesOn (motive := fun _ => Omega.Bool)
    (@Omega.EStateM.run Omega.Bool Omega.Bool Omega.PUnit (Omega.EStateM.set y) x)
    (fun _ s => s) (fun _ _ => x)
"

/-- Compile a fresh ordinary consumer and execute its packaged IR with both Boolean values. -/
unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected generated library path"
  let lib ← IO.FS.realPath lib
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "PairSmoke.lean") consumer
    let proc ← IO.Process.output {
      cmd := "lean", args := #["-c", "PairSmoke.c", "-o", "PairSmoke.olean", "PairSmoke.lean"]
      cwd := dir, env := #[("LEAN_PATH", some lib.toString)] }
    unless proc.exitCode == 0 do throw <| IO.userError (proc.stdout ++ proc.stderr)
    searchPathRef.set [dir, lib]
    let env ← importModules #[{module := `PairSmoke, importAll := true}] {} (level := .private)
    let some (.inductInfo bool) := env.find? `Omega.Bool | throw <| IO.userError "missing Boolean type"
    unless bool.numParams == 0 && bool.ctors == [`Omega.Bool.false, `Omega.Bool.true] do
      throw <| IO.userError "unexpected Boolean representation"
    let b := mkConst `Omega.Bool
    let arity := .forallE `x b (.forallE `y b b .default) .default
    for (name, selectFirst) in [(`firstValue, true), (`secondValue, false),
        (`additionFirst, true), (`stateSecond, false)] do
      let some ci := env.find? name | throw <| IO.userError s!"missing {name}"
      unless Kernel.isDefEqGuarded env {} ci.type arity do throw <| IO.userError s!"invalid type of {name}"
      let fn ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool) {} name
      for x in [false, true] do
        for y in [false, true] do
          unless fn x y == (if selectFirst then x else y) do
            throw <| IO.userError s!"invalid executable result for {name} at {x}, {y}"

