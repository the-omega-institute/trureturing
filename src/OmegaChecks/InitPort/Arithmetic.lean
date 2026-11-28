module
public import Lean.Elab.Tactic.Omega

namespace OmegaChecks.InitPort

open Lean Meta

private def arithmeticRelation (e : Expr) : Bool :=
  let app := e.getAppFn
  let ty := e.getAppArgs[0]?
  [`Eq, `LT.lt, `LE.le].any app.isConstOf && ty.any fun t =>
    [`Nat, `Int, `Fin].any t.getAppFn.isConstOf

/-- Construct a linear arithmetic proof in the pinned environment. Only the proof term is
transferred. The destination checks it and all constants used by the solver. -/
public def arithmeticProof? (source : Environment) (type : Expr) : IO (Option Expr) := do
  let conclusion := type.getForallBody
  unless arithmeticRelation conclusion ||
      (conclusion.iff?.any fun (a, b) => arithmeticRelation a && arithmeticRelation b) do
    return none
  let prove (statement : Expr) : MetaM Expr := forallTelescope statement fun xs goal => do
    let hole ← mkFreshExprSyntheticOpaqueMVar goal
    if let some g ← hole.mvarId!.falseOrByContra then
      g.withContext do Elab.Tactic.Omega.omega (← getLocalHyps).toList g
    mkLambdaFVars xs (← instantiateMVars hole)
  let action : MetaM Expr := forallTelescope type fun xs goal => do
    let result ← match goal.iff? with
      | some (a, b) => do
        pure (mkApp4 (mkConst `Iff.intro) a b (← prove (← mkArrow a b)) (← prove (← mkArrow b a)))
      | none => prove goal
    mkLambdaFVars xs result
  try
    let proof ← action.run' |>.toIO'
      {fileName := "<linear arithmetic>", fileMap := default, options := maxHeartbeats.set {} 1000}
      {env := source}
    if proof.hasFVar || proof.hasMVar || proof.hasLooseBVars then return none
    return some proof
  catch _ => return none

end OmegaChecks.InitPort
