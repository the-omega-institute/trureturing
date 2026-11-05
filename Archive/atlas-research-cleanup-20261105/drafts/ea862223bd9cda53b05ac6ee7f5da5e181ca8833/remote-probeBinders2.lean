import D5.S3.Topology.Measures.FiniteObservationVariation
import Lean
open Lean Elab Command
namespace ProbeBinders
private def showPath (p : Array String) : String :=
  "[" ++ String.intercalate "," p.toList ++ "]"
partial def walk (e : Expr) (path : Array String) (ctx : Array Name) : CommandElabM Unit := do
  match e with
  | .bvar i =>
      if h : i < ctx.size then
        let n := ctx[ctx.size - i - 1]!
        if n == `J || n == `ε || n == `q || n == `s || n == `a then
          liftIO <| IO.println ("BVAR name=" ++ n.toString ++ " index=" ++ toString i ++ " ctxSize=" ++ toString ctx.size ++ " path=" ++ showPath path)
      else pure ()
  | .app f a =>
      walk f (path.push "fn") ctx
      walk a (path.push "arg") ctx
  | .forallE n d b _ =>
      walk d (path.push "domain") ctx
      walk b (path.push "body") (ctx.push n)
  | .lam n d b _ =>
      walk d (path.push "domain") ctx
      walk b (path.push "body") (ctx.push n)
  | .letE n t v b _ =>
      walk t (path.push "type") ctx
      walk v (path.push "value") ctx
      walk b (path.push "body") (ctx.push n)
  | .proj _ _ b => walk b (path.push "body") ctx
  | .mdata _ b => walk b (path.push "body") ctx
  | _ => pure ()
end ProbeBinders
run_cmd do
  let env ← getEnv
  let name := ``D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation
  let some info := env.find? name | throwError "missing target"
  ProbeBinders.walk info.type #[] #[]
