import D5.S3.Topology.Measures.FiniteObservationVariation
import D5.S3.Topology.Measures.NormPreservingLifts
import D5.S3.Topology.Measures.RegularSignedLift
open Lean Elab Command
set_option pp.universes true
run_cmd do
  let names := #[
    ``D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation,
    ``D5.S3.Topology.Measures.NormPreservingLifts.functional_map,
    ``D5.S3.Topology.Measures.RegularSignedLift.regular_add]
  let env ← getEnv
  let rec walk (e : Expr) (ctx : Array Name) (path : Array String) : IO Unit := do
    match e with
    | .bvar i =>
      if h : i < ctx.size then
        let n := ctx[ctx.size - 1 - i]!
        if n == `ε || n == `μ || n == `ν || n == `g || n == `p || n == `s then
          IO.println s!"BVAR name={n} index={i} ctxSize={ctx.size} ctx={ctx} path={path}"
    | .forallE n d b _ => walk d ctx (path.push "domain") >> walk b (ctx.push n) (path.push "body")
    | .lam n d b _ => walk d ctx (path.push "domain") >> walk b (ctx.push n) (path.push "body")
    | .letE n d v b _ => walk d ctx (path.push "domain") >> walk v ctx (path.push "value") >> walk b (ctx.push n) (path.push "body")
    | .app f a => walk f ctx (path.push "fn") >> walk a ctx (path.push "arg")
    | .mdata _ b => walk b ctx (path.push "mdata")
    | .proj _ _ b => walk b ctx (path.push "proj")
    | _ => pure ()
  for n in names do
    IO.println s!"THEOREM {n}"
    let some ci := env.constants.find? n | throw <| IO.userError s!"missing {n}"
    walk ci.type #[] #[]
