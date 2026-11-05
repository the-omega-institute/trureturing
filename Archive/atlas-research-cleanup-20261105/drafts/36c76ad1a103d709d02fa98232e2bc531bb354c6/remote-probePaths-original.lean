import D5.S3.Topology.Measures.FiniteObservationVariation
import Lean
open Lean Elab Command
namespace ProbePaths
partial def walk (target : Name) (e : Expr) (path : Array String) : CommandElabM Unit := do
  if e.getAppFn.constName? == some target then
    logInfo m!"HIT path={path.toList} expr={e}"
  match e with
  | .app f a =>
      walk target f (path.push "fn")
      walk target a (path.push "arg")
  | .forallE _ d b _ =>
      walk target d (path.push "domain")
      walk target b (path.push "body")
  | .lam _ d b _ =>
      walk target d (path.push "domain")
      walk target b (path.push "body")
  | .letE _ t v b _ =>
      walk target t (path.push "type")
      walk target v (path.push "value")
      walk target b (path.push "body")
  | .proj _ _ b => walk target b (path.push "body")
  | .mdata _ b => walk target b (path.push "body")
  | _ => pure ()
end ProbePaths

run_cmd do
  let env ← getEnv
  let name := ``D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation
  let some info := env.find? name | throwError "missing target"
  ProbePaths.walk ``D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange.finiteObservationReadout info.type #[]
