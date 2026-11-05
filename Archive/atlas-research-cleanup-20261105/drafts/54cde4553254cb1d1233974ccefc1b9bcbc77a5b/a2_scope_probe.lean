import LeanInformationAudit.CompiledSourceScope
import LeanInformationAudit.CompiledRegistration
import D5.S3.Topology.Measures.FiniteObservationVariation
import D5.S3.Topology.Measures.NormPreservingLifts
import D5.S3.Topology.Measures.RegularSignedLift
open Lean LeanInformationAudit

partial def paths (e : Expr) (p : Array String := #[]) : Array (Array String) := Id.run do
  let mut out := #[]
  if e.isAppOfArity `D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange.finiteObservationReadout 5 then
    out := out.push p
  match e with
  | .app f a => return out ++ paths f (p.push "fn") ++ paths a (p.push "arg")
  | .forallE _ d b _ | .lam _ d b _ => return out ++ paths d (p.push "domain") ++ paths b (p.push "body")
  | .letE _ d v b _ => return out ++ paths d (p.push "type") ++ paths v (p.push "value") ++ paths b (p.push "body")
  | .mdata _ b | .proj _ _ b => return out ++ paths b (p.push "body")
  | _ => return out

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  let modules := #[`LeanInformationAudit.TemplateEnrollment,
    `D5.S3.Topology.Measures.FiniteObservationVariation]
  for m in modules do RawArtifacts.loadModule m reader
  let store ← reader.get
  let ctx ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store
    `D5.S3.Topology.Measures.FiniteObservationVariation {} {}
  let uname := `D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation
  let some uinfo := store.constants.find? uname | throw <| IO.userError "target_missing"
  let ps := paths uinfo.type
  IO.println (Json.compress <| Json.mkObj [("uniform_paths",toJson ps)])
  let usel : SourceSelection := {owner := `D5.S3.Topology.Measures.FiniteObservationVariation, coordinates := #[0,4,5,23], readouts := #[{path := ps[0]!, stateOperand := some #["fn","arg"]}]}
  let uresult ← try
    let (scope,_) ← ((CompiledSourceScope.resolve uinfo usel).run 524288).run ctx
    pure s!"accepted_scope:coordinates={scope.coordinates.size};readouts={scope.readouts.size}"
  catch e => pure e.toString
  IO.println (Json.compress <| Json.mkObj [("candidate",toJson "uniform_raw_sensor"),("result",toJson uresult)])
  let cases : Array (String × Name × SourceSelection) := #[
    ("functional_typed", `D5.S3.Topology.Measures.NormPreservingLifts.functional_map,
      {owner := `D5.S3.Topology.Measures.NormPreservingLifts, coordinates := #[0,1], readouts := #[{path := Array.replicate 13 "body" ++ #["fn","arg"], stateBinder := 12}]}),
    ("functional_scalar_predicate", `D5.S3.Topology.Measures.NormPreservingLifts.functional_map,
      {owner := `D5.S3.Topology.Measures.NormPreservingLifts, coordinates := #[0,1], readouts := #[{path := Array.replicate 13 "body", stateOperand := some #["arg"], booleanPredicate := true}]}),
    ("functional_dependency_closure_guard", `D5.S3.Topology.Measures.NormPreservingLifts.functional_map,
      {owner := `D5.S3.Topology.Measures.NormPreservingLifts, coordinates := #[0,1,2,4,6,8], readouts := #[{path := Array.replicate 13 "body", stateOperand := some #["arg"], booleanPredicate := true}]}),
    ("regular_typed", `D5.S3.Topology.Measures.RegularSignedLift.regular_add,
      {owner := `D5.S3.Topology.Measures.RegularSignedLift, coordinates := #[0], readouts := #[{path := Array.replicate 10 "body" ++ #["arg"], stateBinder := 6}]}),
    ("regular_boolean_predicate", `D5.S3.Topology.Measures.RegularSignedLift.regular_add,
      {owner := `D5.S3.Topology.Measures.RegularSignedLift, coordinates := #[0], readouts := #[{path := Array.replicate 10 "body", stateOperand := some #["arg"], booleanPredicate := true}]}),
    ("regular_dependency_closure_guard", `D5.S3.Topology.Measures.RegularSignedLift.regular_add,
      {owner := `D5.S3.Topology.Measures.RegularSignedLift, coordinates := #[0,1,4], readouts := #[{path := Array.replicate 10 "body", stateOperand := some #["arg"], booleanPredicate := true}]})]
  for (label,name,sel) in cases do
    let some info := store.constants.find? name | throw <| IO.userError "target_missing"
    let result ← try
      let (scope,_) ← ((CompiledSourceScope.resolve info sel).run 524288).run ctx
      pure s!"accepted_scope:coordinates={scope.coordinates.size};readouts={scope.readouts.size}"
    catch e => pure e.toString
    IO.println (Json.compress <| Json.mkObj [("candidate",toJson label),("result",toJson result)])
  -- Exact current raw source occurrence paths and source telescope ordinals.
  for n in #[`D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation,
      `D5.S3.Topology.Measures.NormPreservingLifts.functional_map,
      `D5.S3.Topology.Measures.RegularSignedLift.regular_add] do
    let some ci := store.constants.find? n | throw <| IO.userError "target_missing"
    let mut e := ci.type
    let mut ordinal := 0
    while let .forallE name domain body bi := e do
      IO.println (Json.compress <| Json.mkObj [("target",toJson n.toString),("ordinal",toJson ordinal),
        ("name",toJson name.toString),("binderInfo",toJson (reprStr bi)),("domain",toJson (reprStr domain))])
      ordinal := ordinal+1
      e := body
