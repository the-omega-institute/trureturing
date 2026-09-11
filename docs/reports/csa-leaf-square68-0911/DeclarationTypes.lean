import D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout
import Lean.Meta
import Lean.Util.CollectAxioms

/- Authored evidence probe for the single explicitly routed module. This does not
   classify repository ownership, compute canonical identities, or write state. -/
open Lean Meta in
run_meta do
  let env := (← getEnv).setExporting false
  let some idx := env.getModuleIdx? `D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout
    | throwError "routed module missing"
  let mut rows : Array Json := #[]
  for name in env.header.moduleData[idx]!.constNames do
    let some info := env.find? name | throwError "constant missing: {name}"
    let rendered ← withOptions (fun o => o.setBool `pp.universes true |>.setBool `pp.fullNames true)
      (ppExpr info.type)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("type", toJson rendered.pretty),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("value_dependencies", toJson
        (info.value? (allowOpaque := true) |>.map (fun e => e.getUsedConstants.map Name.toString)))]
  IO.FS.writeFile "docs/reports/csa-leaf-square68-0911/declaration-types.json"
    ("[\n" ++ String.intercalate ",\n" (rows.toList.map Json.compress) ++ "\n]\n")
