import LeanInformationAuditRegAnalysis.K2FactsGenerator
import LeanInformationAuditRegTests.Fixtures.Provenance

namespace K2ProvenanceFactsGenerator
open Lean Meta K2FactsGenerator

def fixture : Name := `LeanInformationAuditRegTests.Fixtures.Provenance

def readouts : Array Name := #[
  `AllowlistBoundaries.plain, `AllowlistBoundaries.proofArgument,
  `AllowlistBoundaries.forbiddenArgument, `AllowlistBoundaries.hiddenPayload]

def roots : Array (Name × String) :=
  #[(`AllowlistBoundaries.target, "type")] ++
    readouts.flatMap (fun name => #[(name, "type"), (name, "value")])

def collect : MetaM Json := do
  let env ← getEnv
  K2FactsGenerator.setScope env fixture
  let action : K2FactsGenerator.M (Array Row) := do
    for (name, part) in roots do
      let some info := env.find? name | throwError "missing provenance root {name}"
      let expression ← if part == "type" then pure info.type else
        match info with
        | .defnInfo definition => pure definition.value
        | _ => throwError "provenance root has no data body {name}"
      visitRoot name part info.levelParams [] #[] expression
    let mut seen : NameSet := {}
    let initial ← get
    let mut pending := initial.toList.flatMap (·.directReferences)
    while let name :: rest := pending do
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | throwError "missing provenance dependency {name}"
      let start := (← get).size
      visitRoot name "type" info.levelParams [] #[] info.type
      if let .inductInfo inductiveInfo := info then
        pending := inductiveInfo.ctors ++ pending
      if ← K2FactsGenerator.protectedNode env name then
        if let .defnInfo definition := info then
          if definition.safety == .safe && !(← isProp info.type) then
            visitRoot name "value" info.levelParams [] #[] definition.value
      let added := (← get).extract start (← get).size
      pending := added.toList.flatMap (·.directReferences) ++ pending
    get
  let (nodes, _) ← action.run #[]
  let roots ← roots.mapM fun (name, part) => do
    let some info := env.find? name | throwError "missing provenance root {name}"
    return Json.mkObj [
      ("owner", toJson (ownerOf env name)), ("declName", toJson name),
      ("part", toJson part), ("path", toJson ([] : List String)),
      ("levels", toJson info.levelParams),
      ("coordinateLevels", toJson (info.levelParams.map (fun name => levelText (.param name))))]
  return Json.mkObj [("module", toJson fixture), ("roots", toJson roots), ("nodes", toJson nodes)]

def publish : MetaM Unit := do
  let some output ← IO.getEnv "K2_PROVENANCE_FACTS_OUTPUT"
    | throwError "K2_PROVENANCE_FACTS_OUTPUT required"
  let options := (← getOptions).setBool `pp.all true |>.setBool `pp.notation false
    |>.setBool `pp.fullNames true |>.setBool `pp.universes true |>.setBool `pp.proofs true
  let data ← withOptions (fun _ => options) collect
  IO.FS.writeFile output (data.pretty ++ "\n")

run_meta publish

end K2ProvenanceFactsGenerator
