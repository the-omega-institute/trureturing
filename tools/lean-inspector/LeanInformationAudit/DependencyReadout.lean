import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms

namespace LeanInformationAudit.DependencyReadout
open Lean

private def textName (name : Name) : String := String.ofList name.toString.toList

private def namesJson (names : Array Name) : Json :=
  toJson ((names.map textName).qsort (· < ·))

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declaration (owner : Name) (info : ConstantInfo) : Json :=
  let (types, values) := CompiledAxioms.declarationDependencyParts info
  Json.mkObj [
    ("name", toJson (textName info.name)), ("module", toJson (textName owner)),
    ("user_name", toJson (textName (privateToUserName info.name))),
    ("private", toJson (isPrivateName info.name)),
    ("internal", toJson (privateToUserName info.name).isInternalDetail),
    ("kind", toJson (kind info)), ("type", namesJson types),
    ("value", values.map namesJson |>.getD Json.null)]

/-- Read the complete own public/server/private chain with the report's existing
reader. No imports or declarations outside the explicit domain are expanded.
All returned strings are detached before releasing the mapped compiler regions. -/
@[noinline] private unsafe def projectModule (owner : Name) : IO (Json × Array CompactedRegion) := do
  let (data, regions) ← RawArtifacts.readOwn owner
  let declarations := data.constants.map (declaration owner)
  return (Json.mkObj [("module", toJson (textName owner)), ("status", toJson "ok"),
    ("imports", namesJson (data.imports.map (·.module))),
    ("declarations", Json.arr declarations)], regions)

unsafe def readModules (owners : Array Name) : IO Json := do
  let mut modules := #[]
  for owner in owners do
    try
      let (result, regions) ← projectModule owner
      for region in regions.reverse do region.free
      modules := modules.push result
    catch error =>
      modules := modules.push (Json.mkObj [("module", toJson (textName owner)),
        ("status", toJson "read_failed"), ("detail", toJson error.toString),
        ("imports", toJson (#[] : Array String)), ("declarations", toJson (#[] : Array Json))])
  return Json.mkObj [("modules", Json.arr modules)]

end LeanInformationAudit.DependencyReadout
