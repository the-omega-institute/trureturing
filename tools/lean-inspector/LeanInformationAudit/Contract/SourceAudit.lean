import Lean

namespace LeanInformationAudit.Contract.SourceAudit
open Lean

def heads : Array Name := #[
  `LeanInformationAudit.Contract.Registration,
  `LeanInformationAudit.Contract.TemplateEnrollment,
  `LeanInformationAudit.Contract.RootCatalog,
  `LeanInformationAudit.Contract.ExpectedDeclaration,
  `LeanInformationAudit.Contract.Seal]

/-- Type heads and data constructors identify schema inputs without source text. -/
def isInput (info : ConstantInfo) : Bool :=
  match info with
  | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
  | _ =>
    heads.contains (info.type.getForallBody.getAppFn.constName?.getD .anonymous) ||
      (!info.type.getForallBody.isSort &&
        heads.any fun head => (info.value? (allowOpaque := true)).any fun value =>
          value.consumeMData.getLambdaBody.consumeMData.getAppFn.isConstOf (head.str "mk"))

/-- The compiler input schema, independent of the source declaration syntax. -/
def checkInputDefinition (info : ConstantInfo) : Except String DefinitionVal := do
  unless heads.contains (info.type.getAppFn.constName?.getD .anonymous) do
    throw s!"contract.cannot_decode:{info.name}:computed_type"
  let .defnInfo value := info
    | throw s!"contract.cannot_decode:{info.name}:missing_definition_value"
  unless value.safety == .safe do throw s!"contract.discovery:unsafe:{info.name}"
  let closed (e : Expr) := !e.hasFVar && !e.hasMVar && !e.hasLooseBVars && !e.hasLevelMVar
  unless closed value.type && closed value.value do
    throw s!"contract.discovery:open_term:{info.name}"
  return value

end LeanInformationAudit.Contract.SourceAudit
