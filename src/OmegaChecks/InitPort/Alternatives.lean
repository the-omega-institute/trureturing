module

public import Lean
public import OmegaChecks.InitPort.Alternatives.Array
public import OmegaChecks.InitPort.Alternatives.ArrayPredicates
public import OmegaChecks.InitPort.Alternatives.ArrayReverse
public import OmegaChecks.InitPort.Alternatives.Constraint
public import OmegaChecks.InitPort.Alternatives.Extract
public import OmegaChecks.InitPort.Alternatives.GeneratedProofs
public import OmegaChecks.InitPort.Alternatives.Integer
public import OmegaChecks.InitPort.Alternatives.List
public import OmegaChecks.InitPort.Alternatives.NatBits
public import OmegaChecks.InitPort.Alternatives.OmegaIntList
public import OmegaChecks.InitPort.Alternatives.Powers
public import OmegaChecks.InitPort.Alternatives.Range
public import OmegaChecks.InitPort.Alternatives.RangeFinite
public import OmegaChecks.InitPort.Alternatives.Word

/-! Read constructive alternatives without importing their environment into the generated library. -/

open Lean

namespace OmegaChecks.InitPort

/-- Register the bodies of named alternatives under their official declaration names. -/
public def loadAlternatives : IO (NameMap ConstantInfo) := do
  let scope := `OmegaChecks.InitPort.Alternatives
  let env ← importModules #[{module := scope}] {} (level := .private)
  let mut alternatives := {}
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    unless owner != scope && scope.isPrefixOf owner do continue
    let localMatcher := fun n => isPrivateName n && env.getModuleIdxFor? n == env.getModuleIdx? owner
    for ci in data.constants do
      let namedProof := match ci.name with
        | .str _ component => ci.isTheorem && component.startsWith "_proof_"
        | _ => false
      unless scope.isPrefixOf ci.name && (!ci.name.isInternalOrNum || namedProof) && !ci.name.hasMacroScopes &&
          !ci.isUnsafe && !ci.isPartial do continue
      let some body := ci.value? (allowOpaque := true) | continue
      let body ← (Meta.deltaExpand body localMatcher (allowOpaque := true)).toIO'
        {fileName := "<constructive alternative>", fileMap := default} {env}
      let some info := (match ci with
        | .thmInfo v => some (ConstantInfo.thmInfo {v with value := body})
        | .defnInfo v => some (ConstantInfo.defnInfo {v with value := body})
        | _ => none) | continue
      alternatives := alternatives.insert (ci.name.replacePrefix scope .anonymous) info
  return alternatives

/-- Names shared between alternatives refer to the implementations at their official sites.
The caller checks each candidate against the full original type in the target kernel. -/
public def alternativeBody? (alternatives : NameMap ConstantInfo) (official : ConstantInfo) : Option Expr := do
  let ci ← alternatives.find? official.name <|> do
    guard official.isTheorem
    let user ← privateToUserName? official.name
    let ci ← alternatives.find? user
    guard (ci.isTheorem && ci.numLevelParams == official.numLevelParams)
    guard (ci.type.instantiateLevelParams ci.levelParams (official.levelParams.map Level.param) == official.type)
    return ci
  guard (ci.numLevelParams == official.numLevelParams)
  let body ← ci.value? (allowOpaque := true)
  let body := body.instantiateLevelParams ci.levelParams (official.levelParams.map Level.param)
  return body.replace fun
    | .const name levels =>
      if (`OmegaChecks.InitPort.Alternatives).isPrefixOf name then
        some (.const (name.replacePrefix `OmegaChecks.InitPort.Alternatives .anonymous) levels)
      else none
    | _ => none

end OmegaChecks.InitPort
