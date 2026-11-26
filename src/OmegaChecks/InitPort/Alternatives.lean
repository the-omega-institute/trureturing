module

public import Lean
public import OmegaChecks.InitPort.Alternatives.AC
public import OmegaChecks.InitPort.Alternatives.Array
public import OmegaChecks.InitPort.Alternatives.ArrayFold
public import OmegaChecks.InitPort.Alternatives.ArrayPredicates
public import OmegaChecks.InitPort.Alternatives.ArrayReverse
public import OmegaChecks.InitPort.Alternatives.ArrayZip
public import OmegaChecks.InitPort.Alternatives.Collect
public import OmegaChecks.InitPort.Alternatives.Constraint
public import OmegaChecks.InitPort.Alternatives.Extract
public import OmegaChecks.InitPort.Alternatives.Fin
public import OmegaChecks.InitPort.Alternatives.Float
public import OmegaChecks.InitPort.Alternatives.GeneratedProofs
public import OmegaChecks.InitPort.Alternatives.GrindAC
public import OmegaChecks.InitPort.Alternatives.GrindField
public import OmegaChecks.InitPort.Alternatives.GrindFieldNorm
public import OmegaChecks.InitPort.Alternatives.GrindLinear
public import OmegaChecks.InitPort.Alternatives.GrindNatModule
public import OmegaChecks.InitPort.Alternatives.GrindOrder
public import OmegaChecks.InitPort.Alternatives.GrindRing
public import OmegaChecks.InitPort.Alternatives.Indexing
public import OmegaChecks.InitPort.Alternatives.Integer
public import OmegaChecks.InitPort.Alternatives.List
public import OmegaChecks.InitPort.Alternatives.ListRange
public import OmegaChecks.InitPort.Alternatives.ListZip
public import OmegaChecks.InitPort.Alternatives.Logic
public import OmegaChecks.InitPort.Alternatives.Name
public import OmegaChecks.InitPort.Alternatives.NatBits
public import OmegaChecks.InitPort.Alternatives.NatDigits
public import OmegaChecks.InitPort.Alternatives.NatFold
public import OmegaChecks.InitPort.Alternatives.NatLinear
public import OmegaChecks.InitPort.Alternatives.NatSOM
public import OmegaChecks.InitPort.Alternatives.NatOrder
public import OmegaChecks.InitPort.Alternatives.OmegaIntList
public import OmegaChecks.InitPort.Alternatives.Option
public import OmegaChecks.InitPort.Alternatives.OrderPackages
public import OmegaChecks.InitPort.Alternatives.Powers
public import OmegaChecks.InitPort.Alternatives.Range
public import OmegaChecks.InitPort.Alternatives.RangeFinite
public import OmegaChecks.InitPort.Alternatives.Rational
public import OmegaChecks.InitPort.Alternatives.UTF8
public import OmegaChecks.InitPort.Alternatives.StringSlice
public import OmegaChecks.InitPort.Alternatives.Word

/-! Read constructive alternatives without importing their environment into the generated library. -/

open Lean

namespace OmegaChecks.InitPort

private def officialNames (orders : NameMap (List Nat)) (expr : Expr) : Expr :=
  expr.replace fun
    | .const name levels =>
      if (`OmegaChecks.InitPort.Alternatives).isPrefixOf name then
        let levels := (orders.find? name).map (fun order => order.map (levels[·]!)) |>.getD levels
        some (.const (name.replacePrefix `OmegaChecks.InitPort.Alternatives .anonymous) levels)
      else none
    | _ => none

/-- Declaration universe binders can be ordered differently by elaboration. Match
their first occurrences in the interface and require conversion in the source kernel. -/
private def officialLevelArgs (env : Environment) (alt official : ConstantInfo) : List Level := Id.run do
  let positional := official.levelParams.map Level.param
  if alt.numLevelParams < 2 || alt.numLevelParams != official.numLevelParams then return positional
  let altParams := (collectLevelParams {} alt.type).params.toList
  let officialParams := (collectLevelParams {} official.type).params.toList
  if altParams.length != alt.numLevelParams || officialParams.length != official.numLevelParams then return positional
  let mapping := altParams.zip officialParams
  let args := alt.levelParams.map fun n => Level.param ((mapping.lookup n).getD n)
  if args == positional then return positional
  let type := officialNames {} alt.type
  if Kernel.isDefEqGuarded env {} (type.instantiateLevelParams alt.levelParams args) official.type then return args
  return positional

/-- Register the bodies of named alternatives under their official declaration names. -/
public def loadAlternatives : IO (NameMap ConstantInfo) := do
  let scope := `OmegaChecks.InitPort.Alternatives
  let env ← importModules #[{module := scope}] {} (level := .private)
  let mut alternatives : NameMap ConstantInfo := {}
  let mut orders : NameMap (List Nat) := {}
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    unless owner != scope && scope.isPrefixOf owner do continue
    let localMatcher := fun n => isPrivateName n && (env.getModuleIdxFor? n).any fun i =>
      scope.isPrefixOf env.header.moduleNames[i]!
    for ci in data.constants do
      let namedProof := match ci.name with
        | .str _ component => ci.isTheorem && component.startsWith "_proof_"
        | _ => false
      unless scope.isPrefixOf ci.name && (!ci.name.isInternalOrNum || namedProof) && !ci.name.hasMacroScopes &&
          !ci.isUnsafe && !ci.isPartial do continue
      let some body := ci.value? (allowOpaque := true) | continue
      let body ← (Meta.deltaExpand body localMatcher (allowOpaque := true)).toIO'
        {fileName := "<constructive alternative>", fileMap := default} {env}
      let name := ci.name.replacePrefix scope .anonymous
      let official := (env.find? name).filter (fun entry => entry.numLevelParams == ci.numLevelParams)
      let params := official.map (·.levelParams) |>.getD ci.levelParams
      let args := official.map (officialLevelArgs env ci) |>.getD (ci.levelParams.map Level.param)
      if args != params.map Level.param then
        let order := params.map fun param => args.idxOf (.param param)
        orders := orders.insert ci.name order
      let type := ci.type.instantiateLevelParams ci.levelParams args
      let body := body.instantiateLevelParams ci.levelParams args
      let some info := (match ci with
        | .thmInfo v => some (ConstantInfo.thmInfo {v with value := body, type, levelParams := params})
        | .defnInfo v => some (ConstantInfo.defnInfo {v with value := body, type, levelParams := params})
        | _ => none) | continue
      alternatives := alternatives.insert name info
  -- References to other alternatives carry universes in their author's binder order.
  -- Rename these after every assignment is known, including forward references.
  let mut aligned : NameMap ConstantInfo := {}
  for (name, ci) in alternatives do
    let value := match ci with
    | .thmInfo v => .thmInfo {v with type := officialNames orders v.type, value := officialNames orders v.value}
    | .defnInfo v => .defnInfo {v with type := officialNames orders v.type, value := officialNames orders v.value}
    | other => other
    aligned := aligned.insert name value
  return aligned

/-- A dependent interface can use different proofs of the same index bounds. The caller
checks that this candidate is well typed and definitionally equal to the complete official type. -/
public def alternativeType? (alternatives : NameMap ConstantInfo) (official : ConstantInfo) : Option Expr := do
  let alt ← alternatives.find? official.name
  guard (official.numLevelParams == alt.numLevelParams)
  return alt.type.instantiateLevelParams alt.levelParams (official.levelParams.map Level.param)

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
  return body.instantiateLevelParams ci.levelParams (official.levelParams.map Level.param)

end OmegaChecks.InitPort
