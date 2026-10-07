import LeanInformationAudit.Contract.Literal
import LeanInformationAuditInterface.Contract.NodeFacts

namespace LeanInformationAudit.Contract.NodeFacts
open Lean

structure View where
  find : Name → Option ConstantInfo
  owner : Name → Option Name
  external : Name → Bool
  /-- Independently established source terms and external library leaves stop
  data-body traversal. Their declaration and constructor types remain visited. -/
  sourceLeaf : Name → Bool := fun _ => false

private def bad (reason : String) : Except String α :=
  .error ("contract.node_binding:" ++ reason)

private def tag (find : Name → Option ConstantInfo) (e : Expr) : Except String Name := do
  let e ← Literal.referencedValue find e
  unless e.isConst do bad "nonliteral_tag"
  return e.constName!

def coordinate (find : Name → Option ConstantInfo) (e : Expr) : Except String NodeCoordinate := do
  let fs ← Literal.fields find ``NodeCoordinate e 5
  let owner ← Literal.name "node.owner" (← Literal.resolveReferences find fs[0]!)
  let declaration ← Literal.name "node.declaration" (← Literal.resolveReferences find fs[1]!)
  let part ← match ← tag find fs[2]! with
    | ``NodePart.type => pure NodePart.type
    | ``NodePart.value => pure NodePart.value
    | _ => bad "part"
  let edges ← Literal.list "node.path" (← Literal.resolveReferences find fs[3]!)
  let path ← edges.toList.mapM fun e => do
    match ← tag find e with
    | ``NodeEdge.function => pure NodeEdge.function
    | ``NodeEdge.argument => pure NodeEdge.argument
    | ``NodeEdge.domain => pure NodeEdge.domain
    | ``NodeEdge.body => pure NodeEdge.body
    | ``NodeEdge.letType => pure NodeEdge.letType
    | ``NodeEdge.letValue => pure NodeEdge.letValue
    | ``NodeEdge.letBody => pure NodeEdge.letBody
    | ``NodeEdge.metadata => pure NodeEdge.metadata
    | ``NodeEdge.projection => pure NodeEdge.projection
    | _ => bad "edge"
  let rec level : Nat → Expr → Except String Level
    | 0, _ => bad "level_work"
    | fuel + 1, input => do
      let e ← Literal.referencedValue find input
      let args := e.getAppArgs
      match e.getAppFn.constName?.getD .anonymous with
      | ``Level.zero =>
        unless args.isEmpty do bad "level_arity"
        return .zero
      | ``Level.param =>
        unless args.size == 1 do bad "level_arity"
        return .param (← Literal.name "node.level" args[0]!)
      | ``Level.succ =>
        unless args.size == 1 do bad "level_arity"
        return .succ (← level fuel args[0]!)
      | ``Level.max | ``Level.imax =>
        unless args.size == 2 do bad "level_arity"
        let left ← level fuel args[0]!
        let right ← level fuel args[1]!
        return if e.getAppFn.isConstOf ``Level.max then .max left right else .imax left right
      | _ => bad "level_constructor"
  let levels ← (← Literal.list "node.levels" (← Literal.referencedValue find fs[4]!)).toList.mapM
    (level 256)
  return { owner, declaration, part, path, levels }

/-- A selected open node is closed by the actual surrounding telescope.
 Only explicit universe substitution is performed; no term substitution,
 unfolding, type inference or conversion is performed. -/
def locate (view : View) (location : NodeCoordinate) : Except String Expr := do
  unless view.owner location.declaration == some location.owner do bad s!"owner:{location.declaration}"
  let some info := view.find location.declaration | bad s!"missing:{location.declaration}"
  unless info.levelParams.length == location.levels.length do bad "level_parameters"
  let mut node ← match location.part with
    | .type => pure (Literal.instantiateRawLevels info.levelParams location.levels info.type)
    | .value => match info with
      | .defnInfo defn =>
        unless defn.safety == .safe do bad s!"unsafe:{location.declaration}"
        pure (Literal.instantiateRawLevels info.levelParams location.levels defn.value)
      | _ => bad s!"data_body_required:{location.declaration}"
  let mut telescope : List (Expr → Expr) := []
  for edge in location.path do
    match edge, node with
    | .function, .app f _ => node := f
    | .argument, .app _ a => node := a
    | .domain, .lam _ t _ _ | .domain, .forallE _ t _ _ => node := t
    | .body, .lam n t b bi | .body, .forallE n t b bi =>
      telescope := (fun e => Expr.lam n t e bi) :: telescope
      node := b
    | .letType, .letE _ t _ _ _ => node := t
    | .letValue, .letE _ _ v _ _ => node := v
    | .letBody, .letE n t v b nd =>
      telescope := (fun e => Expr.letE n t v e nd) :: telescope
      node := b
    | .metadata, .mdata _ b | .projection, .proj _ _ b => node := b
    | _, _ => bad s!"edge_shape:{location.declaration}:{repr edge}"
  return telescope.foldl (fun e wrap => wrap e) node

private def binds (view : View) (location value : Expr) : Except String NodeCoordinate := do
  let location ← coordinate view.find location
  unless (← locate view location).equal value do bad s!"operand:{location.declaration}:{repr location.path}"
  return location

inductive BoundRole where
  | data | type | proof | relation
  deriving BEq, Inhabited

structure BoundOperand where
  location : NodeCoordinate
  value : Expr
  role : BoundRole
  type : Option Expr := none
  /-- The sort of the complete certified type, including its telescope. -/
  typeSort : Option Level := none
  relation : Option Name := none
  other : Option Expr := none
  otherLocation : Option NodeCoordinate := none
  proposition : Option Expr := none
  deriving Inhabited

/-- This decodes only the fixed fact constructors and binds their operands.
 The proof fields have already been checked by the Reg compiler. -/
def fact (view : View) (name : Name) : Except String (Array BoundOperand) := do
  let some (.defnInfo info) := view.find name | bad s!"fact_definition:{name}"
  unless info.safety == .safe do bad s!"fact_safety:{name}"
  if !info.type.isConstOf ``NodeFact then
    let mut type := info.type
    let mut value := info.value
    let mut telescope : List (Expr → Expr) := []
    let mut types : List (Expr → Expr) := []
    while true do
      match type with
      | .forallE binder domain body mode =>
        let .lam _ actualDomain actualBody actualMode := value
          | bad "reflection_lambda"
        unless domain.equal actualDomain && mode == actualMode do bad "reflection_telescope"
        telescope := (fun e => Expr.lam binder domain e mode) :: telescope
        types := (fun e => Expr.forallE binder domain e mode) :: types
        type := body
        value := actualBody
      | .letE binder domain assigned body nd =>
        let .letE _ actualDomain actualAssigned actualBody actualNd := value
          | bad "reflection_let"
        unless domain.equal actualDomain && assigned.equal actualAssigned && nd == actualNd do
          bad "reflection_let_telescope"
        let wrap := fun e => Expr.letE binder domain assigned e nd
        telescope := wrap :: telescope
        types := wrap :: types
        type := body
        value := actualBody
      | _ => break
    unless type.isAppOfArity `LeanInformationAudit.Contract.BoolReflection 2 do
      bad s!"fact_type:{name}"
    unless value.getAppFn.isConstOf `LeanInformationAudit.Contract.BoolReflection.mk &&
        value.getAppArgs.size == 5 do bad "reflection_constructor"
    let indices := type.getAppArgs
    let fields := value.getAppArgs
    unless fields[0]!.equal indices[0]! && fields[1]!.equal indices[1]! do
      bad "reflection_indices"
    let left := telescope.foldl (fun e wrap => wrap e) indices[0]!
    let right := telescope.foldl (fun e wrap => wrap e) indices[1]!
    let leftAt ← binds view fields[2]! left
    let rightAt ← binds view fields[3]! right
    let leftType := types.foldl (fun e wrap => wrap e) (mkSort .zero)
    let rightType := types.foldl (fun e wrap => wrap e) (mkConst ``Bool)
    let relation := some `LeanInformationAudit.Contract.BoolReflection
    return #[
      { location := leftAt, value := left, role := .relation, type := some leftType,
        relation, other := some right, otherLocation := some rightAt },
      { location := rightAt, value := right, role := .relation, type := some rightType,
        relation, other := some left, otherLocation := some leftAt }]
  let e ← Literal.referencedValue view.find info.value
  let args := e.getAppArgs
  let .const constructor universes := e.getAppFn | bad "fact_constructor_head"
  let sortLevel ← match universes with
    | [sortLevel] => pure sortLevel
    | _ => bad "fact_universes"
  let one := fun role value location type typeSort => do
    return #[{ location := ← binds view location value, value, role, type, typeSort : BoundOperand }]
  let two := fun constructor left right leftAt rightAt type typeSort => do
    let left ← one .relation left leftAt type typeSort
    let right ← one .relation right rightAt type typeSort
    return (left.map fun item => { item with
      relation := some constructor
      other := some right[0]!.value
      otherLocation := some right[0]!.location }) ++
      (right.map fun item => { item with
        relation := some constructor
        other := some left[0]!.value
        otherLocation := some left[0]!.location })
  match constructor with
  | ``NodeFact.data =>
    unless args.size == 3 do bad "data_arity"
    one .data args[1]! args[2]! (some args[0]!) (some sortLevel)
  | ``NodeFact.type =>
    unless args.size == 2 do bad "type_arity"
    one .type args[0]! args[1]! (some (mkSort sortLevel)) (some (.succ sortLevel))
  | ``NodeFact.proof =>
    unless args.size == 3 do bad "proof_arity"
    let operands ← one .proof args[1]! args[2]! (some args[0]!) (some .zero)
    return operands.map fun operand => { operand with proposition := some args[0]! }
  | ``NodeFact.exact =>
    unless args.size == 6 do bad "exact_arity"
    let evidence ← Literal.referencedValue view.find args[5]!
    unless evidence.getAppFn.isConstOf ``ExactMatch.evidence do bad "exact_evidence_required"
    two ``NodeFact.exact args[1]! args[2]! args[3]! args[4]! (some args[0]!) (some sortLevel)
  | ``NodeFact.equal =>
    unless args.size == 6 do bad "equal_arity"
    two ``NodeFact.equal args[1]! args[2]! args[3]! args[4]! (some args[0]!) (some sortLevel)
  | ``NodeFact.equivalent =>
    unless args.size == 5 do bad "equivalent_arity"
    two ``NodeFact.equivalent args[0]! args[1]! args[2]! args[3]! (some (mkSort .zero))
      (some (.succ .zero))
  | _ => bad s!"fact_constructor:{name}"

/-- Distinct rigid inductive heads after kernel-checked definitional matches
 establish conversion apartness. Mathematical Eq/Iff facts cannot authorize it. -/
def inductiveApart (view : View) (left right : Name) : Except String Unit := do
  let normalized ← #[left, right].mapM fun name => do
    let operands ← fact view name
    let some (.defnInfo info) := view.find name | bad "apart_fact"
    let e ← Literal.referencedValue view.find info.value
    unless e.getAppFn.isConstOf ``NodeFact.exact && operands.size == 2 do bad "apart_exact_required"
    let value := operands[1]!.value
    unless value.isConst do bad "apart_rigid_required"
    let some (.inductInfo _) := view.find value.constName! | bad "apart_inductive_required"
    return value.constName!
  unless normalized[0]! != normalized[1]! do bad "apart_distinct_heads_required"

private def children (location : NodeCoordinate) (node : Expr) : Array (NodeCoordinate × Expr) :=
  let child := fun edge e => ({ location with path := location.path ++ [edge] }, e)
  match node with
  | .app f a => #[child .function f, child .argument a]
  | .lam _ t b _ | .forallE _ t b _ => #[child .domain t, child .body b]
  | .letE _ t v b _ => #[child .letType t, child .letValue v, child .letBody b]
  | .mdata _ b => #[child .metadata b]
  | .proj _ _ b => #[child .projection b]
  | _ => #[]

private instance : Hashable NodeEdge where
  hash edge :=
    let tag : Nat := match edge with
      | .function => 0 | .argument => 1 | .domain => 2 | .body => 3
      | .letType => 4 | .letValue => 5 | .letBody => 6
      | .metadata => 7 | .projection => 8
    hash tag

private instance : Hashable NodePart where
  hash part := hash (part == .value)

private instance : Hashable NodeCoordinate where
  hash location := hash (location.owner, location.declaration, location.part,
    location.path, location.levels)

/-- Every requested raw root is walked, including discarded arguments.
 Only a bound proof fact can cut a subtree. Roots are supplied independently
 by the consuming contract, never selected by the coverage payload. -/
def coverage (view : View) (expected : Array NodeCoordinate) (payload : Expr)
    (fuel : Nat := 524288) : Except String Nat := do
  let fs ← Literal.fields view.find ``NodeCoverage payload 2
  let roots ← (← Literal.list "coverage.roots" (← Literal.resolveReferences view.find fs[0]!)).mapM
    (coordinate view.find)
  unless roots == expected do bad "coverage_roots"
  let names ← (← Literal.list "coverage.facts" (← Literal.resolveReferences view.find fs[1]!)).mapM
    (Literal.name "coverage.fact")
  let mut seenNames : Std.HashSet Name := {}
  for name in names do
    if seenNames.contains name then bad "duplicate_facts"
    seenNames := seenNames.insert name
  let operands := (← names.mapM (fact view)).flatten
  let mut byCoordinate : Std.HashMap NodeCoordinate (Array BoundOperand) := {}
  for operand in operands do
    byCoordinate := byCoordinate.insert operand.location
      ((byCoordinate[operand.location]?).getD #[] |>.push operand)
  let mut pending ← expected.mapM fun location => return (location, ← locate view location, false)
  let mut visited : Std.HashSet (NodeCoordinate × Bool) := {}
  let limit := min 524288 fuel
  let mut remaining := limit
  while let some (location, node, propositionOnly) := pending.back? do
    pending := pending.pop
    if visited.contains (location, propositionOnly) then continue
    unless remaining > 0 do bad "coverage_fuel"
    remaining := remaining - 1
    visited := visited.insert (location, propositionOnly)
    let localOperands := if propositionOnly then #[] else
      (byCoordinate[location]?).getD #[]
    unless propositionOnly do
      for operand in localOperands do
        if let some other := operand.otherLocation then
          pending := pending.push (other, ← locate view other, false)
    let cut := localOperands.find? (fun item => item.role == .proof)
    if let some cut := cut then
      let some proposition := cut.proposition | bad "proof_proposition"
      let mut head := node
      repeat
        unless remaining > 0 do bad "coverage_fuel"
        remaining := remaining - 1
        match head with
        | .app function _ | .mdata _ function => head := function
        | _ => break
      if let .const name _ := head then
        let some info := view.find name | bad s!"closure_missing:{name}"
        let some owner := view.owner name | bad s!"closure_owner:{name}"
        unless !info.isUnsafe && !view.external name do bad s!"closure_unsafe:{name}"
        pending := pending.push ({
          owner, declaration := name, part := .type, path := [],
          levels := info.levelParams.map Level.param }, info.type, false)
      pending := pending.push (location, proposition, true)
    else
      pending := pending ++ (children location node).map (fun (atNode, child) =>
        (atNode, child, propositionOnly))
      if let .const name _ := node then
        let some info := view.find name | bad s!"closure_missing:{name}"
        let some owner := view.owner name | bad s!"closure_owner:{name}"
        unless !info.isUnsafe && !view.external name do bad s!"closure_unsafe:{name}"
        let typeLocation : NodeCoordinate := {
          owner, declaration := name, part := .type, path := [],
          levels := info.levelParams.map Level.param }
        pending := pending.push (typeLocation, info.type, false)
        if let .inductInfo inductiveInfo := info then
          for constructor in inductiveInfo.ctors do
            let some ctor := view.find constructor | bad "closure_constructor"
            let some ctorOwner := view.owner constructor | bad "closure_constructor_owner"
            pending := pending.push ({
              owner := ctorOwner
              declaration := constructor
              part := .type
              path := []
              levels := ctor.levelParams.map Level.param }, ctor.type, false)
        unless view.sourceLeaf name do
          if let .defnInfo defn := info then
            pending := pending.push ({ typeLocation with part := .value }, defn.value, false)
  -- A coordinate outside the traversed roots cannot provide boundary authority.
  unless operands.all (fun item => visited.contains (item.location, false)) do bad "unused_fact_coordinate"
  return limit - remaining

def table (view : View) (value : Expr) (size : Nat) : Except String (Array Expr) := do
  let fs ← Literal.fields view.find ``FiniteTable value 2
  let entries ← Literal.list "table.entries" (← Literal.referencedValue view.find fs[0]!)
  let rows ← entries.mapM fun e => Literal.fields view.find ``TableEntry e 4
  let positions ← rows.mapM fun fs => Literal.nat "table.position" fs[0]!
  unless positions == (List.range size).toArray do bad "table_positions"
  return rows.map (·[2]!)

def exclusion (view : View) (name : Name) : Except String Unit := do
  let some (.defnInfo info) := view.find name | bad "exclusion_definition"
  unless info.safety == .safe do bad "unsafe_definition"
  unless info.type.isAppOfArity ``StatementExclusion 3 do bad "exclusion_type"
  let args := info.type.getAppArgs
  let fs ← Literal.fields view.find ``StatementExclusion info.value 3
  discard <| binds view fs[0]! args[1]!
  discard <| binds view fs[1]! args[2]!

def finiteLift (view : View) (name finite family lift lower : Name) : Except String Unit := do
  let some (.defnInfo info) := view.find name | bad "finite_lift_definition"
  unless info.safety == .safe do bad "unsafe_definition"
  unless info.type.isAppOfArity ``FiniteLiftFacts 4 do bad "finite_lift_type"
  let args := info.type.getAppArgs
  unless (args.zip #[finite, family, lift, lower]).all (fun (e,n) => e.isConstOf n) do
    bad "finite_lift_indices"
  let fs ← Literal.fields view.find ``FiniteLiftFacts info.value 4
  let names ← Literal.list "lift.observations" (← Literal.resolveReferences view.find fs[3]!)
  for e in names do discard <| fact view (← Literal.name "lift.observation" e)

def root (view : View) (name : Name) : Except String Nat := do
  let some (.defnInfo info) := view.find name | bad "root_definition"
  unless info.safety == .safe do bad "unsafe_definition"
  let outer ← Literal.fields view.find ``RootCatalog info.value 1
  let fs ← Literal.fields view.find ``RootCatalogData outer[0]! 5
  let owner ← Literal.name "root.id" (← Literal.resolveReferences view.find fs[0]!)
  unless view.owner name == some owner do bad "root_owner"
  let expected ← Literal.array "root.expected" (← Literal.referencedValue view.find fs[1]!)
  for value in expected do
    let row ← Literal.fields view.find ``ExpectedOccurrence value 6
    let theoremName ← Literal.name "root.theorem" (← Literal.resolveReferences view.find row[2]!)
    let some (.thmInfo target) := view.find theoremName | bad "root_theorem"
    unless row[1]!.isConstOf theoremName && Literal.closed row[1]! &&
        row[1]!.constLevels!.length == target.levelParams.length do bad "root_proof_reference"
  return expected.size

/-- Check the actual catalog binding and publish only its complete unit vector. -/
def sealFacts (view : View) (reference : Expr) (catalogAt : NodeCoordinate)
    : Except String (Array Expr) := do
  let reference := reference.consumeMData
  unless reference.isConst do bad "seal_facts_reference"
  let name := reference.constName!
  let some (.defnInfo info) := view.find name | bad "seal_facts_definition"
  unless info.safety == .safe && !view.external name do bad "unsafe_definition"
  let levels := reference.constLevels!
  unless info.levelParams.length == levels.length do bad "seal_facts_levels"
  let type := Literal.instantiateRawLevels info.levelParams levels info.type
  let value := Literal.instantiateRawLevels info.levelParams levels info.value
  unless type.isAppOfArity ``SealFacts 1 do bad "seal_facts_type"
  unless (← locate view catalogAt).equal type.appArg! do bad "seal_catalog_binding"
  let cs ← Literal.fields view.find ``SealCatalog type.appArg! 15
  let size ← Literal.nat "seal.size" cs[3]!
  let fs ← Literal.fields view.find ``SealFacts value 1
  table view fs[0]! size

end LeanInformationAudit.Contract.NodeFacts
