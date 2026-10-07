import Lean.Elab.Term
import Lean.Data.Json
import LeanInformationAuditInterface.Contract.NodeFactsCore

namespace Reg.Support.CompiledNodeTerm
open Lean Elab Term

private def name (input : Json) : Except String Name := do
  let components ← input.getArr?
  let mut result := Name.anonymous
  for component in components do
    match component with
    | .str text => result := .str result text
    | .num _ => result := .num result (← component.getNat?)
    | _ => throw "name_component"
  return result

private partial def level (input : Json) : Except String Level := do
  let fields ← input.getArr?
  unless !fields.isEmpty do throw "level_tag"
  match ← fields[0]!.getStr? with
  | "zero" =>
    unless fields.size == 1 do throw "zero_arity"
    return .zero
  | "param" =>
    unless fields.size == 2 do throw "param_arity"
    return .param (← name fields[1]!)
  | "succ" =>
    unless fields.size == 2 do throw "succ_arity"
    return .succ (← level fields[1]!)
  | "max" =>
    unless fields.size == 3 do throw "max_arity"
    return .max (← level fields[1]!) (← level fields[2]!)
  | "imax" =>
    unless fields.size == 3 do throw "imax_arity"
    return .imax (← level fields[1]!) (← level fields[2]!)
  | _ => throw "level_tag"

private def termBinder (input : Json) : Except String BinderInfo := do
  match ← input.getStr? with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => throw "term_binder"

private def termChild (previous : Array Expr) (input : Json) : Except String Expr := do
  let index ← input.getNat?
  unless index < previous.size do throw "term_reference"
  return previous[index]!

private def termNode (previous : Array Expr) (input : Json) : Except String Expr := do
  let fields ← input.getArr?
  unless !fields.isEmpty do throw "term_tag"
  let expect : Nat → Except String Unit := fun arity => do
    unless fields.size == arity do throw "term_arity"
  match ← fields[0]!.getStr? with
  | "bvar" =>
    expect 2
    return .bvar (← fields[1]!.getNat?)
  | "sort" =>
    expect 2
    return .sort (← level fields[1]!)
  | "const" =>
    expect 3
    let levels ← (← fields[2]!.getArr?).toList.mapM level
    return .const (← name fields[1]!) levels
  | "app" =>
    expect 3
    return .app (← termChild previous fields[1]!) (← termChild previous fields[2]!)
  | "lam" =>
    expect 5
    return .lam (← name fields[1]!) (← termChild previous fields[3]!)
      (← termChild previous fields[4]!) (← termBinder fields[2]!)
  | "forall" =>
    expect 5
    return .forallE (← name fields[1]!) (← termChild previous fields[3]!)
      (← termChild previous fields[4]!) (← termBinder fields[2]!)
  | "let" =>
    expect 6
    return .letE (← name fields[1]!) (← termChild previous fields[2]!)
      (← termChild previous fields[3]!) (← termChild previous fields[4]!)
      (← fields[5]!.getBool?)
  | "nat" =>
    expect 2
    return .lit (.natVal (← fields[1]!.getNat?))
  | "str" =>
    expect 2
    return .lit (.strVal (← fields[1]!.getStr?))
  | "proj" =>
    expect 4
    return .proj (← name fields[1]!) (← fields[2]!.getNat?)
      (← termChild previous fields[3]!)
  | "mdata" =>
    expect 2
    return .mdata {} (← termChild previous fields[1]!)
  | _ => throw "term_tag"

private def termDag (input : Json) : Except String Expr := do
  let rows ← input.getArr?
  unless !rows.isEmpty do throw "term_empty"
  let mut expressions : Array Expr := #[]
  for row in rows do
    expressions := expressions.push (← termNode expressions row)
  let result := expressions[expressions.size - 1]!
  unless !result.hasFVar && !result.hasMVar && !result.hasLooseBVars do
    throw "term_not_closed"
  return result

/-- A backward-reference constructor DAG builds a closed ordinary term.
 Binder names, modes, raw levels, let flags and metadata edges are retained.
 Metadata annotation maps are empty in the new helper; the source coordinates
 retain their original annotations and every Exact fact remains kernel checked.
 No inference, reduction, comparison or evidence construction occurs here. -/
syntax (name := compiledConstructorTerm) "compiled_term% " str : term

@[term_elab compiledConstructorTerm] private def elaborateConstructor : TermElab := fun stx _ => do
  let some literal := stx[1].isStrLit? | throwError "compiled_term:literal_required"
  match Json.parse literal >>= termDag with
  | .ok expression => return expression
  | .error reason => throwError "compiled_term:{reason}"

private structure Address where
  declaration : Name
  part : String
  path : Array String
  levels : List Level

private def address (input : Json) : Except String Address := do
  let object ← input.getObj?
  unless object.size == 4 do throw "address_fields"
  let declaration ← name (← input.getObjVal? "declaration")
  let part ← (← input.getObjVal? "part").getStr?
  let path ← (← (← input.getObjVal? "path").getArr?).mapM Json.getStr?
  let levels ← (← (← input.getObjVal? "levels").getArr?).toList.mapM level
  return { declaration, part, path, levels }

private def instantiate (params : List Name) (levels : List Level) (expression : Expr) : Expr :=
  let rec substitute : Level → Level
    | .param parameter => ((params.zip levels).find? (·.1 == parameter)).map (·.2)
        |>.getD (.param parameter)
    | .succ nested => .succ (substitute nested)
    | .max left right => .max (substitute left) (substitute right)
    | .imax left right => .imax (substitute left) (substitute right)
    | other => other
  expression.replace fun node => match node with
    | .sort universeLevel => some (.sort (substitute universeLevel))
    | .const constant universeLevels => some (.const constant (universeLevels.map substitute))
    | _ => none

private def construct (env : Environment) (location : Address) : Except String Expr := do
  let some declaration := env.find? location.declaration | throw "declaration_missing"
  unless declaration.levelParams.length == location.levels.length do throw "level_parameters"
  let source ← match location.part with
    | "type" => pure declaration.type
    | "value" =>
      let some value := declaration.value? (allowOpaque := true) | throw "value_missing"
      pure value
    | _ => throw "part"
  let mut node := instantiate declaration.levelParams location.levels source
  let mut telescope : List (Expr → Expr) := []
  for edge in location.path do
    match edge, node with
    | "function", .app function _ => node := function
    | "argument", .app _ argument => node := argument
    | "domain", .lam _ domain _ _ | "domain", .forallE _ domain _ _ => node := domain
    | "body", .lam binder domain body mode | "body", .forallE binder domain body mode =>
      telescope := (fun expression => .lam binder domain expression mode) :: telescope
      node := body
    | "letType", .letE _ domain _ _ _ => node := domain
    | "letValue", .letE _ _ value _ _ => node := value
    | "letBody", .letE binder domain value body nondependent =>
      telescope := (fun expression => .letE binder domain value expression nondependent) :: telescope
      node := body
    | "metadata", .mdata _ body | "projection", .proj _ _ body => node := body
    | _, _ => throw "edge_shape"
  return telescope.foldl (fun expression wrap => wrap expression) node

/-- A literal address constructs the selected compiler term with its original
 binder names, modes, annotations and unsimplified universe constructors. -/
syntax (name := compiledNodeTerm) "compiled_node% " str : term

@[term_elab compiledNodeTerm] private def elaborate : TermElab := fun stx _ => do
  let some literal := stx[1].isStrLit? | throwError "compiled_node:literal_required"
  let decoded ← match Json.parse literal >>= address with
    | .ok location => pure location
    | .error reason => throwError "compiled_node:{reason}"
  match construct (← getEnv) decoded with
  | .ok expression => return expression
  | .error reason => throwError "compiled_node:{reason}:{decoded.declaration}"

private partial def headUnder (remaining : Nat) (parameters : Array Expr)
    (expression : Expr) : TermElabM Expr := do
  match remaining with
  | 0 => do
    Meta.mkLambdaFVars parameters (← Meta.withTransparency .default <| Meta.whnf expression)
      (usedOnly := false) (usedLetOnly := false) (etaReduce := false)
      (generalizeNondepLet := false)
  | remaining + 1 =>
    match expression with
    | .lam binder domain body mode =>
      Meta.withLocalDecl binder mode domain fun parameter =>
        headUnder remaining (parameters.push parameter) (body.instantiate1 parameter)
    | .letE binder domain value body nondependent =>
      Meta.withLetDecl binder domain value (nondep := nondependent) fun parameter =>
        headUnder remaining (parameters.push parameter) (body.instantiate1 parameter)
    | _ => throwError "compiled_head:telescope"

/-- Construct an ordinary helper at compile time from the selected raw node.
 Only its enclosing coordinate telescope is opened; the resulting term still
 requires the ordinary declaration type and ExactMatch evidence checks. -/
syntax (name := compiledHeadTerm) "compiled_head% " str : term

@[term_elab compiledHeadTerm] private def elaborateHead : TermElab := fun stx _ => do
  let some literal := stx[1].isStrLit? | throwError "compiled_head:literal_required"
  let location ← match Json.parse literal >>= address with
    | .ok location => pure location
    | .error reason => throwError "compiled_head:{reason}"
  let expression ← match construct (← getEnv) location with
    | .ok expression => pure expression
    | .error reason => throwError "compiled_head:{reason}:{location.declaration}"
  headUnder (location.path.filter (fun edge => edge == "body" || edge == "letBody")).size
    #[] expression

private partial def nameSyntax : Name → TermElabM (TSyntax `term)
  | .anonymous => `(Lean.Name.anonymous)
  | .str namePrefix component => do
    `(Lean.Name.str $(← nameSyntax namePrefix) $(quote component))
  | .num namePrefix component => do
    `(Lean.Name.num $(← nameSyntax namePrefix) $(quote component))

private partial def levelSyntax : Level → TermElabM (TSyntax `term)
  | .zero => `(Lean.Level.zero)
  | .param parameter => do `(Lean.Level.param $(← nameSyntax parameter))
  | .succ nested => do `(Lean.Level.succ $(← levelSyntax nested))
  | .max left right => do `(Lean.Level.max $(← levelSyntax left) $(← levelSyntax right))
  | .imax left right => do `(Lean.Level.imax $(← levelSyntax left) $(← levelSyntax right))
  | .mvar _ => throwError "compiled_fact:level_metavariable"

private def edgeSyntax (edge : String) : TermElabM (TSyntax `term) :=
  match edge with
  | "function" => `(LeanInformationAudit.Contract.NodeEdge.function)
  | "argument" => `(LeanInformationAudit.Contract.NodeEdge.argument)
  | "domain" => `(LeanInformationAudit.Contract.NodeEdge.domain)
  | "body" => `(LeanInformationAudit.Contract.NodeEdge.body)
  | "letType" => `(LeanInformationAudit.Contract.NodeEdge.letType)
  | "letValue" => `(LeanInformationAudit.Contract.NodeEdge.letValue)
  | "letBody" => `(LeanInformationAudit.Contract.NodeEdge.letBody)
  | "metadata" => `(LeanInformationAudit.Contract.NodeEdge.metadata)
  | "projection" => `(LeanInformationAudit.Contract.NodeEdge.projection)
  | _ => throwError "compiled_fact:edge"

private def locationSyntax (location : Address) : TermElabM (TSyntax `term) := do
  let env ← getEnv
  unless (env.find? location.declaration).isSome do throwError "compiled_fact:declaration_missing"
  let owner := match env.getModuleIdxFor? location.declaration with
    | some index => env.header.modules[index.toNat]!.module
    | none => env.mainModule
  let part ← match location.part with
    | "type" => `(LeanInformationAudit.Contract.NodePart.type)
    | "value" => `(LeanInformationAudit.Contract.NodePart.value)
    | _ => throwError "compiled_fact:part"
  let edges ← location.path.mapM edgeSyntax
  let levels ← location.levels.toArray.mapM levelSyntax
  `(LeanInformationAudit.Contract.NodeCoordinate.mk $(← nameSyntax owner)
    $(← nameSyntax location.declaration) $part [$[$edges],*] [$[$levels],*])

private def literalAddress (literal : Syntax) : TermElabM Address := do
  let some text := literal.isStrLit? | throwError "compiled_fact:literal_required"
  match Json.parse text >>= address with
  | .ok location => pure location
  | .error reason => throwError "compiled_fact:{reason}"

/-- One literal supplies both the raw compiler term and its actual owner coordinate.
 The ordinary constructor elaboration checks its type or proposition. -/
syntax (name := compiledNodeFact) "compiled_fact% " str str : term

@[term_elab compiledNodeFact] private def elaborateFact : TermElab := fun stx expected => do
  let some role := stx[1].isStrLit? | throwError "compiled_fact:role_required"
  let literal : TSyntax `str := ⟨stx[2]⟩
  let atNode ← locationSyntax (← literalAddress literal)
  let operand ← `((@(compiled_node% $literal)))
  let application ← match role with
    | "data" => `(LeanInformationAudit.Contract.NodeFact.data _ $operand $atNode)
    | "type" => `(LeanInformationAudit.Contract.NodeFact.type $operand $atNode)
    | "proof" => `(LeanInformationAudit.Contract.NodeFact.proof _ $operand $atNode)
    | _ => throwError "compiled_fact:role"
  elabTerm application expected

/-- Each endpoint keeps its original compiler address. Definitional matching
 is certified by the existing constructor's ordinary kernel-checked evidence. -/
syntax (name := compiledExactFact) "compiled_exact% " str str : term

@[term_elab compiledExactFact] private def elaborateExact : TermElab := fun stx expected => do
  let left : TSyntax `str := ⟨stx[1]⟩
  let right : TSyntax `str := ⟨stx[2]⟩
  let leftAt ← locationSyntax (← literalAddress left)
  let rightAt ← locationSyntax (← literalAddress right)
  elabTerm (← `(LeanInformationAudit.Contract.NodeFact.exact
    (@(compiled_node% $left)) (@(compiled_node% $right)) $leftAt $rightAt
    LeanInformationAudit.Contract.ExactMatch.evidence)) expected

end Reg.Support.CompiledNodeTerm
