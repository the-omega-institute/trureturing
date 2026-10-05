import Lean

namespace LeanInformationAudit.Contract.SourceLiteral
open Lean

inductive Shape where
  | literal (type : Name)
  | record (type : Name)
  | optional (element : Shape)
  | array (element : Shape)
  | math
  deriving Inhabited

private def lit (n : Name) := Shape.literal n
private def recd (n : Name) := Shape.record (`LeanInformationAudit.Contract ++ n)

/-- Mathematical payloads keep their ordinary elaboration. Metadata has no
default role: every accepted field belongs to the closed contract schema. -/
private def fields (type : Name) : Array (Name × Shape) :=
  let ref := recd `Ref
  let optRef := Shape.optional ref
  let name := lit `Lean.Name
  let options := Shape.array (recd `OptionSetting)
  match type.getString! with
  | "Registration" => #[(`unitName, name), (`realizationName, name),
      (`realizationSource, .optional name), (`generated, lit `Bool), (`arena, recd `ArenaRef),
      (`objectArena, recd `ArenaRef), (`catalog, name), (`localNames, lit `Bool),
      (`realization, recd `Implementation), (`correspondence, .math),
      (`bundleNonempty, .math), (`readout, .math), (`variation, .math),
      (`sensitivity, .math), (`partialSensitivity, .math), (`escapeFrom, .math),
      (`sourceSelection, .optional (recd `SourceSelection)),
      (`continuation, recd `Continuation), (`familyRecord, .math), (`options, options)]
  | "Ref" => #[(`value, .math)]
  | "TypeRef" => #[(`name, name), (`type, .math)]
  | "TemplateEnrollment" => #[(`name, name), (`version, lit `Nat),
      (`constructors, .array (recd `TypeRef)), (`options, options)]
  | "OptionSetting" => #[(`name, name), (`value, recd `OptionValue)]
  | "ReadoutSelection" => #[(`path, .array (lit `String)), (`stateBinder, lit `Nat),
      (`functionOperand, lit `Bool), (`stateOperand, .optional (.array (lit `String))),
      (`booleanPredicate, lit `Bool)]
  | "DefinitionSelection" => #[(`owner, name), (`name, name), (`path, .array (lit `String))]
  | "SourceSelection" => #[(`owner, name), (`definition, .optional (recd `DefinitionSelection)),
      (`coordinates, .array (lit `Nat)), (`readouts, .array (recd `ReadoutSelection))]
  | "ExpectedOccurrence" => #[(`statement, .math), (`proof, .math), (`theoremName, name),
      (`objectArenaName, name), (`statementIdentity, .optional (lit `String)),
      (`registrationModuleName, name)]
  | "RootCatalogData" => #[(`rootId, name), (`expected, .array (recd `ExpectedOccurrence)),
      (`source, .array (recd `ExpectedOccurrence)), (`baseline, .array (recd `ExpectedOccurrence)),
      (`companionPrefix, .optional name)]
  | "RootCatalog" => #[(`data, recd `RootCatalogData)]
  | "ExpectedDeclaration" => #[(`rootId, name), (`occurrence, recd `ExpectedOccurrence)]
  | "Seal" => #[(`rootId, name), (`catalogs, .array (recd `SealCatalog)), (`options, options)]
  | "SealCatalog" => #[(`arenaName, name), (`catalogId, name), (`arena, .math),
      (`size, lit `Nat), (`units, .math), (`nondegenerate, .math), (`bundleNonempty, .math),
      (`stateCard, lit `Nat), (`stateCardEq, .math), (`full, lit `Nat), (`fullEq, .math),
      (`rows, .math), (`collisions, .math), (`conclusion, .math), (`enumeration, .math)]
  | _ => #[]

private def constructorName (env : Environment) (type : Name) (stx : Syntax) : Option Name := do
  let name ← if stx.isIdent then some stx.getId
    else if stx.isOfKind ``Parser.Term.dotIdent then some (type ++ stx[1].getId)
    else none
  let name := if name == `true then `Bool.true else if name == `false then `Bool.false
    else if name == `none then `Option.none else if name == `some then `Option.some
    else name
  let name := if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else name
  let name := if (`Contract).isPrefixOf name then
      name.replacePrefix `Contract `LeanInformationAudit.Contract else name
  let name := if (env.find? name).isSome then name
    else if name.getPrefix == type.getString!.toName then type ++ name.getString!.toName
    else if name.getPrefix.isAnonymous then type ++ name else name
  let some (.ctorInfo info) := env.find? name | none
  if info.induct == type then some name else none

private def arguments (type ctor : Name) : Array Shape :=
  if ctor == `Option.none then #[]
  else if type == `Lean.Name then
    if ctor == `Lean.Name.anonymous then #[]
    else if ctor == `Lean.Name.str then #[lit type, lit `String]
    else #[lit type, lit `Nat]
  else if type == `LeanInformationAudit.Contract.Implementation then
    match ctor.getString! with
    | "source" => #[.math, recd `Ref]
    | "witness" => #[.math, .math, .math, recd `Ref, .math, .math, .math, .math, .math]
    | _ => #[.math, .math, .math, recd `Ref, .math, .math]
  else if type == `LeanInformationAudit.Contract.ArenaRef then #[recd `Ref]
  else if type == `LeanInformationAudit.Contract.Continuation then
    if ctor.getString! == "evidence" then #[recd `Ref] else #[]
  else if type == `LeanInformationAudit.Contract.OptionValue then
    #[lit <| match ctor.getString! with
      | "bool" => `Bool | "nat" => `Nat | "int" => `Int
      | "string" => `String | _ => `Lean.Name]
  else if type == `Nat then
    if ctor == `Nat.zero then #[] else #[lit `Nat]
  else if type == `Int then #[lit `Nat]
  else (fields type).map Prod.snd

/-- Inspect the original parser tree, before any macro or tactic expansion. -/
partial def audit (env : Environment) (shape : Shape) (stx : Syntax)
    (path : String) (forbidden : NameSet := {}) : Except String Unit := do
  if let .math := shape then return
  if forbidden.contains stx.getKind ||
      (stx.getKind == `choice &&
        (stx.find? (fun node => forbidden.contains node.getKind)).isSome) then
    throw s!"contract.source_literal:term_expander:{path}:{stx.getKind}"
  let reject := s!"contract.source_literal:nonliteral:{path}:{stx.getKind}"
  if stx.isOfKind ``Parser.Term.typeAscription then
    let expected := match shape with
      | .literal n | .record n => n
      | _ => Name.anonymous
    let annotation := stx[3][0]
    unless !expected.isAnonymous && annotation.isIdent &&
        #[expected, expected.getString!.toName,
          `Contract ++ expected.getString!.toName].contains annotation.getId do throw reject
    return ← audit env shape stx[1] path forbidden
  if stx.isOfKind ``Parser.Term.paren then
    return ← audit env shape stx[1] path forbidden
  if let .array element := shape then
    unless stx.isOfKind `«term#[_,]» do throw reject
    for item in stx[1].getSepArgs do audit env element item path forbidden
    return
  let type := match shape with
    | .literal n | .record n => n | .optional _ => `Option | _ => .anonymous
  if let .literal n := shape then
    if n == `Lean.Name && stx.isOfKind ``Parser.Term.quotedName then return
    if n == `String && stx.isOfKind `str then return
    if (n == `Nat || n == `Int) && stx.isOfKind `num then return
    if n == `Int && stx.isOfKind `«term-_» then
      return ← audit env (lit `Int) stx[1] path forbidden
  if stx.isOfKind ``Parser.Term.structInst then
    unless (fields type).size > 0 && stx[1].getArgs.isEmpty &&
        stx[3][0].getArgs.isEmpty && stx[4].getArgs.isEmpty do
      throw reject
    for field in stx[2][0].getSepArgs do
      unless field[0][0].isIdent && field[0][1].getArgs.isEmpty &&
          field[1][2].isOfKind ``Parser.Term.structInstFieldDef do
        throw reject
      let key := field[0][0].getId
      let some (_, role) := (fields type).find? (·.1 == key) | throw reject
      audit env role field[1][2][2] (path ++ "." ++ key.toString) forbidden
    return
  let (head, args) := if stx.isOfKind ``Parser.Term.app then (stx[0], stx[1].getArgs)
    else (stx, #[])
  if type == `Int && head.isIdent &&
      #[`OfNat.ofNat, `Neg.neg].contains head.getId then
    unless args.size == 1 do throw reject
    return ← audit env (lit (if head.getId == `OfNat.ofNat then `Nat else `Int)) args[0]! path forbidden
  let roles ← if stx.isOfKind ``Parser.Term.anonymousCtor then
      if (fields type).isEmpty then throw reject else pure ((fields type).map Prod.snd)
    else do
      let some ctor := constructorName env type head | throw reject
      if let .optional element := shape then
        pure <| if ctor == `Option.some then #[element] else #[]
      else pure (arguments type ctor)
  let args := if stx.isOfKind ``Parser.Term.anonymousCtor then stx[1].getSepArgs else args
  unless args.size == roles.size do throw reject
  for i in [:args.size] do audit env roles[i]! args[i]! path forbidden

end LeanInformationAudit.Contract.SourceLiteral
