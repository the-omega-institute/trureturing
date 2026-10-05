import LeanInformationAudit.Contract.SourceAudit

/-!
Interfaces use the command and typeSyntaxKinds tables. Indexed sort families
may use pure matches and logical type constructors. Defaults, attributes,
deriving, quotation, tactic/do/elab nodes and unknown forms fail closed before
compiled companion authorization. Compiled family results must be sorts.
-/

namespace LeanInformationAudit.Contract.InterfaceGuard
open Lean

/-- A sort-valued index family is a contract type. Value-producing
helpers and proof declarations are outside the interface surface. -/
private def indexFamily (declaration : Syntax) : Bool :=
  declaration.isOfKind ``Parser.Command.definition &&
    (declaration[2][1].find? (fun node => node.isOfKind ``Parser.Term.prop ||
      node.isOfKind ``Parser.Term.type || node.isOfKind ``Parser.Term.sort)).isSome

/-- Source types authorize their compiled families, never arbitrary name prefixes. -/
def auditSource (entries : Array SourceAudit.Entry) : Except String Unit := do
  for entry in entries do
    unless entry.command.isOfKind ``Parser.Command.declaration do continue
    let declaration := entry.command[1]
    unless declaration.isOfKind ``Parser.Command.structure ||
        declaration.isOfKind ``Parser.Command.inductive || indexFamily declaration do
      throw s!"contract.interface:authored_non_type:{entry.sourceName}:{declaration.getKind}"

/-- Fixed companion families emitted by the pinned Lean compiler. Constructor
and projection names come from kernel/structure metadata, not source spelling.
An unrecognized compiler product fails closed alongside authored constants. -/
def family (env : Environment) (type : Name) : Except String NameSet := do
  let some (.inductInfo info) := env.find? type
    | throw s!"contract.interface:compiled_type_missing:{type}"
  let mut allowed : NameSet := ({} : NameSet).insert type
  for suffix in #[`rec, `recOn, `casesOn, `noConfusion, `noConfusionType,
      `ctorIdx, `ctorElim, `ctorElimType, `_sizeOf_1, `_sizeOf_inst] do
    allowed := allowed.insert (type ++ suffix)
  for ctor in info.ctors do
    allowed := allowed.insert ctor
    for suffix in #[`inj, `injEq, `noConfusion, `elim, `sizeOf_spec, `_flat_ctor] do
      allowed := allowed.insert (ctor ++ suffix)
  if isStructure env type then
    for projection in getStructureFields env type do
      allowed := allowed.insert (type ++ projection)
  return allowed

private partial def hasAttribute (command : Syntax) : Bool :=
  (command.find? (·.isOfKind ``Parser.Term.attributes)).isSome

/-- Closed syntax table for type declarations. Leaves are identifiers and parser
atoms; every compound term, binder, level and declaration node is named here.
Default values and computation/elaboration/quotation nodes have no entry. -/
private def typeSyntaxKinds : Array Name := #[
  `null, `hygieneInfo, `num,
  ``Parser.Command.declaration, ``Parser.Command.declModifiers,
  ``Parser.Command.docComment, ``Parser.Command.declId,
  ``Parser.Command.structure, ``Parser.Command.structureTk,
  ``Parser.Command.structFields, ``Parser.Command.structSimpleBinder,
  ``Parser.Command.inductive, ``Parser.Command.ctor,
  ``Parser.Command.optDeclSig, ``Parser.Command.optDeriving,
  ``Parser.Command.definition, ``Parser.Command.declValSimple,
  ``Parser.Command.declValEqns, `Lean.Parser.Command.optDefDeriving,
  `Lean.Parser.Termination.suffix,
  ``Parser.Term.optType, ``Parser.Term.matchAltsWhereDecls,
  `Lean.Parser.Term.match, `Lean.Parser.Term.matchAlt, `Lean.Parser.Term.matchAlts,
  `Lean.Parser.Term.matchDiscr, `Lean.Parser.Term.matchDiscrs,
  `Lean.Parser.Term.dotIdent, `Lean.Parser.Term.ellipsis,
  `Lean.Parser.Term.hole, `Lean.Parser.Term.fun, `Lean.Parser.Term.funBinder, `Lean.Parser.Term.basicFun,
  `Lean.Parser.Term.matchAltExpr,
  `«term_=_», `«term_≠_», `«term_∈_», `«term_∧_», `«term_↔_»,
  `«term¬_», `«term_<_», `«term_≤_»,
  `«term_+_»,
  ``Parser.Term.proj, ``Parser.Term.app, ``Parser.Term.arrow, ``Parser.Term.depArrow, ``Parser.Term.forall,
  ``Parser.Term.explicit, ``Parser.Term.explicitUniv,
  ``Parser.Term.paren, ``Parser.Term.hygienicLParen,
  ``Parser.Term.typeSpec, ``Parser.Term.type, ``Parser.Term.sort, ``Parser.Term.prop,
  ``Parser.Term.explicitBinder, ``Parser.Term.implicitBinder,
  ``Parser.Term.strictImplicitBinder, ``Parser.Term.instBinder,
  ``Parser.Term.binderIdent,
  ``Parser.Level.addLit, ``Parser.Level.max, ``Parser.Level.imax, ``Parser.Level.paren]

private partial def typeSyntaxIssue (node : Syntax) : Option Name :=
  if node.isIdent || node.isAtom then none
  else if !typeSyntaxKinds.contains node.getKind then some node.getKind
  else node.getArgs.findSome? typeSyntaxIssue

private partial def hasDerivingClause (command : Syntax) : Bool :=
  (command.find? fun node => node.isAtom && node.getAtomVal == "deriving").isSome

private partial def permittedDeclaration (command : Syntax) : Bool :=
  if !command.isOfKind ``Parser.Command.declaration then false
  else
    let declaration := command[1]
    (declaration.isOfKind ``Parser.Command.structure ||
      (declaration.isOfKind ``Parser.Command.inductive || indexFamily declaration)) &&
      !hasAttribute command && (typeSyntaxIssue command).isNone &&
      !hasDerivingClause declaration

/-- Closed interface command allowlist. It is deliberately lexical and
fail-closed: imports, namespace/section scaffolding, opens, universes, doc
comments and bare type declarations are the complete accepted set. -/
private partial def permittedCommand (command : Syntax) : Bool :=
  if permittedDeclaration command then true
  else if command.isOfKind ``Parser.Command.import ||
      command.isOfKind ``Parser.Command.docComment ||
      command.isOfKind ``Parser.Command.namespace ||
      command.isOfKind ``Parser.Command.section ||
      command.isOfKind ``Parser.Command.end ||
      command.isOfKind ``Parser.Command.open ||
      command.isOfKind ``Parser.Command.universe then true
  else false

/-- Inventory is read from the imported compiled module; no user command runs. -/
def audit (env : Environment) (owner : Name) (entries : Array SourceAudit.Entry)
    : Except String Unit := do
  for entry in entries do
    if entry.originCommand.isOfKind ``Parser.Command.declaration then
      if let some kind := typeSyntaxIssue entry.originCommand then
        throw s!"contract.interface:command_not_allowed:{owner}:type_syntax_not_allowed:{kind}"
    unless permittedCommand entry.originCommand do
      throw s!"contract.interface:command_not_allowed:{owner}:{entry.originCommand.getKind}"
  auditSource entries
  let some idx := env.getModuleIdx? owner
    | throw s!"contract.interface:module_missing:{owner}"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mut allowed : NameSet := {}
  for entry in entries do
    unless SourceAudit.hasInventory entry.command do continue
    let some type := entry.sourceName
      | throw "contract.interface:source_type_missing"
    unless names.contains type do throw s!"contract.interface:compiled_type_missing:{type}"
    if indexFamily entry.command[1] then
      let some (.defnInfo info) := env.find? type
        | throw s!"contract.interface:compiled_type_missing:{type}"
      let rec resultSort : Expr → Bool
        | .forallE _ _ body _ => resultSort body
        | .sort _ => true
        | _ => false
      unless resultSort info.type do throw s!"contract.interface:compiled_non_type:{owner}:{type}"
      let mut pending := #[type]
      while !pending.isEmpty do
        let next := pending.back!
        pending := pending.pop
        if allowed.contains next then continue
        allowed := allowed.insert next
        if let some dependency := env.find? next then
          let used := dependency.type.getUsedConstants ++
            ((dependency.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
          pending := pending ++ used.filter names.contains
    else
      for name in (← family env type).toArray do allowed := allowed.insert name
  for name in names do
    let compilerEquation := match name with
      | .str parent suffix => allowed.contains parent && isReservedName env name &&
          (suffix == "eq_def" || (suffix.startsWith "eq_" && (suffix.drop 3).toString.toNat?.isSome))
      | _ => false
    unless allowed.contains name || compilerEquation do
      throw s!"contract.interface:compiled_non_type:{owner}:{name}"

end LeanInformationAudit.Contract.InterfaceGuard
