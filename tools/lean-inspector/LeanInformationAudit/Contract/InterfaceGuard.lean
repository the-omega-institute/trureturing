import LeanInformationAudit.Contract.SourceAudit

namespace LeanInformationAudit.Contract.InterfaceGuard
open Lean

/-- Source types authorize their compiled families, never arbitrary name prefixes. -/
def auditSource (entries : Array SourceAudit.Entry) : Except String Unit := do
  for entry in entries do
    unless entry.command.isOfKind ``Parser.Command.declaration do continue
    let declaration := entry.command[1]
    unless declaration.isOfKind ``Parser.Command.structure ||
        declaration.isOfKind ``Parser.Command.inductive do
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

private partial def hasTermElaboration (command : Syntax) : Bool :=
  (command.find? fun node => node.isOfKind ``Parser.Term.byTactic ||
    node.isOfKind ``Parser.Term.do || node.getKind.toString.toLower.contains "term_elab").isSome

private partial def hasDerivingClause (command : Syntax) : Bool :=
  (command.find? fun node => node.isAtom && node.getAtomVal == "deriving").isSome

private partial def permittedDeclaration (command : Syntax) : Bool :=
  if !command.isOfKind ``Parser.Command.declaration then false
  else
    let declaration := command[1]
    (declaration.isOfKind ``Parser.Command.structure ||
      declaration.isOfKind ``Parser.Command.inductive) &&
      !hasAttribute command && !hasTermElaboration declaration &&
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
    for name in (← family env type).toArray do allowed := allowed.insert name
  for name in names do
    unless allowed.contains name do
      throw s!"contract.interface:compiled_non_type:{owner}:{name}"

end LeanInformationAudit.Contract.InterfaceGuard
