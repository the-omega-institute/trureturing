import LeanInformationAudit.Contract.SourceAudit

namespace LeanInformationAudit.Contract.InterfaceGuard
open Lean

/-- Author declarations are read from source. Compiler-generated constructors,
projections, recursors and theorems are part of their enclosing type declaration. -/
def audit (entries : Array SourceAudit.Entry) : Except String Unit := do
  for entry in entries do
    unless entry.command.isOfKind ``Parser.Command.declaration do continue
    let declaration := entry.command[1]
    unless declaration.isOfKind ``Parser.Command.structure ||
        declaration.isOfKind ``Parser.Command.inductive ||
        declaration.isOfKind ``Parser.Command.coinductive ||
        declaration.isOfKind ``Parser.Command.classInductive do
      throw s!"contract.interface:authored_non_type:{entry.sourceName}:{declaration.getKind}"

end LeanInformationAudit.Contract.InterfaceGuard
