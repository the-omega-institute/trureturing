import LeanInformationAudit.Registry.SourceScope
import LeanInformationAudit.CompiledSourceOperands

namespace LeanInformationAudit.SourceOperands
open Lean

/-- Compilation callers use the same source linkage and identity calculator. -/
def check (theoremName : Name) (expressions : Array Expr) (fuel : Nat)
    (law : Option Expr := none) (sourceDefinition : Option Expr := none)
    (checkedFiniteArena : Option Expr := none) : Meta.MetaM (Array Name × Nat) :=
  TemplateAudit.runCompiled (CompiledSourceOperands.check theoremName expressions fuel
    law sourceDefinition checkedFiniteArena)

end LeanInformationAudit.SourceOperands
