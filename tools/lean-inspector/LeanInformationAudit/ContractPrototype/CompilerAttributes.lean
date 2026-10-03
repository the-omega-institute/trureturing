module

public import Lean.Compiler.LCNF.Passes
import all Lean.Compiler.LCNF.ToImpure

public meta section

namespace LeanInformationAudit.ContractPrototype.CompilerAttributes

/-- The pinned compiler keeps this tag private. Expose its metadata object
through a compiler-only import; no repository implementation is evaluated. -/
def taggedReturnAttribute : Lean.TagAttribute := Lean.Compiler.LCNF.taggedReturnAttr

end LeanInformationAudit.ContractPrototype.CompilerAttributes
