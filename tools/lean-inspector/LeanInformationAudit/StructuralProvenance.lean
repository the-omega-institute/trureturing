import Lean

namespace LeanInformationAudit
open Lean

namespace DispositionCensus

/-- Provenance from immutable structural theorem source. The registry retains raw
expressions and spellings; it grants no source-writing authority. -/
structure StructuralProvenanceEntry where
  theoremName : Name
  lawArenaConst : Name
  realizationConst : Name
  unitConst : Name
  statementExpr : Expr
  proofExpr : Expr
  levelParams : List Name
  certificateName : Name
  sensitivityWitness : Name := .anonymous
  domainName : Name := .anonymous
  registrationModule : Name
  canonicalArena : Name
  lawArenaSyntax : String := ""
  realizationSyntax : String := ""
  deriving Inhabited

end DispositionCensus

end LeanInformationAudit
