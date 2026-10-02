import LeanInformationAuditInterface.Records
import LeanInformationAudit.EscapeEvidence

namespace LeanInformationAudit
open Lean

structure TemplateOccurrenceKey where
  root : Name
  registrationModule : Name
  theoremName : Name
  objectArena : Name
  catalog : Name
  deriving BEq, Hashable, Inhabited

structure TemplateOccurrenceEvent where
  key : TemplateOccurrenceKey
  unitName : Name
  realizationName : Name
  statement : Expr
  levelParams : List Name
  statementIdentity : String
  arena : Expr
  registrationSource : String
  registrationSourceIdentity : String
  deriving Inhabited

structure TemplateBindingClaim where
  key : TemplateOccurrenceKey
  arena : Expr
  descriptor : Option Expr
  resolutionDiagnostic : Option String := none
  escapeInput : EscapeRecordInput := {}
  owner : Name
  deriving Inhabited

namespace TemplateAudit

structure DependencyIdentity where
  name : Name
  owner : Name
  typeIdentity : String
  bodyIdentity : String
  deriving Inhabited

end TemplateAudit

structure TemplateBindingCertificate where
  evidenceRef : String
  key : TemplateOccurrenceKey
  planIdentity : String
  descriptorIdentity : String
  actualIdentity : String
  argumentInputs : Array TemplateAudit.DependencyIdentity
  extractionInputs : Array TemplateAudit.DependencyIdentity
  escape : EscapeRecordEvidence := {}
  /-- Producer-created scope and reconstruction evidence for the source-bound plan variant. -/
  sourceBinding : Option Json := none
  deriving Inhabited

inductive TemplateBindingResult where
  | undeclared
  | declaredUnresolved (diagnostic : String)
  | declaredValidated (certificate : TemplateBindingCertificate)
  deriving Inhabited

structure BindingRecord where
  schemaVersion : Nat := 1
  compatibilityVersion : Nat := 7
  occurrence : TemplateOccurrenceEvent
  descriptor : Option Expr
  bindingOwner : Option Name
  result : TemplateBindingResult
  escape : EscapeRecordEvidence := {}
  deriving Inhabited

end LeanInformationAudit
