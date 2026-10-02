import Lean

namespace LeanInformationAudit
open Lean

structure EscapeFromIdentity where
  name : Name
  typeIdentity : String
  objectIdentity : String
  deriving Inhabited, BEq

structure EscapeContinuationIdentity where
  kind : String
  declarationName : Option Name := none
  statementIdentity : Option String := none
  chainName : Option Name := none
  deriving Inhabited, BEq

structure EscapeRecordEvidence where
  fromObject : Option EscapeFromIdentity := none
  continuation : Option EscapeContinuationIdentity := none
  bridgeKind : String := "legacy"
  deriving Inhabited, BEq

end LeanInformationAudit
