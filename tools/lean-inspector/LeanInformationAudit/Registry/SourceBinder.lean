import Lean

namespace LeanInformationAudit

structure SourceBinder where
  /-- Raw path through the binder body. Distinguishes equal-shaped sibling scopes. -/
  path : Array String := #[]
  name : Lean.Name
  info : Lean.BinderInfo
  domain : Lean.Expr
  value : Option Lean.Expr := none
  isLambda : Bool := false
  nondep : Bool := false
  deriving BEq, Inhabited

end LeanInformationAudit
