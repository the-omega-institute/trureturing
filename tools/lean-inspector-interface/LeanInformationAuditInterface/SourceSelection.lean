import Lean

namespace LeanInformationAudit

/-- Paths address raw ConstantInfo.type, not pretty-printed text or normalized terms.
Steps are fn/arg, domain/body, type/value/body, or projection/metadata body. -/
structure SourceReadoutSelection where
  path : Array String
  stateBinder : Nat
  deriving BEq, Inhabited, Repr

/-- Increasing source telescope ordinals with dependency-closed domains.
Each readout selects an actual observation in its original lexical scope. -/
structure SourceSelection where
  owner : Lean.Name
  coordinates : Array Nat
  readouts : Array SourceReadoutSelection
  deriving BEq, Inhabited, Repr

structure SourceBinder where
  name : Lean.Name
  info : Lean.BinderInfo
  domain : Lean.Expr
  value : Option Lean.Expr := none
  isLambda : Bool := false
  nondep : Bool := false
  deriving BEq, Inhabited

end LeanInformationAudit
