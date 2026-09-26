import Lean

namespace LeanInformationAudit

/-- Paths address the raw theorem type, or its explicitly selected named claim body.
No pretty-printing or normalization selects occurrences.
Steps are fn/arg, domain/body, type/value/body, or projection/metadata body. -/
structure SourceReadoutSelection where
  path : Array String
  stateBinder : Nat
  deriving BEq, Inhabited, Repr

/-- A bounded entry into a named source definition.  The theorem remains the
raw binding root. Only its exact nullary proposition constant may be entered,
once, at the root or the sole argument of raw `Not`, in the same source module.
Definition aliases and proof bodies are not entered. -/
structure SourceDefinitionSelection where
  owner : Lean.Name
  name : Lean.Name
  /-- Raw theorem occurrence: `#[]` or `#["arg"]` under literal `Not`. -/
  path : Array String := #[]
  deriving BEq, Inhabited, Repr

/-- Increasing lexical binder ordinals, shared by raw ancestor path across readouts.
Domains are dependency closed after deterministic expansion of source local lets.
Each readout selects an actual observation in its original lexical scope. -/
structure SourceSelection where
  owner : Lean.Name
  definition : Option SourceDefinitionSelection := none
  coordinates : Array Nat
  readouts : Array SourceReadoutSelection
  deriving BEq, Inhabited, Repr

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
