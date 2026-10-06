import Lean.Expr
import Lean.Data.Options
import LeanInformationAudit.SourceSelection

namespace LeanInformationAudit
open Lean

abbrev CatalogId := Name

/-- Compiled input is retained for authoritative reassessment, never executed. -/
structure EscapeRecordInput where
  sourceSelection : Option SourceSelection := none
  finiteBridge : Option Name := none
  fromObject : Option Expr := none
  continuation : Option Expr := none
  openContinuation : Bool := false
  exclusion : Option Name := none
  finiteLift : Option Name := none
  roleEnumeration : Option Name := none
  anchorEnumeration : Option Name := none
  deriving Inhabited, BEq

inductive CatalogKind where
  | canonicalMaximal
  | analysisView
  deriving BEq, Inhabited, Repr

/-- Occurrence-bound inputs to the executable predicates in RegistrationReifier.
No stored boolean asserts certification; consumers revalidate these inputs. -/
structure AutoDerivedSemanticCertificate where
  occurrence : Array Name
  catalogKind : CatalogKind
  localRegistrationNames : Bool
  statementIdentity : String
  levelParams : List Name
  statement : Expr
  descriptor : Expr
  arena : Expr
  nondegenerate : Name
  outputEvidence : Expr

/-- Constructor states decoded from indexed Reg obligations. This is transient
consumer data; it is never an importable assessment or report receipt. -/
inductive CompiledObligationState where
  | evidence | unknown | absent | unsupported
  deriving Inhabited, BEq

structure CompiledMathematics where
  correspondence : CompiledObligationState
  bundleNonempty : CompiledObligationState
  variation : CompiledObligationState
  sensitivity : CompiledObligationState
  partialReadouts : Option (Array Bool) := none
  partialAnchors : Option (Array Bool) := none
  deriving Inhabited, BEq

structure InformationRegistryEntry where
  sourceBound : Bool := false
  theoremName : Name
  unitName : Name
  /-- The `PrimitiveLawArena` presentation. -/
  arenaName : Name
  /-- The declaration holding the native realization or the legacy bridge. -/
  realizationName : Name
  variationWitness : Name := .anonymous
  sensitivityWitness : Name := .anonymous
  catalogId : CatalogId := .anonymous
  catalogKind : CatalogKind := .canonicalMaximal
  registrationModuleName : Name := .anonymous
  objectArenaName : Name := .anonymous
  /-- Resolved declaration owner; arenaName/objectArenaName retain the source spelling. -/
  resolvedArenaName : Name := .anonymous
  /-- Stable identity of the elaborated theorem statement captured at registration. -/
  statementIdentity : String := ""
  /-- False exactly for registrations using occurrence-aware syntax. -/
  localRegistrationNames : Bool := true
  derivedCertificate : Option AutoDerivedSemanticCertificate := none
  compiledMathematics : Option CompiledMathematics := none

end LeanInformationAudit
