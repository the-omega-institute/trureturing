import Lean
import LeanInformationAuditInterface.SourceSelection

namespace LeanInformationAudit
open Lean

initialize registerTraceClass `InformationRegistration.check

abbrev CatalogId := Name

/-- Syntax input is retained for authoritative reassessment, never executed. -/
structure EscapeRecordInput where
  sourceSelection : Option SourceSelection := none
  finiteBridge : Option Name := none
  fromObject : Option Expr := none
  continuation : Option Expr := none
  openContinuation : Bool := false
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

structure InformationRegistryEntry where
  sourceBound : Bool := false
  theoremName : Name
  unitName : Name
  /-- The `PrimitiveLawArena` presentation. -/
  arenaName : Name
  /-- The declaration holding the native realization or the legacy witness. -/
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

end LeanInformationAudit
