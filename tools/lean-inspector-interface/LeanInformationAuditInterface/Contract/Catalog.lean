import LeanInformationAuditInterface.Contract.Core

/- L0 原型 -/
namespace LeanInformationAudit.Contract
open Lean
universe u v

structure TypeRef where
  name : Name
  type : Type u

structure TemplateEnrollment {T : Sort u} (template : T) where
  name : Name
  version : Nat
  constructors : Array (TypeRef.{v})
  options : Options

/-- Expectations are independent of discovered registrations. -/
structure ExpectedOccurrence where
  statement : Prop
  proof : statement
  theoremName : Name
  objectArenaName : Name
  statementIdentity : Option String
  registrationModuleName : Name

structure RootCatalogData where
  rootId : Name
  expected : Array ExpectedOccurrence
  source : Array ExpectedOccurrence
  baseline : Array ExpectedOccurrence
  companionPrefix : Option Name

structure RootCatalog where
  data : RootCatalogData

structure ExpectedDeclaration where
  rootId : Name
  occurrence : ExpectedOccurrence

structure Seal where
  rootId : Name
  options : Options

end LeanInformationAudit.Contract
