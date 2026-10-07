import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAudit.Tests.DeclaredTemplates
open Lean
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- A homogeneous signature avoids proof-to-data Eq.rec transports. The existing
-- heterogeneous separation signature is an explicit unsupported control below.
def symbolicSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def symbolicPointwise {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (symbolicSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0

def boolCases {X : Type} (f g : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Bool.rec (f x) (g x) (f x))

def propositionSlot (P : Prop) {X : Type} (f : X → Bool) :
    PrimitiveRealization (cutSignature X Bool) := cutRealization f

def wrongInterface (x : Bool) : Bool := x

def closedDecision {X : Type} : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => decide True)

def recursiveBody {X : Type} (f : X → Bool) (n : Nat) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun x => Nat.rec (f x) (fun _ b => b) n)


def symbolicPointwiseEnrollment : LeanInformationAudit.Contract.TemplateEnrollment.{_, 0} (@symbolicPointwise) := {
  name := `LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwise, version := 1, constructors := #[], options := #[],
  bodyFact := `LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwiseBodyFact,
  coverage := { roots := [{ owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwise, part := .type, path := [] },
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwise, part := .value, path := [] }], facts := [] } }

def symbolicPointwiseBodyFact : LeanInformationAudit.Contract.NodeFact :=
  .equal (@symbolicPointwise)
    (fun {X Y : Type} [dY : DecidableEq Y] (f g : X → Y) => ⟨fun b x => Bool.rec (f x) (g x) b, Fin.elim0⟩)
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwiseEnrollment, part := .type, path := [.argument] }
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.symbolicPointwise, part := .value, path := [] }
    rfl

def boolCasesEnrollment : LeanInformationAudit.Contract.TemplateEnrollment.{_, 0} (@boolCases) := {
  name := `LeanInformationAudit.Tests.DeclaredTemplates.boolCases, version := 1, constructors := #[], options := #[],
  bodyFact := `LeanInformationAudit.Tests.DeclaredTemplates.boolCasesBodyFact,
  coverage := { roots := [{ owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.boolCases, part := .type, path := [] },
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.boolCases, part := .value, path := [] }], facts := [] } }

def boolCasesBodyFact : LeanInformationAudit.Contract.NodeFact :=
  .equal (@boolCases)
    (fun {X : Type} (f g : X → Bool) => cutRealization (fun x => Bool.rec (f x) (g x) (f x)))
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.boolCasesEnrollment, part := .type, path := [.argument] }
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.boolCases, part := .value, path := [] }
    rfl

def propositionSlotEnrollment : LeanInformationAudit.Contract.TemplateEnrollment.{_, 0} (@propositionSlot) := {
  name := `LeanInformationAudit.Tests.DeclaredTemplates.propositionSlot, version := 1, constructors := #[], options := #[],
  bodyFact := `LeanInformationAudit.Tests.DeclaredTemplates.propositionSlotBodyFact,
  coverage := { roots := [{ owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.propositionSlot, part := .type, path := [] },
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.propositionSlot, part := .value, path := [] }], facts := [] } }

def propositionSlotBodyFact : LeanInformationAudit.Contract.NodeFact :=
  .equal (@propositionSlot)
    (fun (P : Prop) {X : Type} (f : X → Bool) => cutRealization f)
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.propositionSlotEnrollment, part := .type, path := [.argument] }
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.propositionSlot, part := .value, path := [] }
    rfl

def wrongInterfaceEnrollment : LeanInformationAudit.Contract.TemplateEnrollment.{_, 0} (@wrongInterface) := {
  name := `LeanInformationAudit.Tests.DeclaredTemplates.wrongInterface, version := 1, constructors := #[], options := #[],
  bodyFact := `LeanInformationAudit.Tests.DeclaredTemplates.wrongInterfaceBodyFact,
  coverage := { roots := [{ owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.wrongInterface, part := .type, path := [] },
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.wrongInterface, part := .value, path := [] }], facts := [] } }

def wrongInterfaceBodyFact : LeanInformationAudit.Contract.NodeFact :=
  .equal (@wrongInterface)
    (fun (x : Bool) => x)
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.wrongInterfaceEnrollment, part := .type, path := [.argument] }
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.wrongInterface, part := .value, path := [] }
    rfl

def closedDecisionEnrollment : LeanInformationAudit.Contract.TemplateEnrollment.{_, 0} (@closedDecision) := {
  name := `LeanInformationAudit.Tests.DeclaredTemplates.closedDecision, version := 1, constructors := #[], options := #[],
  bodyFact := `LeanInformationAudit.Tests.DeclaredTemplates.closedDecisionBodyFact,
  coverage := { roots := [{ owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.closedDecision, part := .type, path := [] },
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.closedDecision, part := .value, path := [] }], facts := [] } }

def closedDecisionBodyFact : LeanInformationAudit.Contract.NodeFact :=
  .equal (@closedDecision)
    (fun {X : Type} => cutRealization (fun _ => decide True))
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.closedDecisionEnrollment, part := .type, path := [.argument] }
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.closedDecision, part := .value, path := [] }
    rfl

def recursiveBodyEnrollment : LeanInformationAudit.Contract.TemplateEnrollment.{_, 0} (@recursiveBody) := {
  name := `LeanInformationAudit.Tests.DeclaredTemplates.recursiveBody, version := 1, constructors := #[], options := #[],
  bodyFact := `LeanInformationAudit.Tests.DeclaredTemplates.recursiveBodyBodyFact,
  coverage := { roots := [{ owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.recursiveBody, part := .type, path := [] },
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.recursiveBody, part := .value, path := [] }], facts := [] } }

def recursiveBodyBodyFact : LeanInformationAudit.Contract.NodeFact :=
  .equal (@recursiveBody)
    (fun {X : Type} (f : X → Bool) (n : Nat) => cutRealization (fun x => Nat.rec (f x) (fun _ b => b) n))
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.recursiveBodyEnrollment, part := .type, path := [.argument] }
    { owner := `LeanInformationAuditRegTests.Fixtures.TemplateBodies, declaration := `LeanInformationAudit.Tests.DeclaredTemplates.recursiveBody, part := .value, path := [] }
    rfl

end LeanInformationAudit.Tests.DeclaredTemplates
