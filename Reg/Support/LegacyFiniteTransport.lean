import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscapeCounting.Fused

namespace Reg.Support.LegacyFiniteTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit

/-- Three data values, with the standard sum instances and eliminator. -/
abbrev Three := Bool ⊕ Unit

def threeEquiv : Three ≃ Fin 3 where
  toFun
    | .inl false => 0
    | .inl true => 1
    | .inr () => 2
  invFun i := if i = 0 then .inl false else if i = 1 then .inl true else .inr ()
  left_inv := by intro x; rcases x with b | u; cases b <;> rfl; cases u; rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Constructor-level codes avoid overloaded numerals in executable operands. -/
def code : Three → Fin 3 := fun x => Sum.rec
  (fun b => Bool.rec (Fin.mk Nat.zero (by decide))
    (Fin.mk (Nat.succ Nat.zero) (by decide)) b)
  (fun _ => Fin.mk (Nat.succ (Nat.succ Nat.zero)) (by decide)) x

def selectThree {Y : Type} (a b c : Y) (i : Fin 3) : Y :=
  Bool.rec
    (Bool.rec c b (decide (i = Fin.mk (Nat.succ Nat.zero) (by decide))))
    a (decide (i = Fin.mk Nat.zero (by decide)))

/-- Generic ADMIT family with no interpretation of the supplied Boolean observations. -/
def admitSignature (X I : Type) [Fintype I] [DecidableEq I] : PrimitiveSignature X where
  Index := I
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def admitRealization {X I : Type} [Fintype I] [DecidableEq I]
    (r : I → X → Bool) : PrimitiveRealization (admitSignature X I) := ⟨r, Fin.elim0⟩

/-- A direct dependent eliminator keeps the CUT and ADMIT roles distinct. -/
def agendaSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun b => Bool.rec Y Bool b
  outputDecidableEq := fun b => Bool.rec
    (motive := fun b => DecidableEq (Bool.rec Y Bool b)) inferInstance inferInstance b
  axis := fun b => Bool.rec .cut .admit b
  readoutAxisNotAnchor := by intro b; cases b <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def agendaRealization {X Y : Type} [DecidableEq Y] (f : X → Y) (g : X → Bool) :
    PrimitiveRealization (agendaSignature X Y) :=
  ⟨fun b => Bool.rec (motive := fun b => X → (agendaSignature X Y).Output b) f g b, Fin.elim0⟩

theorem realization_ext {X : Type} {S : PrimitiveSignature X}
    {a b : PrimitiveRealization S} (hr : a.readout = b.readout)
    (ha : a.anchor = b.anchor) : a = b := by
  cases a; cases b; cases hr; cases ha; rfl

noncomputable def enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilyRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilyRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.LegacyFiniteTransport.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilyRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.binaryFamilyRealization, part := .value, path := [], levels := [] }], facts := [] } }

noncomputable def enrollment_2 : LeanInformationAudit.Contract.TemplateEnrollment.{2, 0} (@_root_.Reg.Support.LegacyFiniteTransport.admitRealization) := {
  name := `Reg.Support.LegacyFiniteTransport.admitRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.LegacyFiniteTransport.enrollment_2.bodyFact,
  coverage := { roots := [
    { owner := `Reg.Support.LegacyFiniteTransport, declaration := `Reg.Support.LegacyFiniteTransport.admitRealization, part := .type, path := [], levels := [] },
    { owner := `Reg.Support.LegacyFiniteTransport, declaration := `Reg.Support.LegacyFiniteTransport.admitRealization, part := .value, path := [], levels := [] }], facts := [] } }

noncomputable def enrollment_3 : LeanInformationAudit.Contract.TemplateEnrollment.{2, 0} (@_root_.Reg.Support.LegacyFiniteTransport.agendaRealization) := {
  name := `Reg.Support.LegacyFiniteTransport.agendaRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.LegacyFiniteTransport.enrollment_3.bodyFact,
  coverage := { roots := [
    { owner := `Reg.Support.LegacyFiniteTransport, declaration := `Reg.Support.LegacyFiniteTransport.agendaRealization, part := .type, path := [], levels := [] },
    { owner := `Reg.Support.LegacyFiniteTransport, declaration := `Reg.Support.LegacyFiniteTransport.agendaRealization, part := .value, path := [], levels := [] }], facts := [] } }


end Reg.Support.LegacyFiniteTransport

noncomputable def Reg.Support.LegacyFiniteTransport.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyFiniteTransport\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"RegistrationTemplates\",\"binaryFamilyRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.Support.LegacyFiniteTransport.enrollment_3.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyFiniteTransport\",\"enrollment_3\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"Reg\",\"Support\",\"LegacyFiniteTransport\",\"agendaRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.Support.LegacyFiniteTransport.enrollment_2.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"LegacyFiniteTransport\",\"enrollment_2\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"Reg\",\"Support\",\"LegacyFiniteTransport\",\"admitRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
