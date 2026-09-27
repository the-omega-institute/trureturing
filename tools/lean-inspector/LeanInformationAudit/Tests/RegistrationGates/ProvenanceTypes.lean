import LeanInformationAudit.Tests.RegistrationGates.ProvenanceRegressions

open Lean LeanInformationAudit
namespace RegistrationProvenance

-- V1 registers True deliberately; the stored True.intro is forbidden evidence.
theorem fieldTruth : True := independentProof
structure ProofBox where
  evidence : True
  tag : Bool
def box : ProofBox := ⟨True.intro, false⟩
def fieldRead (_ : Unit) (x : Bool) : Bool := let _ := box.evidence; x
check_provenance "StructureField" using fieldRead expects "forbidden_dependency" for fieldTruth

noncomputable def letDecision (_ : Unit) (x : Bool) : Bool :=
  let p : Prop := specificStatement
  if @decide p (Classical.propDecidable p) then x else true
check_provenance "LetBoundDecision" using letDecision expects "unclassified_form" for specificTruth

structure Dispatcher where
  family : Prop → Type
  choose : (p : Prop) → family p
noncomputable def dispatcher : Dispatcher := ⟨Decidable, Classical.propDecidable⟩
noncomputable def projectedDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide specificStatement (dispatcher.choose specificStatement) then x else true
check_provenance "DependentProjectionDecision" using projectedDecision expects "unclassified_form" for specificTruth

def owner (s : String) : Name := .str (.str .anonymous "RegistrationProvenance") s
def ownerCertificate : Certificate (owner "specificTruth") := ⟨true⟩
def ownerRead (_ : Unit) (x : Bool) : Bool := cond ownerCertificate.bit x true
-- A user record with Bool data reaches no judge API, generated record, or theorem.
check_provenance "ComputedOwnerCertificate" using ownerRead expects "clean" for specificTruth
run_cmd Elab.Command.liftTermElabM do
  addDecl <| .defnDecl {
    name := `RegistrationProvenance.descendantName, levelParams := [], type := mkConst ``Name
    value := mkApp2 (mkConst ``Name.str) (toExpr ``specificTruth) (mkStrLit "other")
    hints := .abbrev, safety := .safe }
def descendantRead (_ : Unit) (x : Bool) : Bool := let _ := descendantName; x
check_provenance "DescendantNameControl" using descendantRead expects "clean" for specificTruth

-- Here S really is True: True.intro must be rejected, even inside a structure.
structure TrueBox where
  evidence : True
  tag : Bool
def trueBox : TrueBox := ⟨True.intro, false⟩
def trueBoxRead (_ : Unit) (x : Bool) : Bool := let _ := trueBox.evidence; x
check_provenance "TrueStatementInhabitant" using trueBoxRead expects "forbidden_dependency" for truth

def theoremProposition : Prop := specificTruth = specificTruth
theorem dependentProof : theoremProposition := rfl
def dependentProofRead (_ : Unit) (x : Bool) : Bool := let _ := dependentProof; x
check_provenance "TheoremDependentProposition" using dependentProofRead expects "forbidden_dependency" for specificTruth
def theoremRelay : Bool := let _ := specificTruth; true
def relayRead (_ : Unit) (x : Bool) : Bool := if theoremRelay then x else false
check_provenance "TheoremDependencyClosure" using relayRead expects "forbidden_dependency" for specificTruth

set_option linter.style.nameCheck false
-- Synthetic instances of the generator's reserved declaration-name grammar.
def generated.__lowers_escape : Bool := true
def generated.__escape_enriched : Bool := true
def generated.__trivial_in_catalog : Bool := true
def generated.__catalog_suite : Bool := true
def generated.__system_catalog_irredundant : Bool := true
def generated.«root/arena/catalog».__lowers_escape : Bool := true
def generatedRead (_ : Unit) (x : Bool) : Bool :=
  let _ := generated.__lowers_escape
  let _ := generated.__escape_enriched
  let _ := generated.__trivial_in_catalog
  let _ := generated.__catalog_suite
  let _ := generated.__system_catalog_irredundant
  let _ := generated.«root/arena/catalog».__lowers_escape
  x
check_provenance "JudgeGeneratedCompanions" using generatedRead expects "forbidden_dependency" for specificTruth
def sealPayloadRead (_ : Unit) (x : Bool) : Bool := let _ := SealTheoremRecord.mk; x
check_provenance "JudgeSealPayload" using sealPayloadRead expects "forbidden_dependency" for specificTruth

def apiOnlyRead (_ : Unit) (x : Bool) : Bool := let _ := InformationRegistryEntry.statementIdentity; x
check_provenance "JudgeIdentityAPI" using apiOnlyRead expects "forbidden_dependency" for specificTruth
def closedStatementRead (_ : Unit) (x : Bool) : Bool := let _ : specificStatement := Eq.refl 137; x
check_provenance "ClosedStatementInhabitant" using closedStatementRead expects "forbidden_dependency" for specificTruth

-- F1: the binder disappears only after reducing the proposition argument.
def openAliasFamily (_ : Bool) : Prop := specificStatement
noncomputable def openAliasDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide (openAliasFamily x) (Classical.propDecidable _) then x else false
check_provenance "OpenAliasDecision" using openAliasDecision expects "unclassified_form" for specificTruth
noncomputable def openAliasBinderControl := unrelatedDecisionRead
check_provenance "OpenAliasBinderControl" using openAliasBinderControl expects "unclassified_form" for specificTruth

def structuralAliasFamily (_ : Nat) : Prop := specificStatement
noncomputable def structuralAliasDecision (_ : Unit) (x : Nat) : Nat :=
  if @decide (structuralAliasFamily x) (Classical.propDecidable _) then x else 0
noncomputable def structuralBinderDecision (_ : Unit) (x : Nat) : Nat :=
  if @decide (x = 138) (Classical.propDecidable _) then x else 0

-- Structural witness validation no longer audits an undeclared realization.
-- Assess exact applications against an existing declared structural occurrence.
-- These noncomputable negative providers are inspected, never executed.
noncomputable def structuralAliasRealization := structuralTemplate (fun i x => structuralAliasDecision i x)
noncomputable def structuralBinderRealization := structuralTemplate (fun i x => structuralBinderDecision i x)
def structuralAliasClean := structuralTemplate (fun _ x => x)

run_cmd Elab.Command.liftTermElabM do
  let some source := (TemplateBinding.records (← getEnv)).find?
      (·.occurrence.key.theoremName == ``cleanStructural)
    | throwError "setup: missing declared structural occurrence"
  for (name, label, expected) in [
      (``structuralAliasRealization, "OpenAliasDecisionStructural", some "reason=unclassified_form rule=E2.closed_proposition"),
      (``structuralBinderRealization, "OpenAliasBinderControlStructural", some "reason=forbidden_dependency rule=E6.closed_identity"),
      (``structuralAliasClean, "OpenAliasStructuralClean", none)] do
    let .defnInfo info ← getConstInfo name
      | throwError "setup: missing structural provider {name}"
    let claim : TemplateBindingClaim := {
      key := source.occurrence.key, arena := source.occurrence.arena,
      descriptor := some info.value, owner := (← getEnv).header.mainModule }
    let row ← TemplateBinding.assess { source.occurrence with realizationName := name }
      (some claim)
    let ok := match row.result, expected with
      | .declaredUnresolved diagnostic, some fragment => diagnostic.contains fragment
      | .declaredValidated _, none => true
      | _, _ => false
    let actual := match row.result with
      | .declaredUnresolved diagnostic => diagnostic
      | .declaredValidated _ => "validated"
      | .undeclared => "undeclared"
    if ok then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: {actual}"

end RegistrationProvenance
