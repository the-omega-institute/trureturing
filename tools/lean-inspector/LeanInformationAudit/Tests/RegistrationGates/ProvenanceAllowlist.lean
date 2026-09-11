import LeanInformationAudit.Tests.RegistrationGates.ProvenancePrefilter
import Mathlib.Data.Finset.Card

open Lean LeanInformationAudit

namespace D5.ProvenanceFixture

def statement : Prop := (137 : Nat) = 137
theorem truth : statement := rfl
def arithmetic (_ : Unit) (x : Nat) : Nat :=
  if @decide (x ≤ 10) (Nat.decLe x 10) then Nat.mod x 3 else x
def finsetData (_ : Unit) (x : Finset Nat) : Nat := x.card
def multisetData (_ : Unit) (x : Multiset Nat) : Nat := x.card
def ValidAgenda (x : Nat) : Prop := x < 3
@[instance_reducible] def validAgendaDecidable : DecidablePred ValidAgenda := fun x => Nat.decLt x 3
def arenaDecision (_ : Unit) (x : Nat) : Bool :=
  @decide (ValidAgenda x) (validAgendaDecidable x)

noncomputable def directClassical (_ : Unit) (x : Bool) : Bool :=
  if @decide (x = false) (Classical.propDecidable _) then x else true
opaque opaqueData : Bool := false
def opaqueRead (_ : Unit) (x : Bool) : Bool := if opaqueData then true else x
def implementation (_ : Unit) (x : Bool) : Bool := x
@[implemented_by implementation] def implementedRead (_ : Unit) (x : Bool) : Bool := x

theorem helper : True := True.intro
theorem registered : True := helper
def proofAlias (_ : Unit) (x : Bool) : Bool := let _ := helper; x
structure ProofBox where
  proof : True
  tag : Bool
def box : ProofBox := ⟨helper, false⟩
def fieldRead (_ : Unit) (x : Bool) : Bool := let _ := box.proof; x
noncomputable def letDecision (_ : Unit) (x : Bool) : Bool :=
  let p : Prop := statement
  if @decide p (Classical.propDecidable p) then x else true
structure Dispatcher where
  family : Prop → Type
  select : (p : Prop) → family p
noncomputable def dispatcher : Dispatcher := ⟨Decidable, Classical.propDecidable⟩
noncomputable def dependentDecision (_ : Unit) (x : Bool) : Bool :=
  if @decide statement (dispatcher.select statement) then x else true

def finBound (_ : Unit) (x : Bool) : Bool :=
  let _ : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
  x
def equalityInstances (_ : Unit) (x : Bool) : Bool :=
  let _ : DecidableEq Nat := inferInstance
  let _ : DecidableEq Bool := inferInstance
  let _ : DecidableEq (Fin 3) := inferInstance
  x
def listLemma (_ : Unit) (x : Bool) : Bool :=
  let _ := List.length_append (as := [0]) (bs := [1])
  x

end D5.ProvenanceFixture

-- Verdicts are independent literal predictions, evaluated through production.
run_cmd do
  for (label, readout, theoremName, expected) in #[
      ("CoreArithmetic", ``D5.ProvenanceFixture.arithmetic, ``D5.ProvenanceFixture.truth, "clean"),
      ("FinsetData", ``D5.ProvenanceFixture.finsetData, ``D5.ProvenanceFixture.truth, "clean"),
      ("MultisetData", ``D5.ProvenanceFixture.multisetData, ``D5.ProvenanceFixture.truth, "clean"),
      ("ArenaDecidableSameModule", ``D5.ProvenanceFixture.arenaDecision, ``D5.ProvenanceFixture.truth, "clean"),
      ("DirectClassicalD5", ``D5.ProvenanceFixture.directClassical, ``D5.ProvenanceFixture.truth, "unclassified_form"),
      ("OpaqueD5", ``D5.ProvenanceFixture.opaqueRead, ``D5.ProvenanceFixture.truth, "unclassified_form"),
      ("ImplementedD5", ``D5.ProvenanceFixture.implementedRead, ``D5.ProvenanceFixture.truth, "unclassified_form"),
      ("ProofAliasD5", ``D5.ProvenanceFixture.proofAlias, ``D5.ProvenanceFixture.registered, "forbidden_dependency"),
      ("StructureFieldD5", ``D5.ProvenanceFixture.fieldRead, ``D5.ProvenanceFixture.registered, "forbidden_dependency"),
      ("LetDecisionD5", ``D5.ProvenanceFixture.letDecision, ``D5.ProvenanceFixture.truth, "forbidden_dependency"),
      ("DependentProjectionD5", ``D5.ProvenanceFixture.dependentDecision, ``D5.ProvenanceFixture.truth, "forbidden_dependency"),
      ("FinBoundProof", ``D5.ProvenanceFixture.finBound, ``D5.ProvenanceFixture.truth, "clean"),
      ("DataEqualityInstances", ``D5.ProvenanceFixture.equalityInstances, ``D5.ProvenanceFixture.truth, "clean"),
      ("ListDataLemma", ``D5.ProvenanceFixture.listLemma, ``D5.ProvenanceFixture.registered, "clean")] do
    let actual ← Elab.Command.liftCoreM <|
      RegistrationGates.classifyReadoutCurrent theoremName (mkConst readout)
    let reason := if actual.closure.isNone then "incomplete_closure"
      else if actual.forbidden then "forbidden_dependency"
      else if actual.firstUnknown.isSome then "unclassified_form" else "clean"
    logInfo m!"FIXTURE_RESULT {label} {reason}"
    if reason == expected then logInfo m!"[PASS] {label}"
    else logError m!"[FAIL] {label}: expected {expected}, got {reason}: {actual.firstUnknown}"
