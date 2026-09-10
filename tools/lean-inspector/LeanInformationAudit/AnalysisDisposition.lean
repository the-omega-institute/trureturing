import LeanInformationAudit.NameWire
import Lean
import Mathlib.Data.Finset.Card

namespace LeanInformationAudit

open Lean

-- Canonical declarations copied verbatim from the disposition section of the spec.
inductive UnreachableReason
  | noCanonicalObjectCarrier
  | noFinitePrimitiveBundle
  | noFaithfulPrimitiveRealization

structure StatementKey where
  theoremName : Name
  statementId : String
  deriving DecidableEq, Repr

structure FiniteOccurrenceDisposition (key : StatementKey) where
  canonicalArena : Name
  registration : Name
  realization : Name
  nondegeneracyCertificate : Name
  stateEnumerationCertificate : Name

structure StructuralOccurrenceDisposition (key : StatementKey) where
  canonicalArena : Name
  registration : Name
  realization : Name
  strictnessCertificate : Name
  witnessCertificate : Name

inductive TruncationCertification
  | reportOnly
  | transferred (transferTheorem : Name)

structure BoundedFiniteTruncationDisposition (key : StatementKey) where
  truncationFamily : Name
  bound : Nat
  comparisonStatement : Name
  certification : TruncationCertification

structure UnreachableDisposition (key : StatementKey) where
  reason : UnreachableReason
  evidence : Name

inductive AnalysisDisposition (key : StatementKey) where
  | finiteOccurrence (value : FiniteOccurrenceDisposition key)
  | structuralOccurrence (value : StructuralOccurrenceDisposition key)
  | boundedFiniteTruncation
      (value : BoundedFiniteTruncationDisposition key)
  | unreachable (value : UnreachableDisposition key)

/-- Every module in the root's transitive import closure, including the root. -/
structure ImportClosureScope where
  modules : Array Name
  completed : Bool
  deriving DecidableEq, Repr

/-- A completed query record for census accounting. Admission requires both
`queryCompleted` and `importScope.completed`, with the root, owning module,
full import closure, and candidate provenance checked against the environment.
Query completion does not certify a disposition: an observed row never counts
as classified, never contributes to certified counts or AC-023, and is never a
closed reason. Registry absence alone is only an observation. -/
structure AnalysisObservation (key : StatementKey) where
  owningModule : Name
  root : Name
  importScope : ImportClosureScope
  queryCompleted : Bool
  candidates : Array Name
  note : String -- Presentation only; never consumed as evidence.
  deriving DecidableEq, Repr

/-- A certified disposition or a completed observation for one frozen theorem key.
The observed case never counts as classified, contributes nothing to certified
counts or AC-023, and is never a closed reason.

A census is accounted when every frozen theorem key has exactly one assessment.
`DispositionInventory.ExactlyCovers` ranges over all keys, including observed
ones; the artifact's `accounted` count includes both cases. For a validated
census, `certified_complete` holds iff `observed = 0`. -/
inductive CensusAssessment (key : StatementKey) where
  | certified (value : AnalysisDisposition key)
  | observed (value : AnalysisObservation key)

structure DispositionInventory where
  headSha : String
  entries : Array (Sigma fun key : StatementKey => CensusAssessment key)

def DispositionInventory.keys
    (inventory : DispositionInventory) : List StatementKey :=
  inventory.entries.toList.map fun entry => entry.1

def DispositionInventory.certifiedKeys
    (inventory : DispositionInventory) : List StatementKey :=
  inventory.entries.toList.filterMap fun entry =>
    match entry.2 with
    | .certified _ => some entry.1
    | .observed _ => none

def DispositionInventory.ExactlyCovers
    (inventory : DispositionInventory)
    (frozenHeadSha : String)
    (frozenTheorems : Finset StatementKey) : Prop :=
  inventory.headSha = frozenHeadSha ∧
  inventory.keys.Nodup ∧
  (inventory.keys.map fun key => key.statementId).Nodup ∧
  inventory.keys.toFinset = frozenTheorems

deriving instance DecidableEq, Repr for UnreachableReason
deriving instance DecidableEq, Repr for FiniteOccurrenceDisposition
deriving instance DecidableEq, Repr for StructuralOccurrenceDisposition
deriving instance DecidableEq, Repr for TruncationCertification
deriving instance DecidableEq, Repr for BoundedFiniteTruncationDisposition
deriving instance DecidableEq, Repr for UnreachableDisposition
deriving instance DecidableEq, Repr for AnalysisDisposition
deriving instance DecidableEq, Repr for CensusAssessment
deriving instance DecidableEq, Repr for DispositionInventory

deriving instance Inhabited for StatementKey
deriving instance Inhabited for FiniteOccurrenceDisposition
deriving instance Inhabited for ImportClosureScope
deriving instance Inhabited for AnalysisObservation
deriving instance Inhabited for AnalysisDisposition
deriving instance Inhabited for CensusAssessment

instance (inventory : DispositionInventory) (head : String) (keys : Finset StatementKey) :
    Decidable (inventory.ExactlyCovers head keys) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def StatementKey.lt (left right : StatementKey) : Bool :=
  left.theoremName.toString < right.theoremName.toString ||
    (left.theoremName.toString == right.theoremName.toString && left.statementId < right.statementId)



def UnreachableReason.jsonName : UnreachableReason → String
  | .noCanonicalObjectCarrier => "no_canonical_object_carrier"
  | .noFinitePrimitiveBundle => "no_finite_primitive_bundle"
  | .noFaithfulPrimitiveRealization => "no_faithful_primitive_realization"

instance : ToJson UnreachableReason := ⟨fun reason => toJson reason.jsonName⟩

instance : ToJson StatementKey := ⟨fun key => Json.mkObj [
  ("theorem_name", nameJson key.theoremName),
  ("statement_id", toJson key.statementId)]⟩

instance {key : StatementKey} : ToJson (FiniteOccurrenceDisposition key) :=
  ⟨fun value => Json.mkObj [
    ("canonical_arena", nameJson value.canonicalArena),
    ("registration", nameJson value.registration),
    ("realization", nameJson value.realization),
    ("nondegeneracy_certificate", nameJson value.nondegeneracyCertificate),
    ("state_enumeration_certificate", nameJson value.stateEnumerationCertificate)]⟩

instance {key : StatementKey} : ToJson (StructuralOccurrenceDisposition key) :=
  ⟨fun value => Json.mkObj [
    ("canonical_arena", nameJson value.canonicalArena),
    ("registration", nameJson value.registration),
    ("realization", nameJson value.realization),
    ("strictness_certificate", nameJson value.strictnessCertificate),
    ("witness_certificate", nameJson value.witnessCertificate)]⟩

instance : ToJson TruncationCertification := ⟨fun
  | .reportOnly => Json.mkObj [("kind", toJson "report_only")]
  | .transferred theoremName => Json.mkObj [
      ("kind", toJson "transferred"), ("transfer_theorem", nameJson theoremName)]⟩

instance {key : StatementKey} : ToJson (BoundedFiniteTruncationDisposition key) :=
  ⟨fun value => Json.mkObj [
    ("truncation_family", nameJson value.truncationFamily),
    ("bound", toJson value.bound),
    ("comparison_statement", nameJson value.comparisonStatement),
    ("certification", toJson value.certification)]⟩

instance {key : StatementKey} : ToJson (UnreachableDisposition key) :=
  ⟨fun value => Json.mkObj [
    ("reason", toJson value.reason), ("evidence", nameJson value.evidence)]⟩

instance : ToJson ImportClosureScope := ⟨fun scope => Json.mkObj [
  ("modules", Json.arr (scope.modules.map nameJson)),
  ("completed", toJson scope.completed)]⟩

instance {key : StatementKey} : ToJson (AnalysisObservation key) :=
  ⟨fun value => Json.mkObj [
    ("owning_module", nameJson value.owningModule),
    ("root", nameJson value.root),
    ("import_scope", toJson value.importScope),
    ("query_completed", toJson value.queryCompleted),
    ("candidates", Json.arr (value.candidates.map nameJson)),
    ("note", toJson value.note)]⟩

def AnalysisDisposition.className {key : StatementKey} : AnalysisDisposition key → String
  | .finiteOccurrence _ => "finite_occurrence"
  | .structuralOccurrence _ => "structural_occurrence"
  | .boundedFiniteTruncation _ => "bounded_finite_truncation"
  | .unreachable _ => "unreachable"

def AnalysisDisposition.payloadJson {key : StatementKey} : AnalysisDisposition key → Json
  | .finiteOccurrence value => toJson value
  | .structuralOccurrence value => toJson value
  | .boundedFiniteTruncation value => toJson value
  | .unreachable value => toJson value

def CensusAssessment.className {key : StatementKey} : CensusAssessment key → String
  | .certified value => value.className
  | .observed _ => "observed"

def CensusAssessment.payloadJson {key : StatementKey} : CensusAssessment key → Json
  | .certified value => value.payloadJson
  | .observed value => toJson value

instance {key : StatementKey} : ToJson (AnalysisDisposition key) :=
  ⟨fun disposition => Json.mkObj [
    ("class", toJson disposition.className), ("payload", disposition.payloadJson)]⟩

def dispositionRowJson (entry : Sigma fun key : StatementKey => CensusAssessment key) : Json :=
  Json.mkObj [
    ("theorem_name", nameJson entry.1.theoremName),
    ("statement_id", toJson entry.1.statementId),
    ("class", toJson entry.2.className),
    ("payload", entry.2.payloadJson)]

def DispositionInventory.sortedEntries (inventory : DispositionInventory) :=
  inventory.entries.qsort fun left right => left.1.lt right.1

instance : ToJson DispositionInventory := ⟨fun inventory => Json.mkObj [
  ("head_sha", toJson inventory.headSha),
  ("entries", Json.arr <| inventory.sortedEntries.map dispositionRowJson)]⟩

namespace DispositionCensus

def identityError (name : Name) (component expected actual : String) : String :=
  s!"IE-C036 DispositionIdentityMismatch theorem={name} component={component} \
expected={expected} actual={actual}"

/-- realization.provenance.syntax means the theorem lacks a matching
structural_theorem introducing command in its owning module's source. It is a
source provenance contract, excluding source rewrites and changed search paths. -/
def classError (name : Name) (className invalid : String) : String :=
  s!"IE-C037 DispositionClassMismatch theorem={name} class={className} invalid={invalid}"

def censusError (head component expected actual : String) : String :=
  s!"IE-C044 DispositionCensusMismatch head={head} component={component} \
expected={expected} actual={actual}"

/-- An unfinished query cannot be admitted even as an observation. -/
def checkObservationStatus (head : String) {key : StatementKey}
    (value : AnalysisObservation key) : Except String Unit := do
  unless value.queryCompleted do
    throw <| censusError head "query_completed" "true" "false"
  unless value.importScope.completed do
    throw <| censusError head "import_scope" "completed" "false"

end DispositionCensus

end LeanInformationAudit
