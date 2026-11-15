import D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence

open _root_.D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics
open _root_.D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe x u

/-- A source observation keeps the complete model and intervention parameters.
The observed state is the candidate completed output, not a Boolean surrogate. -/
structure Params where
  n : Nat
  X : Type x
  U : Type u
  model : StructuralModel n X U
  intervention : Finset (Fin n)
  assigned : Fin n → X
  noise : U
  start : Fin n → X

abbrev signature : Signature where
  Params := Params.{x, u}
  State p := Fin p.n → p.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{x, u} := realize signature
  (fun _ p result => EvaluationWitness p.model p.intervention p.assigned p.noise
    p.model.order p.start result) (fun e => nomatch e)

abbrev uniquenessArena : Arena where
  signature := signature.{x, u}
  Law obs := ∀ {n : Nat} {X : Type x} {U : Type u}
    (model : StructuralModel n X U) (_ : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → X) (noise : U)
    {state₁ state₂ first second : Fin n → X},
    obs.readout () ⟨n, X, U, model, intervention, assigned, noise, state₁⟩ first →
    obs.readout () ⟨n, X, U, model, intervention, assigned, noise, state₂⟩ second →
    first = second

abbrev correspondenceArena : Arena where
  signature := signature.{x, u}
  Law obs := ∀ {n : Nat} {X : Type x} {U : Type u}
    (model : StructuralModel n X U) (_ : TopologicalOrder model)
    (noise : U) (seed : Fin n → X),
    let realized := graphTableModel model.order model.order_nodup
      model.order_complete model.parents seed
    let tables := fun (v : Fin n) (pa : model.parents v → X) => model.equation v pa noise
    ∀ (intervention : Finset (Fin n)) (assigned : Fin n → X),
      ∃! canonical : Fin n → X,
        EvaluationWitness realized intervention assigned tables model.order seed canonical ∧
        ∀ (state result : Fin n → X),
          obs.readout () ⟨n, X, U, model, intervention, assigned, noise, state⟩ result →
          result = canonical

/-- This is the full original theorem telescope, including arbitrary universes. -/
def uniquenessBridge :
    (type_of% (@evaluation_witness_result_unique_from_arbitrary_start.{x, u})) ↔
      uniquenessArena.{x, u}.Law actual := Iff.rfl

def correspondenceBridge :
    (type_of% (@graph_table_shared_seed_trace_correspondence.{x, u})) ↔
      correspondenceArena.{x, u}.Law actual := Iff.rfl

def uniquenessPositive : uniquenessArena.{x, u}.Law actual :=
  uniquenessBridge.mp (@evaluation_witness_result_unique_from_arbitrary_start.{x, u})

def correspondencePositive : correspondenceArena.{x, u}.Law actual :=
  correspondenceBridge.mp (@graph_table_shared_seed_trace_correspondence.{x, u})

/-- The unresolved arguments are the exact typed audit obligations. These
constructors are partial evidence, not closed validated registrations. -/
def uniquenessFamily
    (negative : ∃ bad, ¬ uniquenessArena.{x, u}.Law bad)
    (sensitivity : Sensitivity uniquenessArena.{x, u} actual)
    (dependence : ObservationalDependence signature.{x, u} actual) :
    Registration uniquenessArena.{x, u}
      (type_of% (@evaluation_witness_result_unique_from_arbitrary_start.{x, u})) where
  actual := actual
  bridge := uniquenessBridge
  variation := ⟨uniquenessPositive, negative⟩
  sensitivity := sensitivity
  dependence := dependence

def correspondenceFamily
    (negative : ∃ bad, ¬ correspondenceArena.{x, u}.Law bad)
    (sensitivity : Sensitivity correspondenceArena.{x, u} actual)
    (dependence : ObservationalDependence signature.{x, u} actual) :
    Registration correspondenceArena.{x, u}
      (type_of% (@graph_table_shared_seed_trace_correspondence.{x, u})) where
  actual := actual
  bridge := correspondenceBridge
  variation := ⟨correspondencePositive, negative⟩
  sensitivity := sensitivity
  dependence := dependence

/-- Candidate raw occurrences of the two original witness premises. -/
def uniquenessSelection : Contract.SourceSelection where
  owner := `D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence
  definition := none
  coordinates := #[0, 1, 2, 3, 5, 6, 7, 8, 9]
  readouts := #[{
    path := (Array.replicate 12 "body").push "domain"
    stateBinder := 10
    functionOperand := false
    booleanPredicate := false
    stateOperand := some #["arg"] }, {
    path := (Array.replicate 13 "body").push "domain"
    stateBinder := 11
    functionOperand := false
    booleanPredicate := false
    stateOperand := some #["arg"] }]

/-- The original-model witness occurrence under the unique canonical result. -/
def correspondenceSelection : Contract.SourceSelection where
  owner := `D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence
  definition := none
  coordinates := #[0, 1, 2, 3, 5, 6, 9, 10, 12]
  readouts := #[{
    path := Array.replicate 11 "body" ++ #["arg", "body", "arg", "body", "body", "domain"]
    stateBinder := 13
    functionOperand := false
    booleanPredicate := false
    stateOperand := some #["arg"] }]

/-- Compiled source evidence with explicit, unfilled completion obligations.
This record is not a Contract registration and claims no judge validation. -/
structure PartialAudit (A : Arena) (statement : Prop) where
  actual : Realization A.signature
  bridge : statement ↔ A.Law actual
  positive : A.Law actual
  selection : Contract.SourceSelection
  continuation : Contract.Continuation Unit
  complete : (∃ bad, ¬ A.Law bad) → Sensitivity A actual →
    ObservationalDependence A.signature actual → Registration A statement

def uniquenessAttempt : PartialAudit uniquenessArena.{x, u}
    (type_of% (@evaluation_witness_result_unique_from_arbitrary_start.{x, u})) where
  actual := actual
  bridge := uniquenessBridge
  positive := uniquenessPositive
  selection := uniquenessSelection
  continuation := .unknown
  complete := uniquenessFamily

def correspondenceAttempt : PartialAudit correspondenceArena.{x, u}
    (type_of% (@graph_table_shared_seed_trace_correspondence.{x, u})) where
  actual := actual
  bridge := correspondenceBridge
  positive := correspondencePositive
  selection := correspondenceSelection
  continuation := .unknown
  complete := correspondenceFamily

#print axioms uniquenessAttempt
#print axioms correspondenceAttempt

end Reg.D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence
