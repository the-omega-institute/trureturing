import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
import Reg.Support.DependentFamily

/-! The completion cardinality is the observation used in the residual quota. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature.{v} : Signature where
  Params := Type v
  State Site := Finset Site
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual.{v} : Realization signature.{v} :=
  realize signature.{v} (fun _ _ chosen => chosen.card) Empty.elim

private def rejected.{v} : Realization signature.{v} :=
  realize signature.{v} (fun _ _ _ => 0) Empty.elim

private abbrev arena.{u,v} : Arena where
  signature := signature.{v}
  Law A := ∀ {Row : Type u} {Site : Type v} [DecidableEq Site]
    (rows : Finset Row) (neighbors : Row → Finset Site) (fixed : Finset Site)
    (cap : ℕ) (chosen : Finset Site),
    fixed ⊆ chosen →
    (∀ row ∈ rows, Odd (neighbors row ∩ fixed).card) →
    (∀ row ∈ rows, Even (neighbors row ∩ chosen).card) →
    (∀ site ∈ chosen \ fixed, (rows.filter fun row => site ∈ neighbors row).card ≤ cap) →
    rows.card ≤ cap * (A.readout () Site chosen - fixed.card)

private theorem rejected_law.{u,v} : ¬ arena.{u,v}.Law rejected.{v} := by
  intro h
  let chosen : Finset (ULift.{v} Bool) := {⟨false⟩, ⟨true⟩}
  let fixed : Finset (ULift.{v} Bool) := {⟨false⟩}
  let rows : Finset (ULift.{u} Unit) := {⟨()⟩}
  have hfixed : fixed ⊆ chosen := by decide
  have hodd : Odd (chosen ∩ fixed).card := ⟨0, by decide⟩
  have heven : Even (chosen ∩ chosen).card := ⟨1, by decide⟩
  have hcap : ∀ site ∈ chosen \ fixed, (rows.filter fun _ => site ∈ chosen).card ≤ 1 := by
    intro site _
    simpa [rows] using Finset.card_filter_le (s := rows) (p := fun _ => site ∈ chosen)
  have hbad := h rows (fun _ => chosen) fixed 1 chosen hfixed (fun _ _ => hodd)
    (fun _ _ => heven) hcap
  change rows.card ≤ 1 * (0 - fixed.card) at hbad
  simp [rows] at hbad

def sourceEvidence.{u,v} :
    Registration arena.{u,v} (type_of% (@card_rows_le_residual_quota.{u,v})) where
  actual := actual.{v}
  bridge := Iff.rfl
  variation := ⟨card_rows_le_residual_quota, rejected.{v}, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected.{v}, ?_, rfl, rejected_law.{u,v}⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨ULift.{v} Unit, ∅, {⟨()⟩}, ?_⟩
    change (∅ : Finset (ULift.{v} Unit)).card ≠ ({⟨()⟩} : Finset (ULift.{v} Unit)).card
    simp

def quotaRegistration.{u,v} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@card_rows_le_residual_quota.{u,v}) (Realization signature.{v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity.card_rows_le_residual_quota.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨sourceEvidence.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ chosen => chosen.card) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev completionSignature : Signature where
  Params := Fin 3
  State _ := Finset (Fin 256)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev completionArena : Arena where
  signature := completionSignature
  Law A := ∀ (case : Fin 3) (chosen : Finset (Fin 256)),
    archivedFixed case ⊆ chosen →
    chosen \ archivedFixed case ⊆ archivedFree case →
    (∀ row ∈ evenCenters, Even (transverseNeighbors row ∩ chosen).card) →
    (if case = 2 then 56 else 54) ≤ A.readout () case chosen

private def completionActual : Realization completionSignature :=
  realize completionSignature (fun _ _ chosen => chosen.card) Empty.elim

private def completionRejected : Realization completionSignature :=
  realize completionSignature (fun _ _ _ => 0) Empty.elim

private def caseTwoCompletion : Finset (Fin 256) :=
  archivedFixed 0 ∪ ([133, 134, 137, 138, 157, 158, 173, 174, 217, 218, 229, 230] :
    List (Fin 256)).toFinset

set_option maxRecDepth 6000 in
private theorem completionRejected_law : ¬ completionArena.Law completionRejected := by
  intro h
  have hfixed : archivedFixed 0 ⊆ caseTwoCompletion := Finset.subset_union_left
  have hfree : caseTwoCompletion \ archivedFixed 0 ⊆ archivedFree 0 := by decide
  have heven : ∀ row ∈ evenCenters, Even (transverseNeighbors row ∩ caseTwoCompletion).card := by
    decide
  have hbad := h 0 caseTwoCompletion hfixed hfree heven
  change (54 : ℕ) ≤ 0 at hbad
  omega

def completionEvidence :
    Registration completionArena (type_of% archived_completion_card_lower_bound) where
  actual := completionActual
  bridge := Iff.rfl
  variation := ⟨archived_completion_card_lower_bound, completionRejected, completionRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨completionRejected, ?_, rfl, completionRejected_law⟩
      intro other h
      exact (h (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨0, ∅, {0}, ?_⟩
    change (∅ : Finset (Fin 256)).card ≠ ({0} : Finset (Fin 256)).card
    simp

def completionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    archived_completion_card_lower_bound (Realization completionSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity.archived_completion_card_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity.completionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨completionArena⟩
  objectArena := .source ⟨completionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source completionArena ⟨completionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ chosen => chosen.card) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
