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

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSingletonParity
