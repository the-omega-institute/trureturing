import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows

/-! The cut readout observes a signing and the first exact row observes a switch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

private abbrev cutSignature.{u} : Signature where
  Params := Σ V : Type u, Σ _ : V → Finset V, Finset V
  State p := Signing p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

private def cutActual.{u} : Realization cutSignature.{u} :=
  realize cutSignature (fun _ p s => cutParity p.2.1 s p.2.2) Empty.elim

private def cutRejected.{u} : Realization cutSignature.{u} :=
  realize cutSignature (fun _ _ _ => 1) Empty.elim

private abbrev cutArena.{u} : Arena where
  signature := cutSignature.{u}
  Law R := ∀ {V : Type u} [Finite V] [DecidableEq V]
    (neighbors : V → Finset V), (∀ u v, v ∈ neighbors u ↔ u ∈ neighbors v) →
    ∀ (cut : Finset V),
    (∀ u, laplacian neighbors (fun v => if v ∈ cut then 1 else 0) u = 0) →
    ∀ (s : Signing V) (z : V → ZMod 2) (target : V → ℤ),
    (∀ u ∈ cut, rowSum neighbors s z u = target u) →
    (∑ u ∈ cut, (((((neighbors u).card : ℤ) - target u) / 2 : ℤ) : ZMod 2)) =
      R.readout () ⟨V, neighbors, cut⟩ s

private theorem cutRejected_law.{u} : ¬ cutArena.{u}.Law cutRejected.{u} := by
  intro h
  let neighbors : ULift.{u} Bool → Finset (ULift.{u} Bool) := fun _ => ∅
  have bad := h neighbors (by simp [neighbors]) ∅ (by simp [laplacian, neighbors])
    ⟨fun _ _ => 0⟩ (fun _ => 0) (fun _ => 0) (by simp)
  simp [cutRejected, realize] at bad

def cutEvidence.{u} : Registration cutArena.{u} (type_of% (@signed_rows_even_cut.{u})) where
  actual := cutActual
  bridge := Iff.rfl
  variation := ⟨signed_rows_even_cut, cutRejected, cutRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨cutRejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, cutRejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} Bool, fun u => {⟨!u.down⟩}, {⟨false⟩}⟩,
      ⟨fun _ _ => 0⟩, ⟨fun _ _ => 1⟩, ?_⟩
    simp [cutActual, realize, cutParity]

def cutRegistration.{u} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_rows_even_cut.{u}) (Realization cutSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows.signed_rows_even_cut.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows.cutEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cutArena.{u}⟩
  objectArena := .source ⟨cutArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cutArena.{u} ⟨cutEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cutSignature.{u} (fun _ p s => cutParity p.2.1 s p.2.2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev pairSignature : Signature where
  Params := Fin 6
  State _ := Fin 6 → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def pairActual : Realization pairSignature :=
  realize pairSignature (fun _ u z => rowSum sixNeighbors sixSigning z u) Empty.elim

private def pairRejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => 0) Empty.elim

private abbrev pairArena : Arena where
  signature := pairSignature
  Law R :=
    (∀ u v : Fin 6, u ≠ v → ∃ z : Fin 6 → ZMod 2,
      R.readout () u z = sixTarget u ∧ rowSum sixNeighbors sixSigning z v = sixTarget v) ∧
    ¬ ∃ z : Fin 6 → ZMod 2, ∀ u ∈ sixCut,
      rowSum sixNeighbors sixSigning z u = sixTarget u

private theorem pairRejected_law : ¬ pairArena.Law pairRejected := by
  intro h
  obtain ⟨_, bad, _⟩ := h.1 0 1 (by decide)
  exact (by decide : (0 : ℤ) ≠ sixTarget 0) bad

def pairEvidence : Registration pairArena (type_of% six_row_separation) where
  actual := pairActual
  bridge := Iff.rfl
  variation := ⟨six_row_separation, pairRejected, pairRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨pairRejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, pairRejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    intro role
    cases role
    exact ⟨4, (fun _ => 0), (fun u => if u = 0 then 1 else 0), by decide⟩

def pairRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    six_row_separation (Realization pairSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows.six_row_separation.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows.pairEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena⟩
  objectArena := .source ⟨pairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairArena ⟨pairEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature
    (fun _ u z => rowSum sixNeighbors sixSigning z u) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows
