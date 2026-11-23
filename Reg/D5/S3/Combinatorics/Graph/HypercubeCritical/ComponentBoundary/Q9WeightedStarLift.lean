import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum (Q flip)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang (parity)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression (empty)
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift
  (baseParity parity_append_empty)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Q 6) (fun _ => Bool)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : Q 6, parity (Fin.append x empty) = !(R.readout () () x)

private def actual : Realization signature :=
  realize signature (fun _ _ x => baseParity x) Empty.elim

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) Empty.elim

private def origin : Q 6 := fun _ => true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h origin
  change parity (Fin.append origin empty) = false at h'
  have h₀ : parity (Fin.append origin empty) = true := by decide
  rw [h₀] at h'
  contradiction

def sourceEvidence : Registration arena (type_of% @parity_append_empty) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parity_append_empty, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨(), origin, flip origin 0, by decide⟩

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parity_append_empty) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift.parity_append_empty.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => baseParity x) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift
