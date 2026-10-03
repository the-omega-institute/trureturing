import D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
open LeanInformationAudit
open Lean Elab Command
open Filter Set

noncomputable section
namespace Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion

universe u

@[reducible] def pathClockSignature : Signature where
  Params := Sigma fun A : Type u => List A -> A -> ℝ
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization pathClockSignature.{u} :=
  realize pathClockSignature.{u}
    (fun _ p h => pathClock p.2 h)
    (fun e => nomatch e)

def rejected : Realization pathClockSignature.{u} :=
  realize pathClockSignature.{u}
    (fun _ _ _ => (0 : ℝ))
    (fun e => nomatch e)

def arena : Arena where
  signature := pathClockSignature.{u}
  Law R := ∀ {A : Type u} [Fintype A] [Nonempty A]
      (c : List A -> A -> ℝ) (_hc : ∀ h x, 0 ≤ c h x),
    List.TFAE [
      ∀ omega : ℕ -> A,
        Tendsto (fun n => pathClock c (List.ofFn fun i : Fin n => omega i)) atTop atTop,
      Tendsto (minimumPathClock c) atTop atTop,
      ∀ b : ℝ, {h : List A | R.readout () ⟨A, c⟩ h ≤ b}.Finite]

run_cmd do
  let root := `Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
  let sourceName := `D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion ++
    `finite_branching_path_clock_criterion
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    capturedStatement := captureStatement (← getEnv) sourceName
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have htfae := h (A := ULift.{u} Unit) (fun _ _ => (1 : ℝ)) (by simp)
  have hpath : ∀ omega : ℕ -> ULift.{u} Unit,
      Tendsto
        (fun n => pathClock (fun _ _ => (1 : ℝ))
          (List.ofFn fun i : Fin n => omega i)) atTop atTop := by
    intro omega
    simpa [pathClock] using (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpath_iff_finite :
      (∀ omega : ℕ -> ULift.{u} Unit,
        Tendsto
          (fun n => pathClock (fun _ _ => (1 : ℝ))
            (List.ofFn fun i : Fin n => omega i)) atTop atTop) ↔
      (∀ b : ℝ,
        {h : List (ULift.{u} Unit) |
          rejected.{u}.readout () ⟨ULift.{u} Unit, fun _ _ => (1 : ℝ)⟩ h ≤ b}.Finite) :=
    htfae.out 0 2
  have hfinite := hpath_iff_finite.mp hpath 0
  have huniv : (Set.univ : Set (List (ULift.{u} Unit))).Finite := by
    simpa [rejected, realize, pathClockSignature] using hfinite
  exact Set.infinite_univ.not_finite huniv

theorem actual_law : arena.{u}.Law actual.{u} := by
  intro A _ _ c hc
  simpa [actual, realize, pathClockSignature] using
    finite_branching_path_clock_criterion c hc

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected.{u}, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof :
    ObservationalDependence pathClockSignature.{u} actual.{u} := by
  intro i
  cases i
  let p : pathClockSignature.{u}.Params :=
    ⟨ULift.{u} Unit, fun _ _ => (1 : ℝ)⟩
  refine ⟨p, [], [⟨()⟩], ?_⟩
  norm_num [actual, realize, pathClockSignature, pathClock]

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual.{u}
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected.{u}, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem finite_branching_path_clock_criterion in arena
  readout via (realize pathClockSignature.{u}
    (fun _ p h => pathClock p.2 h)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg",
        "fn", "arg", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Estimation.ExperimentCost.FiniteBranchingPathClockCriterion
