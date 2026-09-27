import D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
import Reg.Support.DependentFamily
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
open LeanInformationAudit
open Lean Elab Command
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance

@[reducible] def graphDistanceSignature : Signature where
  Params := Σ d : ℕ, {H : Matrix (Fin d) (Fin d) ℝ //
    (∀ i j, H i j = H j i) ∧ (∀ i j, i ≠ j → 0 ≤ H i j)}
  State p := Fin p.1 × Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization graphDistanceSignature :=
  realize graphDistanceSignature
    (fun _ p q =>
      (q.1 ≠ q.2 ∧ (couplingGraph p.2.1).Reachable q.1 q.2) ∧
        ((∀ n < (couplingGraph p.2.1).dist q.1 q.2,
          (p.2.1 ^ n) q.2 q.1 = 0) ∧
          0 < (p.2.1 ^ (couplingGraph p.2.1).dist q.1 q.2) q.2 q.1))
    (fun e => nomatch e)

def rejected : Realization graphDistanceSignature :=
  realize graphDistanceSignature
    (fun _ _ _ => False)
    (fun e => nomatch e)

def arena : Arena where
  signature := graphDistanceSignature
  Law R := ∀ {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    {i j : Fin d} (_hne : i ≠ j)
    (_hreach : (couplingGraph H).Reachable i j),
    R.readout () ⟨d, ⟨H, ⟨hsym, hoff⟩⟩⟩ ⟨i, j⟩

run_cmd do
  let root := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
  let sourceName := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance ++
    `first_nonzero_power_eq_graph_distance
  let identity := "sha256:f93df77c5b48e83e40d3dba0b9f74eefc46b8a1e5a1d7c3ddecb5d0cff0457ca"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have htest := h (d := 2)
    (H := fun _ _ => (1 : ℝ))
    (hsym := by simp)
    (hoff := by simp)
    (i := 0) (j := 1) (by decide)
    (by exact ⟨SimpleGraph.Walk.cons (by simp [couplingGraph]) .nil⟩)
  exact htest

theorem actual_law : arena.Law actual := by
  intro d H hsym hoff i j hne hreach
  exact ⟨⟨hne, hreach⟩, first_nonzero_power_eq_graph_distance H hsym hoff hne hreach⟩

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence graphDistanceSignature actual := by
  intro i
  cases i
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  have hsym : ∀ i j, H i j = H j i := by simp [H]
  have hoff : ∀ i j, i ≠ j → 0 ≤ H i j := by simp [H]
  have hreach : (couplingGraph H).Reachable (0 : Fin 2) 1 := by
    exact ⟨SimpleGraph.Walk.cons (by simp [couplingGraph, H]) .nil⟩
  refine ⟨⟨2, ⟨H, ⟨hsym, hoff⟩⟩⟩, (⟨0, 0⟩ : Fin 2 × Fin 2),
    (⟨0, 1⟩ : Fin 2 × Fin 2), ?_⟩
  intro h
  have htheorem := first_nonzero_power_eq_graph_distance H hsym hoff
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) hreach
  have hy : actual.readout () ⟨2, ⟨H, ⟨hsym, hoff⟩⟩⟩ (⟨0, 1⟩ : Fin 2 × Fin 2) := by
    change ((0 : Fin 2) ≠ 1 ∧ (couplingGraph H).Reachable 0 1) ∧ _
    exact ⟨⟨by decide, hreach⟩, htheorem⟩
  have hxFalse : ¬ actual.readout () ⟨2, ⟨H, ⟨hsym, hoff⟩⟩⟩ (⟨0, 0⟩ : Fin 2 × Fin 2) := by
    intro hx
    simpa [actual, realize, graphDistanceSignature, H, couplingGraph] using hx
  have hbad : actual.readout () ⟨2, ⟨H, ⟨hsym, hoff⟩⟩⟩ (⟨0, 0⟩ : Fin 2 × Fin 2) := by
    rw [h]
    exact hy
  exact hxFalse hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem first_nonzero_power_eq_graph_distance in arena
  readout via (realize graphDistanceSignature
    (fun _ p q =>
      (q.1 ≠ q.2 ∧ (couplingGraph p.2.1).Reachable q.1 q.2) ∧
        ((∀ n < (couplingGraph p.2.1).dist q.1 q.2,
          (p.2.1 ^ n) q.2 q.1 = 0) ∧
          0 < (p.2.1 ^ (couplingGraph p.2.1).dist q.1 q.2) q.2 q.1))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
    coordinates := #[0, 0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
