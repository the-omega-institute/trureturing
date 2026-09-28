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
  Params := Σ d : ℕ, Σ _ : Matrix (Fin d) (Fin d) ℝ, Σ _ : Fin d, Fin d
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization graphDistanceSignature :=
  realize graphDistanceSignature
    (fun _ p n => (p.2.1 ^ n) p.2.2.2 p.2.2.1)
    (fun e => nomatch e)

def rejected : Realization graphDistanceSignature :=
  realize graphDistanceSignature
    (fun _ _ _ => (1 : ℝ))
    (fun e => nomatch e)

def arena : Arena where
  signature := graphDistanceSignature
  Law R := ∀ {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ)
    (_hsym : ∀ i j, H i j = H j i)
    (_hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    {i j : Fin d} (_hne : i ≠ j)
    (_hreach : (couplingGraph H).Reachable i j),
    (∀ n < (couplingGraph H).dist i j, R.readout () ⟨d, H, i, j⟩ n = 0) ∧
      0 < (H ^ (couplingGraph H).dist i j) j i

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
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  have hadj : (couplingGraph H).Adj (0 : Fin 2) 1 := by
    simp [couplingGraph, H]
  have hdist : (couplingGraph H).dist (0 : Fin 2) 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have htest := (h H (by simp [H]) (by simp [H])
    (i := 0) (j := 1) (by decide) hadj.reachable).1 0 (by omega)
  norm_num [rejected, realize, graphDistanceSignature] at htest

theorem actual_law : arena.Law actual := by
  intro d H hsym hoff i j hne hreach
  exact first_nonzero_power_eq_graph_distance H hsym hoff hne hreach

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
  let p : graphDistanceSignature.Params := ⟨2, H, 0, 1⟩
  refine ⟨p, (0 : ℕ), (1 : ℕ), ?_⟩
  change (H ^ (0 : ℕ)) (1 : Fin 2) (0 : Fin 2) ≠ (H ^ (1 : ℕ)) 1 0
  rw [pow_zero, pow_one]
  norm_num [Matrix.one_apply, H]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem first_nonzero_power_eq_graph_distance in arena
  readout via (realize graphDistanceSignature
    (fun _ p n => (p.2.1 ^ n) p.2.2.2 p.2.2.1)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
