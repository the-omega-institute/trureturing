import D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
import Reg.Support.DependentFamily
import LeanInformationAudit.Syntax

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
open LeanInformationAudit
open Lean Elab Command
open BigOperators Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance

universe u

@[reducible] def branchSignature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℂ
  State p := Matrix (Fin p.1) (Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization branchSignature :=
  realize branchSignature
    (fun _ p σ => traceNorm (p.2 - σ) / 2)
    (fun e => nomatch e)

def rejected : Realization branchSignature :=
  realize branchSignature
    (fun _ _ _ => (-1 : ℝ))
    (fun e => nomatch e)

def arena : Arena where
  signature := branchSignature
  Law R := ∀ {d : ℕ} {ι : Type*} [Fintype ι]
    (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (K : ι → Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (hρtrace : ρ.trace = 1)
    (hσ : σ.PosSemidef) (hσtrace : σ.trace = 1)
    (hB : (∑ i, (K i)ᴴ * K i) ≤ (1 : Matrix (Fin d) (Fin d) ℂ)),
    let B := ∑ i, (K i)ᴴ * K i
    let Φ := fun X : Matrix (Fin d) (Fin d) ℂ ↦ ∑ i, K i * X * (K i)ᴴ
    let p := (ρ * B).trace.re
    let q := (σ * B).trace.re
    let D := fun X Y : Matrix (Fin d) (Fin d) ℂ ↦ traceNorm (X - Y) / 2
    |p - q| ≤ R.readout () ⟨d, ρ⟩ σ ∧
      ((0 < p ∧ 0 < q) →
        max p q * D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ D ρ σ) ∧
      ∀ pStar ε : ℝ, 0 < pStar → pStar ≤ p → D ρ σ ≤ ε → ε < pStar →
        0 < q ∧ D ((1 / p) • Φ ρ) ((1 / q) • Φ σ) ≤ ε / pStar

run_cmd do
  let root := `Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
  let sourceName := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance ++
    `branch_conditioned_trace_distance
  let identity := "sha256:b0402a35876d7baf34f9739ea040e967bd9424a79b7beeec1e4813eca3c8b804"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have htest := h (d := 1) (ι := ULift.{u} Empty)
    (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (fun i => nomatch i.down)
    Matrix.PosSemidef.one (by simp)
    Matrix.PosSemidef.one (by simp) (by simp)
  norm_num [rejected, realize, branchSignature] at htest

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ ρ σ K hρ hρtrace hσ hσtrace hB
  simpa only [actual, realize, branchSignature] using
    branch_conditioned_trace_distance ρ σ K hρ hρtrace hσ hσtrace hB

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence branchSignature actual := by
  intro i
  cases i
  refine ⟨⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ)⟩,
    (0 : Matrix (Fin 1) (Fin 1) ℂ), (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  have hnormZero : traceNorm (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    simpa using h
  have hnormOne : traceNorm (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.PosSemidef.one :
        (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    simpa using h
  intro h
  norm_num [actual, realize, branchSignature, hnormZero, traceNorm_neg, hnormOne] at h

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem branch_conditioned_trace_distance in arena
  readout via (realize branchSignature
    (fun _ p σ => traceNorm (p.2 - σ) / 2)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.BranchConditionedTraceDistance
