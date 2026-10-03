import D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
open LeanInformationAudit
open Lean Elab Command
open scoped BigOperators Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace

universe u

@[reducible] def darkSignature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℂ
  State p := Fin p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization darkSignature :=
  realize darkSignature
    (fun _ p ψ =>
      ((1 - (p.2ᴴ) ^ p.1 * p.2 ^ p.1).mulVec ψ : Fin p.1 → ℂ))
    (fun e => nomatch e)

def rejected : Realization darkSignature :=
  realize darkSignature
    (fun _ p _ => (0 : Fin p.1 → ℂ))
    (fun e => nomatch e)

def arena : Arena where
  signature := darkSignature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1)
    (ψ : Fin d → ℂ),
    (∀ n : ℕ, ∀ x : ι, (L x * Q ^ n).mulVec ψ = 0) ↔
      R.readout () ⟨d, Q⟩ ψ = 0

run_cmd do
  let root := `Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
  let sourceName := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace ++
    `dark_space_eq_survival_defect_kernel
  let identity := "sha256:259e4ff0d4aef58804c19d4748d714e05ef8e9f3f4fac99d5af8be3c97326f57"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

def oneVector : Fin 1 → ℂ := fun _ => 1

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have htest := h (d := 1) (ι := ULift.{u} Unit)
    (0 : Matrix (Fin 1) (Fin 1) ℂ)
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) (by simp) oneVector
  have hall := htest.mpr (by rfl)
  have hzero := hall 0 ⟨()⟩
  have hentry := congrFun hzero 0
  have : (1 : ℂ) = 0 := by
    simpa [rejected, realize, darkSignature, oneVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_one] using hentry
  exact one_ne_zero this

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp ψ
  exact dark_space_eq_survival_defect_kernel Q L hcomp ψ

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

theorem dependence_proof : ObservationalDependence darkSignature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0⟩, oneVector, (0 : Fin 1 → ℂ), ?_⟩
  intro h
  have hentry := congrFun h 0
  norm_num [actual, realize, darkSignature, oneVector, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one] at hentry

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem dark_space_eq_survival_defect_kernel in arena
  readout via (realize darkSignature
    (fun _ p ψ =>
      ((1 - (p.2ᴴ) ^ p.1 * p.2 ^ p.1).mulVec ψ : Fin p.1 → ℂ))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
