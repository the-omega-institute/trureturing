import D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
open LeanInformationAudit
open Lean Elab Command
open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect

@[reducible] def signature : Signature where
  Params := ℝ
  State _ := Matrix (Fin 2) (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ), 0 < a → a < 1 →
    ∃ (Q : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
      (L : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ)
      (F : Matrix (Fin 2) (Fin 2) ℂ),
      Q 0 = basisProjector (0 : Fin 2) ∧
      Q 1 = Matrix.single 0 1 (Real.sqrt a : ℂ) ∧
      L 0 = (Real.sqrt (1 - a) : ℂ) • basisProjector (1 : Fin 2) ∧
      (∑ i, (Q i)ᴴ * Q i) + ∑ i, (L i)ᴴ * L i = 1 ∧
      (∀ X, noClickDual Q X = X 0 0 • F) ∧
      (∀ N, 1 ≤ N → survival Q N = F) ∧
      Tendsto (survival Q) atTop (𝓝 F) ∧
      R.readout () a F =
        basisProjector (0 : Fin 2) + (a : ℂ) • basisProjector (1 : Fin 2) ∧
      F * F ≠ F ∧
      (∀ v : Fin 2 → ℂ, star v ⬝ᵥ v = 1 →
        (star v ⬝ᵥ (F *ᵥ v) = 1 ↔ v 1 = 0)) ∧
      (basisProjector (1 : Fin 2) * F).trace = (a : ℂ) ∧
      (basisProjector (1 : Fin 2) * ((L 0)ᴴ * L 0)).trace = ((1 - a : ℝ) : ℂ) ∧
      (basisProjector (1 : Fin 2) * basisProjector (0 : Fin 2)).trace = 0

run_cmd do
  let root := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
  let sourceName := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect ++
    `non_projective_dark_effect
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    capturedStatement := captureStatement (← getEnv) sourceName
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize] using non_projective_dark_effect

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Q, L, F, _hQ0, _hQ1, _hL0, _hcomp, _hdual, _hstable, _hlimit,
    hF, _hnotIdempotent, _hunitDirections, _htrace, _hclick, _hweight⟩ :=
      h (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hentry := congrFun (congrFun hF (0 : Fin 2)) (0 : Fin 2)
  simp only [rejected, realize, signature, basisProjector, Matrix.add_apply,
    Matrix.smul_apply, Matrix.single_apply] at hentry
  have hzero : (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Fin 2) (0 : Fin 2) = 0 := rfl
  rw [hzero] at hentry
  norm_num at hentry

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

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(0 : ℝ), (0 : Matrix (Fin 2) (Fin 2) ℂ),
    (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [actual, realize] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem non_projective_dark_effect in arena
  readout via (realize signature (fun _ _ F => F) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
