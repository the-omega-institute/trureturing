import D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
import Reg.Support.DependentFamily
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
open Lean Elab Command
open Filter LeanInformationAudit Matrix Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction

@[reducible] def residualSignature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization residualSignature :=
  realize residualSignature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization residualSignature :=
  realize residualSignature (fun _ _ F => F + 1) (fun e => nomatch e)

def arena : Arena where
  signature := residualSignature
  Law R := ∀ {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (_hF : Tendsto (survival Q) atTop (𝓝 F)),
    (∀ n, survival Q n - R.readout () d F =
        (noClickDual Q)^[n] ((1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
      0 ≤ survival Q n - F ∧
        survival Q n - F ≤ (1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
    (∃ M : ℕ, 1 ≤ M ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      survival Q M - F ≤ q • ((1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
      (∀ n, survival Q n - F ≤
        q ^ (n / M) • ((1 : Matrix (Fin d) (Fin d) ℂ) - F)) ∧
      Summable (fun n => survival Q n - F) ∧
      let T := ∑' n, (survival Q n - F)
      0 ≤ T ∧ T ≤ ((M : ℝ) / (1 - q)) •
          ((1 : Matrix (Fin d) (Fin d) ℂ) - F) ∧
        T - noClickDual Q T = (1 : Matrix (Fin d) (Fin d) ℂ) - F ∧
        (∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          let rρ := (ρ * ((1 : Matrix (Fin d) (Fin d) ℂ) - F)).trace.re
          0 < rρ → (ρ * T).trace.re / rρ ≤ (M : ℝ) / (1 - q)) ∧
        (∀ k, 0 ≤ T - ∑ n ∈ Finset.range (k * M), (survival Q n - F) ∧
          T - ∑ n ∈ Finset.range (k * M), (survival Q n - F) ≤
            ((M : ℝ) * q ^ k / (1 - q)) •
              ((1 : Matrix (Fin d) (Fin d) ℂ) - F)) ∧
        (∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          let rρ := (ρ * ((1 : Matrix (Fin d) (Fin d) ℂ) - F)).trace.re
          0 < rρ → ∀ k,
            0 ≤ (ρ * (T - ∑ n ∈ Finset.range (k * M),
              (survival Q n - F))).trace.re / rρ ∧
            (ρ * (T - ∑ n ∈ Finset.range (k * M),
              (survival Q n - F))).trace.re / rρ ≤
                (M : ℝ) * q ^ k / (1 - q)) ∧
        ∀ (X : Matrix (Fin d) (Fin d) ℂ) (c : ℝ),
          X - noClickDual Q X = (1 : Matrix (Fin d) (Fin d) ℂ) - F →
            0 ≤ X → X ≤ c • ((1 : Matrix (Fin d) (Fin d) ℂ) - F) → X = T)

run_cmd do
  let root := `Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
  let sourceName := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction ++
    `residual_tail_contraction
  let identity := theoremStatementIdentity (← getEnv) sourceName
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp F hF
  simpa only [actual, realize, residualSignature] using
    residual_tail_contraction Q L hcomp F hF

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let Q : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 0
  let L : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
  have hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1 := by
    simp [Q, L]
  have hF : Tendsto (survival Q) atTop
      (𝓝 (0 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    cases n with
    | zero => omega
    | succ n => simp [survival, noClickDual, Q]
  have hbad := (h Q L hcomp 0 hF).1 0 |>.1
  have hentry := congrFun (congrFun hbad 0) 0
  norm_num [rejected, realize, residualSignature, survival] at hentry

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

theorem dependence_proof : ObservationalDependence residualSignature actual := by
  intro i
  cases i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ), (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num [actual, realize, residualSignature] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem residual_tail_contraction in arena
  readout via (realize residualSignature (fun _ _ F => F) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
