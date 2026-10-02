import D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open LeanInformationAudit
open Lean Elab Command
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

local notation "kact" => fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost

universe u

@[reducible] def effectSignature : Signature where
  Params := Type u
  State ι := Matrix ι ι ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := Matrix ι ι ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization effectSignature.{u} :=
  realize effectSignature.{u} (fun _ _ R => R) (fun e => nomatch e)

def rejected : Realization effectSignature.{u} :=
  realize effectSignature.{u}
    (fun _ ι _ => (0 : Matrix ι ι ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := effectSignature.{u}
  Law Q := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R : Matrix ι ι ℂ) (hR : R.PosDef),
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ), ExactPreparationContract R K →
      ∃ c : ℝ, 0 < c ∧ ∀ X : Matrix ι ι ℂ,
        kact K X = (c : ℂ) • (CFC.sqrt R * X * CFC.sqrt R)) ∧
    (∀ c : ℝ, 0 < c →
      let Kc : Fin 1 → Matrix ι ι ℂ := fun _ =>
        (Real.sqrt c) • CFC.sqrt R;
      (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
        0 < (kact Kc ρ).trace.re ∧
        kact Kc ρ = ((kact Kc ρ).trace / (R * ρ).trace) •
          (CFC.sqrt R * ρ * CFC.sqrt R)) ∧
      (TraceNonincreasing Kc ↔ (1 - c • R).PosSemidef)) ∧
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ) (c : ℝ), 0 < c →
      (∀ X : Matrix ι ι ℂ,
        kact K X = (c : ℂ) • (CFC.sqrt R * X * CFC.sqrt R)) →
      (TraceNonincreasing K ↔ (1 - (c : ℂ) • R).PosSemidef)) ∧
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ), ExactPreparationContract R K →
      TraceNonincreasing K → ∃ ρ : Matrix ι ι ℂ,
        ρ.PosSemidef ∧ ρ.trace = 1 ∧
        (kact K ρ).trace.re ≤
          leastEigenvalue R hR / greatestEigenvalue R hR) ∧
    (let Kopt : Fin 1 → Matrix ι ι ℂ := fun _ =>
        (((1 / Real.sqrt (greatestEigenvalue R hR) : ℝ) : ℂ) • CFC.sqrt R);
      let Kfail : Matrix ι ι ℂ :=
        CFC.sqrt (1 - ((1 / greatestEigenvalue R hR : ℝ) : ℂ) • R);
      ExactPreparationContract R Kopt ∧ TraceNonincreasing Kopt ∧
        (Kopt 0)ᴴ * Kopt 0 + Kfailᴴ * Kfail = 1 ∧
        ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
          leastEigenvalue R hR / greatestEigenvalue R hR ≤
            (kact Kopt ρ).trace.re) ∧
    ((∃ (m : ℕ) (K : Fin m → Matrix ι ι ℂ),
        ExactPreparationContract R K ∧ TraceNonincreasing K ∧
        ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
          (kact K ρ).trace = 1) ↔
      ∃ scalar : ℝ, 0 < scalar ∧
        Q.readout () ι R = (scalar : ℂ) • 1)

run_cmd do
  let root := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
  let sourceName := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost ++
    `exact_conditional_preparation_cost
  let identity := captureStatement (← getEnv) sourceName
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    capturedStatement := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hLaw := h
    (R := (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ))
    Matrix.PosDef.one
  have hDeterministic :
      ∃ (m : ℕ) (K : Fin m →
        Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ),
        ExactPreparationContract 1 K ∧ TraceNonincreasing K ∧
        ∀ ρ : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ,
          ρ.PosSemidef → ρ.trace = 1 →
          (kact K ρ).trace = 1 := by
    exact (exact_conditional_preparation_cost
      (R := (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ))
        Matrix.PosDef.one).2.2.2.2.2.mpr
        ⟨1, by norm_num, by simp⟩
  obtain ⟨scalar, hscalar, hzero⟩ := hLaw.2.2.2.2.2.mp hDeterministic
  have hentry := congrFun (congrFun hzero (ULift.up 0)) (ULift.up 0)
  change (0 : ℂ) = (scalar : ℂ) *
    (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ)
      (ULift.up 0) (ULift.up 0) at hentry
  have hscalarComplex : (scalar : ℂ) = 0 := by
    simpa only [Matrix.one_apply_eq, mul_one] using hentry.symm
  exact hscalar.ne' (Complex.ofReal_injective hscalarComplex)

theorem actual_law : arena.{u}.Law actual := by
  intro ι _ _ _ R hR
  simpa only [actual, realize] using exact_conditional_preparation_cost R hR

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

theorem dependence_proof : ObservationalDependence effectSignature.{u} actual := by
  intro i
  cases i
  refine ⟨ULift.{u} (Fin 1),
    (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ),
    (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h (ULift.up 0)) (ULift.up 0)
  norm_num [actual, realize] at hentry

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem exact_conditional_preparation_cost in arena
  readout via (realize effectSignature.{u} (fun _ _ R => R) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
