import D5.S3.Quantum.Measurement.FiniteDetectionTailBound
import Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionTailBound
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder Matrix MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound

universe u
namespace Survival

abbrev signature :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature

abbrev actual := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual

abbrev rejected := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1),
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
      (∀ m : ℕ, 0 ≤ R.readout () ⟨d, Q⟩ (m * d) - darkProjection Q L ∧
        R.readout () ⟨d, Q⟩ (m * d) - darkProjection Q L ≤
          (1 - g) ^ m • (1 - darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → darkProjection Q L * ρ = 0 →
          Summable (fun N : ℕ => (ρ * R.readout () ⟨d, Q⟩ N).trace.re) ∧
          ∑' N : ℕ, (ρ * R.readout () ⟨d, Q⟩ N).trace.re ≤ (d : ℝ) / g

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp
  exact finite_detection_tail_bound Q L hcomp

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by simp [Q]
  obtain ⟨g, _hg, _hg1, hblock, _htail⟩ := h Q L hcomp
  have hbad := (hblock 0).2
  simp only [rejected,
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected,
    realize, signature, Q, pow_zero, mul_one, one_smul] at hbad
  have hdiag := (Matrix.le_iff.mp hbad).diag_nonneg (i := 0)
  have hdiag' : (1 : ℂ) ≤ 0 := by simpa using hdiag
  exact (not_le_of_gt (zero_lt_one : (0 : ℂ) < 1)) hdiag'

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

theorem dependence_proof : ObservationalDependence signature actual :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dependence_proof

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem finite_detection_tail_bound in arena
  readout via (realize signature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.FiniteDetectionTailBound
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "arg", "body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "body", "arg", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Survival
end Reg.D5.S3.Quantum.Measurement.FiniteDetectionTailBound
