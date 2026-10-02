import D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
import Reg.Support.DependentFamily
import Reg.Support.GeneralInstrumentModels

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open Reg.Support.GeneralInstrumentModels
open LeanInformationAudit Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

@[reducible] def signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d) (Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ d _ => -(1 : Matrix (Fin d) (Fin d) ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1),
    ∃ F : Matrix (Fin d) (Fin d) ℂ,
      Tendsto (survival Q) atTop (𝓝 F) ∧
      (∀ N, 0 ≤ survival Q N ∧ survival Q (N + 1) ≤ survival Q N ∧ survival Q N ≤ 1 ∧
        F ≤ survival Q N) ∧
      0 ≤ R.readout () d F ∧ F ≤ 1 ∧ noClickDual Q F = F ∧
      (∀ H : Matrix (Fin d) (Fin d) ℂ, 0 ≤ H → H ≤ 1 → noClickDual Q H = H → H ≤ F) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => (ρ * survival Q N).trace) atTop (𝓝 (ρ * F).trace)

theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp
  exact survival_tendsto_maximal_fixed_effect Q L hcomp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨F, _hF, _hchain, hp, _⟩ := h (d := 1) (α := Unit) (ι := Unit)
    (fun _ => 0) (fun _ => 1) (complete 1)
  change (0 : Matrix (Fin 1) (Fin 1) ℂ) ≤ -1 at hp
  have he := hp.posSemidef.diag_nonneg (i := (0 : Fin 1))
  norm_num [Complex.le_def] at he

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
  exact ⟨1, 0, 1, zero_ne_one⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem survival_tendsto_maximal_fixed_effect in arena
  readout via (realize signature (fun _ _ F => F) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
