import D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate
import Reg.Support.DependentFamily
import Reg.Support.GeneralInstrumentModels

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open Reg.Support.GeneralInstrumentModels
open LeanInformationAudit Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate

@[reducible] def signature : Signature where
  Params := ℕ
  State d := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d g => (d : ℝ) / g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1),
    (darkLayer Q L d = ⊥ →
      ∃ g : ℝ, 0 < g ∧ (g : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 - survival Q d) ∧
    ∀ g : ℝ, 0 < g → (g : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 - survival Q d →
      (∀ m, survival Q (m * d) ≤ (((1 - g) ^ m : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        Summable (fun N => (ρ * survival Q N).trace.re) ∧
          ∑' N, (ρ * survival Q N).trace.re ≤ R.readout () d g

theorem actual_law : arena.Law actual := by
  intro d α ι _ _ Q L hcomp
  exact detection_certificate Q L hcomp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgap : (1 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) ≤
      1 - survival (fun _ : Unit => (0 : Matrix (Fin 1) (Fin 1) ℂ)) 1 := by
    simp [survival_zero_succ]
  have hb := ((h (d := 1) (α := Unit) (ι := Unit)
    (fun _ => 0) (fun _ => 1) (complete 1)).2 1 (by norm_num) hgap).2
    1 Matrix.PosSemidef.one (by simp)
  have hseq : (fun N => ((1 : Matrix (Fin 1) (Fin 1) ℂ) *
      survival (fun _ : Unit => (0 : Matrix (Fin 1) (Fin 1) ℂ)) N).trace.re) =
      (fun N => if N = 0 then (1 : ℝ) else 0) := by
    funext N
    cases N with
    | zero => simp [survival]
    | succ N => simp [survival_zero_succ]
  have hsum : (∑' N, ((1 : Matrix (Fin 1) (Fin 1) ℂ) *
      survival (fun _ : Unit => (0 : Matrix (Fin 1) (Fin 1) ℂ)) N).trace.re) = 1 := by
    rw [hseq]
    simp
  have hbound := hb.2
  change (∑' N, ((1 : Matrix (Fin 1) (Fin 1) ℂ) *
    survival (fun _ : Unit => (0 : Matrix (Fin 1) (Fin 1) ℂ)) N).trace.re) ≤ -1 at hbound
  rw [hsum] at hbound
  norm_num at hbound

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
  exact ⟨1, 1, 2, by norm_num [actual, realize]⟩

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem detection_certificate in arena
  readout via (realize signature (fun _ d g => (d : ℝ) / g) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "arg", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate
