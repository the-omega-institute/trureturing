import D5.S3.Fourier.Asymptotics.CosineGaussianGramRate
import Reg.Support.DependentFamily

open MeasureTheory
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate

/-- All four original real parameters and every real integration state are retained. -/
abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p (z : ℝ) => Real.exp (-p.2.2.1 * (z / p.2.2.2) ^ 2))
    (fun e => nomatch e)

/-- This intervention changes the Gaussian role across its complete parameter family. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

/-- Both occurrences of the Gaussian are replaced by the same readout family.
The cosine integrals, target Gram mass, bound, and hypotheses are fixed source operands. -/
def arena : Arena where
  signature := signature
  Law r := ∀ a b beta R : ℝ, 0 < a → 0 < b → 0 < beta → 0 < R →
    Integrable (fun z : ℝ =>
      cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        (r.readout () ⟨a, b, beta, R⟩ z : ℝ)) ∧
    |(∫ z : ℝ, cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        (r.readout () ⟨a, b, beta, R⟩ z : ℝ)) - Real.pi / max a b| ≤
      8 * (beta + 1) / (a * b * R)

theorem rejected_integrable (a b beta R : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun z : ℝ =>
      cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        (rejected.readout () ⟨a, b, beta, R⟩ z : ℝ)) :=
  (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result a b ha hb).1.mul_const 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbound := (h 1 1 1 100 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2
  change |(∫ z : ℝ, cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|) * 2) -
    Real.pi / max 1 1| ≤ 8 * (1 + 1) / (1 * 1 * 100) at hbound
  rw [integral_mul_const,
    (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
      (by norm_num) (by norm_num)).2] at hbound
  norm_num at hbound
  have habs := le_abs_self (Real.pi * 2 - Real.pi)
  linarith [Real.pi_gt_three]

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j h
    exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
  change Real.exp (-(1 : ℝ) * (0 / 1) ^ 2) ≠
    Real.exp (-(1 : ℝ) * (1 / 1) ^ 2)
  intro h
  have hexponent := Real.exp_injective h
  norm_num at hexponent

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result,
    rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate.result in arena
  readout via (realize signature
    (fun _ p (z : ℝ) => Real.exp (-p.2.2.1 * (z / p.2.2.2) ^ 2)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.CosineGaussianGramRate
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 8 }] })
  escape continues (open)

end Reg.D5.S3.Fourier.Asymptotics.CosineGaussianGramRate
