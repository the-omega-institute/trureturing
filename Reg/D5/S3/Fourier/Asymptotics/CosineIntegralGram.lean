import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Reg.Support.DependentFamily

open MeasureTheory
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The whole original conjunction, on the whole real line and at every positive pair. -/
def arena : Arena where
  signature := signature
  Law r := ∀ a b : ℝ, 0 < a → 0 < b →
    Integrable (fun z : ℝ => r.readout () ⟨a, b⟩ z) ∧
      (∫ z : ℝ, r.readout () ⟨a, b⟩ z) = Real.pi / max a b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 1 1 zero_lt_one zero_lt_one).2
  have hp := Real.pi_pos
  norm_num [rejected, realize] at hz
  linarith

/-- A constant integrand on infinite Lebesgue volume has zero Bochner integral;
the original positive Gram mass therefore forces actual state dependence. -/
theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push Not at h
  have hc : (fun z : ℝ => cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|)) =
      fun _ : ℝ => cosineIntegral (1 * |(0 : ℝ)|) * cosineIntegral (1 * |(0 : ℝ)|) := by
    funext z
    exact h ⟨1, 1⟩ z 0
  have hm := (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
    zero_lt_one zero_lt_one).2
  rw [hc] at hm
  simp [measureReal_def, Real.volume_univ] at hm
  exact Real.pi_ne_zero hm.symm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

register_information_theorem _root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result in arena
  readout via (realize signature
    (fun _ p z => cosineIntegral (p.1 * |z|) * cosineIntegral (p.2 * |z|))
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.CosineIntegralGram
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "body"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineIntegralGram
