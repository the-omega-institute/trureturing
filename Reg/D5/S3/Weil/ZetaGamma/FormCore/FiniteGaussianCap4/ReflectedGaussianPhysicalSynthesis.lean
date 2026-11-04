import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianPhysicalSynthesis
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfSynthesisCharge
import Reg.Support.SingleDependentReadout

/-! The readout is actual physical synthesis, with the complete original
coefficient, span and almost-everywhere realization clauses retained. -/

open MeasureTheory
open FiniteGaussianCap4
open FiniteGaussianCap4.LaguerreSevenHalf
open FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit RHGaussianDilationCore

noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianPhysicalSynthesis

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Coeff)
    (fun _ => Lp ℝ 1 mellinMeasure)

private def basis : Coeff := lp.single 2 0 (1 : ℝ)

private theorem basis_charge : mellinIntegral (synthesis basis) = normalizedCentralMellin 0 := by
  rw [synthesis_mellin_charge]
  simp only [coeffCharge, innerSL_apply_apply, lp.inner_single_right, Real.inner_apply, basis]
  change normalizedCentralMellin 0 *
      ((actualCentralZ 0 / coeffWeight 0) * 1) = normalizedCentralMellin 0
  have h0 : normalizedCentralMellin 0 ≠ 0 := by
    simpa only [Nat.mul_zero] using (normalizedCentralMellin_even_pos 0).ne'
  simp [actualCentralZ, coeffWeight, h0]

def actual : Realization signature :=
  realize signature (fun _ _ w => (synthesis w).2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ w => (synthesis w).2 + (synthesis basis).2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    ∃ f : ℝ → Coeff,
      (∀ t : ℝ, 0 < t → t < 1 / 36 → ∀ n : ℕ,
        f t n = RHGaussianDilationCore.coeffWeight n *
          RHGaussianDilationCore.actualReflectedCurveCoefficient t n) ∧
      RHGaussianDilationCore.positiveCurveSpan f (1 / 36) =
        (RHGaussianDilationCore.coeffCharge
          RHGaussianDilationCore.actualCentralChargeVector).ker ∧
      ∀ t : ℝ, 0 < t → t < 1 / 36 →
        let a := RHGaussianDilationCore.positiveGaussianSite t
        let F := fun x => gaussianFeature RHGaussianDilationCore.reflectedSourceCoefficient
          (RHGaussianDilationCore.reflectedSourceSite a) x /
            (2 * gaussianSiteAmplitude a)
        (((synthesis (f t)).1 : ℝ → ℝ) =ᵐ[graphMeasure] F) ∧
        ((R.readout () () (f t) : ℝ → ℝ) =ᵐ[mellinMeasure] F)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨f, hf, _, hphysical⟩
  obtain ⟨g, hg, _, hactual⟩ := actual_reflected_gaussian_physical_synthesis
  have ht : (0 : ℝ) < 1 / 72 := by norm_num
  have ht1 : (1 / 72 : ℝ) < 1 / 36 := by norm_num
  have hfg : f (1 / 72) = g (1 / 72) := by
    apply lp.ext
    funext n
    rw [hf _ ht ht1 n, hg _ ht ht1 n]
  obtain ⟨_, hbad2⟩ := hphysical (1 / 72) ht ht1
  obtain ⟨_, hgood2⟩ := hactual (1 / 72) ht ht1
  have heq : (synthesis (g (1 / 72))).2 + (synthesis basis).2 =
      (synthesis (g (1 / 72))).2 := by
    rw [hfg] at hbad2
    exact Lp.ext (hbad2.trans hgood2.symm)
  have hz : (synthesis basis).2 = 0 := add_left_cancel (show
      (synthesis (g (1 / 72))).2 + (synthesis basis).2 =
        (synthesis (g (1 / 72))).2 + 0 by simpa using heq)
  have hc := basis_charge
  change (L1.integralCLM (α := ℝ) (E := ℝ) (μ := mellinMeasure))
    (synthesis basis).2 = _ at hc
  rw [hz, map_zero] at hc
  exact (normalizedCentralMellin_even_pos 0).ne' hc.symm

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, basis, ?_⟩
  change (synthesis 0).2 ≠ (synthesis basis).2
  rw [map_zero]
  change (0 : Lp ℝ 1 mellinMeasure) ≠ (synthesis basis).2
  intro h
  have hc := basis_charge
  change (L1.integralCLM (α := ℝ) (E := ℝ) (μ := mellinMeasure))
    (synthesis basis).2 = _ at hc
  rw [← h, map_zero] at hc
  exact (normalizedCentralMellin_even_pos 0).ne' hc.symm


def family : Registration arena (type_of% actual_reflected_gaussian_physical_synthesis) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_reflected_gaussian_physical_synthesis, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    actual_reflected_gaussian_physical_synthesis (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianPhysicalSynthesis.physical_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianPhysicalSynthesis.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => (synthesis w).2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianPhysicalSynthesis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianPhysicalSynthesis
